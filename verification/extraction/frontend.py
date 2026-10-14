"""Shared fail-closed Clang AST lowering. No kernel-name dispatch lives here.

Profiles select admitted language features, signatures and ABI layouts. This
translator and those descriptions are part of the trusted C-to-model bridge.
"""
import json
import re

class Unsupported(ValueError):
    pass

def require(condition, message):
    if not condition:
        raise Unsupported(message)

def ty(n):
    return n.get('type', {}).get('qualType', '')

def unqual(t):
    return re.sub(r'\b(const|restrict)\b\s*', '', t).strip()

def q(s):
    return json.dumps(s)

def node(op, *args):
    return '(.' + op + (' ' + ' '.join(args) if args else '') + ')'

def seq(stmts):
    result = '.skip'
    for s in reversed(stmts):
        result = node('seq', s, result)
    return result


def references_decl(tree, ident):
    """Detect a conflicting local use when lowering a narrowly allowed effect."""
    if tree.get('kind') == 'DeclRefExpr' and tree['referencedDecl']['id'] == ident:
        return True
    return any(references_decl(child, ident) for child in tree.get('inner', []))

class Extractor:
    def __init__(self, profile, trusted_calls):
        self.p = profile
        self.trusted_calls = trusted_calls
        self.names, self.tables, self.tuple_init = {}, {}, {}
        self.used, self.initialized = set(), set()

    def has(self, feature):
        return feature in self.p['features']

    def supported(self, t):
        return unqual(t) in set(self.p['scalars']) | set(self.p['vectors']) | set(self.p['pointers'])

    def snapshot(self):
        return self.initialized.copy(), {n: set(v) for n, v in self.tuple_init.items()}

    def restore(self, snapshot):
        self.initialized, fields = snapshot
        self.initialized = self.initialized.copy()
        self.tuple_init = {n: set(v) for n, v in fields.items()}

    def intersect(self, snapshot):
        initialized, fields = snapshot
        self.initialized &= initialized
        for n in self.tuple_init.keys() | fields.keys():
            self.tuple_init[n] = self.tuple_init.get(n, set()) & fields.get(n, set())

    def declare(self, n):
        require(n['kind'] in ('VarDecl', 'ParmVarDecl') and self.supported(ty(n)), f'unsupported declaration {n}')
        require(not n.get('storageClass') and not n.get('tls'), 'static/extern/thread local variables unsupported')
        name = n['name']
        suffix = 1
        fresh = name
        while fresh in self.used:
            suffix += 1
            fresh = name + '_' + str(suffix)
        self.used.add(fresh)
        self.names[n['id']] = fresh
        return fresh

    def ref(self, n):
        require(n['kind'] == 'DeclRefExpr', 'lvalue must be a local variable')
        ref = n['referencedDecl']
        require(ref['id'] in self.names, 'global or undeclared reference: ' + ref.get('name', '?'))
        require(self.supported(ty(n)), 'unsupported reference type: ' + ty(n))
        return self.names[ref['id']]

    def call(self, n):
        children = n.get('inner', [])
        require(n['kind'] == 'CallExpr' and children, 'expected direct call')
        fun = children[0]
        require(fun['kind'] == 'ImplicitCastExpr' and fun.get('castKind') == 'FunctionToPointerDecay', 'indirect/builtin call')
        require(len(fun.get('inner', [])) == 1, 'function decay arity')
        ref = fun['inner'][0]
        require(ref['kind'] == 'DeclRefExpr', 'indirect call')
        decl = ref['referencedDecl']
        name = decl['name']
        require(name in self.p['calls'], 'unsupported call: ' + name)
        require(decl['id'] in self.trusted_calls, 'call does not resolve to trusted interface: ' + name)
        entry = self.p['calls'][name]
        prim, signature = entry['primitive'], entry['signature']
        require(name != 'floor', 'floor only supported inside checked integer conversion')
        require(ty(ref) == signature and ty(decl) == signature, 'signature mismatch: ' + name + ' ' + ty(ref))
        if self.has('literal_table') and prim == 'load16' and len(children) == 2 and children[1]['kind'] == 'UnaryOperator' and children[1].get('opcode') == '&':
            address = children[1]
            require(len(address.get('inner', [])) == 1 and not address.get('isPostfix'), 'table address')
            sub = address['inner'][0]
            require(sub['kind'] == 'ArraySubscriptExpr' and len(sub.get('inner', [])) == 2, 'table subscript')
            decay, index = sub['inner']
            require(decay['kind'] == 'ImplicitCastExpr' and decay.get('castKind') == 'ArrayToPointerDecay'
                    and len(decay.get('inner', [])) == 1, 'table decay')
            ref = decay['inner'][0]
            require(ref['kind'] == 'DeclRefExpr' and ref['referencedDecl']['id'] in self.tables, 'unrecognized table')
            ident = ref['referencedDecl']['id']
            byte = self.p['byte']
            require(name == 'vld1q_' + ('u8' if self.p['word'] == 'uint32_t' else 's8') and ty(ref) == 'const ' + byte + '[32]'
                    and ty(decay) == 'const ' + byte + ' *' and ty(address) == ty(decay)
                    and ty(sub) == 'const ' + byte and unqual(ty(index)) in ('size_t', 'unsigned long', '__size_t'), 'table load types')
            return 'loadTable16', '[' + node('var', q(self.tables[ident])) + ', ' + self.expr(index) + ']'
        return prim, '[' + ', '.join(self.expr(a) for a in children[1:]) + ']'

    def expr(self, n):
        k, cs = n['kind'], n.get('inner', [])
        if k == 'IntegerLiteral':
            require(ty(n) != 'unsigned int' or self.p['unsigned_literals'], 'unsigned literal unsupported')
            require(ty(n) in ('int', 'unsigned int', 'unsigned long', '__size_t') and not cs, 'literal type')
            return node('lit', n['value'])
        if k == 'DeclRefExpr':
            name = self.ref(n)
            require(name in self.initialized, 'read before definite initialization: ' + name)
            require(name not in self.tuple_init or self.tuple_init[name] == {0, 1}, 'uninitialized tuple read')
            return node('var', q(name))
        if k == 'ParenExpr':
            require(len(cs) == 1, 'parenthesis arity')
            return self.expr(cs[0])
        if k == 'ArraySubscriptExpr':
            require(self.has('tuple_read'), 'tuple reads unsupported')
            require(len(cs) == 2 and cs[1]['kind'] == 'IntegerLiteral' and cs[1]['value'] in ('0', '1'), 'vector tuple index')
            base = cs[0]
            require(base['kind'] == 'ImplicitCastExpr' and base.get('castKind') == 'ArrayToPointerDecay' and len(base.get('inner', [])) == 1, 'tuple decay')
            field = base['inner'][0]
            require(field['kind'] == 'MemberExpr' and field['name'] == 'val' and not field.get('isArrow') and len(field.get('inner', [])) == 1, 'tuple member')
            require(unqual(ty(field['inner'][0])) == 'uint32x2x2_t' and unqual(ty(n)) == 'uint32x2_t', 'tuple type')
            base_name = self.ref(field['inner'][0])
            index = int(cs[1]['value'])
            require(base_name not in self.tuple_init or index in self.tuple_init[base_name], 'uninitialized tuple member read')
            return node('vectorMember', node('var', q(base_name)), str(index))
        if k in ('ImplicitCastExpr', 'CStyleCastExpr'):
            require(len(cs) == 1, 'cast arity')
            cast, dst, src = n['castKind'], unqual(ty(n)), unqual(ty(cs[0]))
            if cast == 'LValueToRValue':
                require(k == 'ImplicitCastExpr' and dst == src and self.supported(dst), 'lvalue cast')
                return self.expr(cs[0])
            if cast == 'FloatingToIntegral':
                require(self.has('floor_conversion'), 'floor_conversion unsupported')
                require(k == 'ImplicitCastExpr' and dst == 'int' and src == 'double', 'floor result conversion')
                call = cs[0]
                cc = call.get('inner', [])
                require(call['kind'] == 'CallExpr' and len(cc) == 2 and ty(call) == 'double', 'floor composition')
                fun, arg = cc
                fc = fun.get('inner', [])
                require(fun['kind'] == 'ImplicitCastExpr' and fun.get('castKind') == 'FunctionToPointerDecay'
                        and len(fc) == 1 and fc[0]['kind'] == 'DeclRefExpr', 'floor function')
                ref = fc[0]; decl = ref['referencedDecl']
                require(decl['name'] == 'floor' and decl['id'] in self.trusted_calls
                        and ty(ref) == 'double (double)' and ty(decl) == ty(ref), 'trusted floor signature')
                ac = arg.get('inner', [])
                require(arg['kind'] == 'ImplicitCastExpr' and arg.get('castKind') == 'IntegralToFloating'
                        and ty(arg) == 'double' and len(ac) == 1 and unqual(ty(ac[0])) in self.p['scalars']
                        and self.p['scalars'][unqual(ty(ac[0]))] == 'u64', 'floor requires unsigned 64-bit integer input')
                return node('call', '.floorU64I32', '[' + self.expr(ac[0]) + ']')
            if cast == 'PointerToIntegral':
                require(self.has('pointer_integer'), 'pointer_integer unsupported')
                require(src in self.p['pointers'] and dst == 'uintptr_t', 'pointer to integer type')
                return node('ptrToInt', self.expr(cs[0]))
            if cast == 'IntegralToPointer':
                require(self.has('pointer_integer'), 'pointer_integer unsupported')
                require(src in ('uintptr_t', 'unsigned long') and dst in self.p['pointers'], 'integer to pointer type')
                return node('intToPtr', self.expr(cs[0]))
            if cast == 'IntegralCast':
                require(dst in self.p['scalars'] and src in self.p['scalars'], 'integer conversion type')
                return node('cast', '.' + self.p['scalars'][dst], self.expr(cs[0]))
            if cast in ('BitCast', 'NoOp'):
                require(dst in self.p['pointers'] and src in self.p['pointers'], 'only pointer-preserving casts supported')
                return self.expr(cs[0])
            if cast == 'NullToPointer':
                require(dst in self.p['pointers'] and cs[0]['kind'] == 'IntegerLiteral' and cs[0]['value'] == '0', 'null cast')
                return '.null'
            raise Unsupported('unsupported cast: ' + cast)
        if k == 'UnaryExprOrTypeTraitExpr':
            t = n.get('argType', {}).get('qualType')
            require(n['name'] == 'sizeof' and t in self.p['sizeof'] and not cs, 'sizeof type unsupported')
            return node('lit', str(self.p['sizeof'][t]))
        if k == 'UnaryOperator' and n.get('opcode') == '&':
            require(self.has('address_element'), 'address of element unsupported')
            require(len(cs) == 1 and not n.get('isPostfix'), 'address arity')
            sub = cs[0]; sc = sub.get('inner', [])
            require(sub['kind'] == 'ArraySubscriptExpr' and len(sc) == 2, 'only address of array element supported')
            base, index = sc
            t = unqual(ty(base))
            require(t in ('int8_t *', 'uint8_t *', 'int32_t *', 'uint32_t *') and unqual(ty(n)) == t
                    and unqual(ty(sub)) == t[:-2] and unqual(ty(index)) in self.p['scalars'], 'array address types')
            return node('offset', '4' if '32' in t else '1', self.expr(base), self.expr(index))
        if k == 'UnaryOperator' and n.get('opcode') == '*':
            require(self.has('scalar_read'), 'scalar dereference unsupported')
            require(len(cs) == 1 and unqual(ty(cs[0])) == 'uint32_t *' and unqual(ty(n)) == 'uint32_t', 'scalar read type')
            return node('cast', '.u32', node('param', self.expr(cs[0]), '0'))
        if k == 'UnaryOperator':
            if n['opcode'] == '-':
                require(self.has('signed_negation'), 'signed negation unsupported')
                require(len(cs) == 1 and not n.get('isPostfix') and unqual(ty(n)) in ('int32_t', 'int') and unqual(ty(cs[0])) in ('int32_t', 'int'), 'only signed i32 negation supported')
                return node('negSigned32', self.expr(cs[0]))
            require(n['opcode'] == '!' and len(cs) == 1 and not n.get('isPostfix'), 'unary operator')
            return node('not', self.expr(cs[0]))
        if k == 'ConditionalOperator':
            require(self.has('conditional'), 'conditional expression unsupported')
            require(len(cs) == 3 and unqual(ty(n)) in self.p['scalars'] and
                    unqual(ty(cs[1])) == unqual(ty(n)) and unqual(ty(cs[2])) == unqual(ty(n)),
                    'conditional result type')
            return node('conditional', *(self.expr(c) for c in cs))
        if k == 'BinaryOperator':
            op = n['opcode']
            if op == '&&':
                require(self.has('logical_and'), 'logical_and unsupported')
                require(len(cs) == 2 and all(unqual(ty(c)) in self.p['scalars'] for c in cs), 'logical-and types')
                return node('conditional', self.expr(cs[0]), node('conditional', self.expr(cs[1]), node('lit', '1'), node('lit', '0')), node('lit', '0'))
            if op == '||':
                require(self.has('logical_or'), 'logical_or unsupported')
                require(len(cs) == 2 and all(unqual(ty(c)) in self.p['scalars'] for c in cs), 'logical-or types')
                return node('or', self.expr(cs[0]), self.expr(cs[1]))
            require(op in self.p['binary'] and len(cs) == 2, 'unsupported binary operator: ' + op)
            a, b = cs
            ta, tb, tr = unqual(ty(a)), unqual(ty(b)), unqual(ty(n))
            if op == '+' and ta in self.p['pointers']:
                require(self.has('pointer_add'), 'pointer addition unsupported')
                require(ta in ('int8_t *', 'uint8_t *', 'int32_t *', 'uint32_t *')
                        and tb in self.p['scalars'] and tr == ta, 'pointer addition types')
                return node('offset', '4' if '32' in ta else '1', self.expr(a), self.expr(b))
            require((ta in self.p['scalars'] and tb in self.p['scalars'] and self.p['scalars'][ta] == self.p['scalars'][tb]) or (op in ('==', '!=') and ta in self.p['pointers'] and tb == ta), f'binary operand types: {op} {ta} {tb}')
            # Unsigned operations wrap at their AST result width. The only
            # supported signed arithmetic is i32 subtraction, checked for overflow.
            arithmetic = op in ('+', '-', '*', '/', '%', '&')
            signed_sub = self.has('signed_subtraction') and op == '-' and ta in self.p['scalars'] and self.p['scalars'][ta] == 'i32'
            if arithmetic:
                require(signed_sub or self.p['scalars'][ta] in self.p['arithmetic_types'], 'unsupported arithmetic type')
            result = node('bin', '.' + self.p['binary'][op], self.expr(a), self.expr(b))
            if signed_sub:
                require(self.p['scalars'][tr] == 'i32', 'signed subtraction result')
                result = node('checkedSigned32', result)
            elif arithmetic:
                require(tr in self.p['scalars'], 'binary result type')
                result = node('cast', '.' + self.p['scalars'][tr], result)
            return result
        if k == 'MemberExpr':
            require(n['name'] in self.p['fields'] and not n.get('isArrow') and len(cs) == 1, 'parameter field')
            field_type, primitive, offset = self.p['fields'][n['name']]
            require(unqual(ty(n)) == field_type, 'parameter field type')
            mid = cs[0]
            require(mid['kind'] == 'MemberExpr' and mid['name'] == 'scalar' and mid.get('isArrow') and len(mid.get('inner', [])) == 1, 'parameter aggregate')
            base = mid['inner'][0]
            require(unqual(ty(base)) == self.p['record'], 'parameter base type')
            return node(primitive, self.expr(base), str(offset))
        if k == 'CallExpr':
            require(ty(n) != 'void', 'effect in expression')
            prim, args = self.call(n)
            return node('call', '.' + prim, args)
        raise Unsupported('unsupported expression node: ' + k)

    def stmt(self, n):
        k, cs = n['kind'], n.get('inner', [])
        require(k in self.p['statements'], 'statement not admitted by profile: ' + k)
        if k == 'CompoundStmt':
            return seq([self.stmt(c) for c in cs])
        if k == 'DeclStmt':
            require(len(cs) == 1, 'multiple declaration')
            v = cs[0]
            if v.get('storageClass') == 'static':
                require(self.has('literal_table'), 'static data unsupported')
                byte = self.p['byte']
                vc = v.get('inner', [])
                require(v['kind'] == 'VarDecl' and v.get('name') == 'onemask_table' and not self.tables
                        and ty(v) == 'const ' + byte + '[32]' and not v.get('tls') and v.get('init') == 'c'
                        and len(vc) == 2 and vc[0]['kind'] == 'InitListExpr' and ty(vc[0]) == ty(v)
                        and vc[1]['kind'] == 'AlignedAttr', 'only immutable aligned32byte table supported')
                align = vc[1].get('inner', [])
                require(len(align) == 1 and align[0]['kind'] == 'ConstantExpr' and align[0].get('value') == '16'
                        and len(align[0].get('inner', [])) == 1 and align[0]['inner'][0]['kind'] == 'IntegerLiteral'
                        and align[0]['inner'][0].get('value') == '16', 'table alignment')
                entries = vc[0].get('inner', [])
                require(len(entries) == 32, 'table entry count')
                values = []
                for entry in entries:
                    ec = entry.get('inner', [])
                    require(entry['kind'] == 'ImplicitCastExpr' and entry.get('castKind') == 'IntegralCast'
                            and ty(entry) == byte and len(ec) == 1 and ec[0]['kind'] == 'IntegerLiteral'
                            and ty(ec[0]) == 'int' and not ec[0].get('inner'), 'literal byte table entries')
                    values.append(int(ec[0]['value']))
                require(values == [1] * 16 + [0] * 16, 'unsupported mask table contents')
                require(v['name'] not in self.used, 'table name shadowing')
                self.used.add(v['name'])
                self.tables[v['id']] = v['name']
                return node('assign', q(v['name']), node('byteArray', '[' + ', '.join(map(str, values)) + ']'))
            if not v.get('inner') and not v.get('init'):
                if self.has('tuple_write') and unqual(ty(v)) == 'uint32x2x2_t':
                    name = self.declare(v)
                    self.tuple_init[name] = set()
                    self.initialized.add(name)
                    return node('assign', q(name), node('call', '.emptyTupleU32x2', '[]'))
                require(self.has('uninitialized_vector') and unqual(ty(v)) in self.p['vectors'], 'uninitialized declaration unsupported')
                self.declare(v)
                return '.skip'
            require(len(v.get('inner', [])) == 1 and v.get('init') == 'c', 'missing initializer or declaration attribute')
            name = self.declare(v)
            rhs = self.expr(v['inner'][0])
            self.initialized.add(name)
            return node('assign', q(name), rhs)
        if k == 'BinaryOperator':
            require(n['opcode'] == '=' and len(cs) == 2, 'expression statement')
            lhs, rhs = cs
            if lhs['kind'] == 'ArraySubscriptExpr':
                require(self.has('tuple_write'), 'tuple assignment unsupported')
                ac = lhs.get('inner', [])
                require(len(ac) == 2 and ac[1]['kind'] == 'IntegerLiteral' and ac[1]['value'] in ('0', '1'), 'tuple assignment index')
                decay = ac[0]
                require(decay['kind'] == 'ImplicitCastExpr' and decay.get('castKind') == 'ArrayToPointerDecay' and len(decay.get('inner', [])) == 1, 'tuple assignment decay')
                field = decay['inner'][0]
                require(field['kind'] == 'MemberExpr' and field.get('name') == 'val' and not field.get('isArrow') and len(field.get('inner', [])) == 1, 'tuple assignment field')
                base = field['inner'][0]
                require(unqual(ty(base)) == 'uint32x2x2_t' and unqual(ty(lhs)) == unqual(ty(rhs)) == 'uint32x2_t', 'tuple assignment types')
                name, index = self.ref(base), int(ac[1]['value'])
                value = self.expr(rhs)
                self.tuple_init.setdefault(name, set()).add(index)
                return node('assign', q(name), node('call', '.setTupleU32x2', '[' + node('var', q(name)) + ', ' + node('lit', str(index)) + ', ' + value + ']'))
            if lhs['kind'] == 'UnaryOperator' and lhs.get('opcode') == '*':
                require(self.has('scalar_store'), 'scalar store unsupported')
                require(len(lhs.get('inner', [])) == 1 and unqual(ty(lhs)) == unqual(ty(rhs)) == 'uint32_t' and unqual(ty(lhs['inner'][0])) == 'uint32_t *', 'scalar store type')
                target = self.expr(lhs['inner'][0])
                # The only accepted side effect in a value expression is this
                # scalar load's pointer postincrement. Its old pointer feeds the
                # load; updating this local after the store is observationally
                # equivalent because the destination expression is pure.
                if rhs['kind'] == 'ImplicitCastExpr' and rhs.get('castKind') == 'LValueToRValue':
                    read = rhs['inner'][0]
                    if read['kind'] == 'UnaryOperator' and read.get('opcode') == '*':
                        pointer = read['inner'][0]
                        if pointer['kind'] == 'UnaryOperator' and pointer.get('opcode') == '++' and pointer.get('isPostfix'):
                            require(self.has('scalar_postincrement'), 'load-postincrement unsupported')
                            require(len(pointer.get('inner', [])) == 1 and unqual(ty(pointer)) == 'uint32_t *', 'pointer postincrement type')
                            name = self.ref(pointer['inner'][0])
                            require(name in self.initialized, 'postincrement before initialization')
                            ident = pointer['inner'][0]['referencedDecl']['id']
                            require(not references_decl(lhs, ident), 'unsequenced destination use of postincremented pointer')
                            value = node('cast', '.u32', node('param', node('var', q(name)), '0'))
                            effect = node('effect', '.storeU32', '[' + target + ', ' + value + ']')
                            step = node('assign', q(name), node('offset', '4', node('var', q(name)), node('lit', '1')))
                            return node('seq', effect, step)
                return node('effect', '.storeU32', '[' + target + ', ' + self.expr(rhs) + ']')
            value = self.expr(rhs)
            name = self.ref(lhs)
            self.initialized.add(name)
            if name in self.tuple_init:
                self.tuple_init[name] = {0, 1}
            return node('assign', q(name), value)
        if k == 'CompoundAssignOperator':
            require(len(cs) == 2 and n['opcode'] in ('+=', '-='), 'compound assignment')
            a, b = cs
            if a['kind'] == 'UnaryOperator' and a.get('opcode') == '*':
                require(self.has('scalar_accumulate'), 'scalar accumulation unsupported')
                word = self.p['word']
                ac = a.get('inner', [])
                require(n['opcode'] == '+=' and len(ac) == 1 and not a.get('isPostfix')
                        and unqual(ty(a)) == word and unqual(ty(b)) == word and unqual(ty(n)) == word
                        and unqual(ty(ac[0])) == word + ' *'
                        and n.get('computeLHSType', {}).get('qualType') == word
                        and n.get('computeResultType', {}).get('qualType') == word, 'scalar output addition type')
                pointer = self.expr(ac[0])
                loaded = node('param', pointer, '0')
                if self.p['word'] == 'uint32_t': loaded = node('cast', '.u32', loaded)
                result = node('bin', '.add', loaded, self.expr(b))
                result = node('cast', '.u32', result) if self.p['word'] == 'uint32_t' else node('checkedSigned32', result)
                return node('effect', '.storeU32' if self.p['word'] == 'uint32_t' else '.storeI32', '[' + pointer + ', ' + result + ']')
            name, t = self.ref(a), unqual(ty(a))
            require(name in self.initialized, 'compound read before initialization')
            if t in self.p['pointers']:
                require(t in self.p['pointer_steps'] and n['opcode'] == '+=' and unqual(ty(b)) in self.p['scalars'], 'pointer increment types')
                rhs = node('offset', str(self.p['pointer_steps'][t]), node('var', q(name)), self.expr(b))
            elif t == 'int':
                require(self.has('signed_compound'), 'signed compound unsupported')
                require(unqual(ty(b)) == 'int' and n.get('computeLHSType', {}).get('qualType') == 'int' and n.get('computeResultType', {}).get('qualType') == 'int', 'signed compound types')
                rhs = node('checkedSigned32', node('bin', '.add' if n['opcode'] == '+=' else '.sub', node('var', q(name)), self.expr(b)))
            else:
                require(t == 'size_t' and unqual(ty(b)) in self.p['compound_rhs'], 'compound arithmetic type')
                rhs = node('cast', '.u64', node('bin', '.add' if n['opcode'] == '+=' else '.sub', node('var', q(name)), self.expr(b)))
            return node('assign', q(name), rhs)
        if k == 'UnaryOperator' and unqual(ty(n)) == 'int':
            require(self.has('signed_decrement'), 'signed decrement unsupported')
            require(n.get('opcode') == '--' and not n.get('isPostfix') and len(cs) == 1
                    and unqual(ty(n)) == 'int' and unqual(ty(cs[0])) == 'int', 'only prefix signed decrement statement supported')
            name = self.ref(cs[0])
            require(name in self.initialized, 'decrement before initialization')
            return node('assign', q(name), node('checkedSigned32', node('bin', '.sub', node('var', q(name)), node('lit', '1'))))
        if k == 'UnaryOperator':
            require(self.has('increment'), 'increment unsupported')
            require(len(cs) == 1 and n.get('opcode') in ('++', '--'), 'increment statement')
            name, t = self.ref(cs[0]), unqual(ty(cs[0]))
            require(name in self.initialized, 'increment before initialization')
            require(t in ('size_t', 'uint32_t *'), 'increment type')
            if t == 'size_t':
                value = node('cast', '.u64', node('bin', '.add' if n['opcode'] == '++' else '.sub', node('var', q(name)), node('lit', '1')))
            else:
                value = node('offset', '4', node('var', q(name)), node('lit', '1' if n['opcode'] == '++' else '(-1)'))
            return node('assign', q(name), value)
        if k == 'CallExpr':
            require(ty(n) == 'void', 'discarded pure expression')
            prim, args = self.call(n)
            return node('effect', '.' + prim, args)
        if k == 'ForStmt':
            require(len(cs) == 5 and cs[1] == {}, 'for declaration condition unsupported')
            require(not cs[0] or self.has('for_initializer'), 'for initializer unsupported')
            cond, step, body = cs[2:]
            init = self.stmt(cs[0]) if cs[0] else '.skip'
            before = self.snapshot()
            loop = node('loop', self.expr(cond), node('seq', self.stmt(body), self.stmt(step) if step else '.skip'))
            self.restore(before)
            return node('seq', init, loop) if cs[0] else loop
        if k == 'WhileStmt':
            require(len(cs) == 2, 'while arity')
            before = self.snapshot()
            result = node('loop', self.expr(cs[0]), self.stmt(cs[1]))
            self.restore(before)
            return result
        if k == 'IfStmt':
            require(len(cs) == (3 if n.get('hasElse') else 2), 'if arity')
            require(not n.get('hasElse') or self.has('if_else'), 'else unsupported')
            cond = self.expr(cs[0]); before = self.snapshot()
            yes = self.stmt(cs[1]); yes_initialized = self.snapshot()
            self.restore(before)
            no = self.stmt(cs[2]) if n.get('hasElse') else '.skip'
            self.intersect(yes_initialized)
            return node('branch', cond, yes, no)
        if k == 'DoStmt':
            require(len(cs) == 2, 'do while arity')
            body, cond = cs
            b = self.stmt(body)
            test = cond
            if test['kind'] == 'BinaryOperator' and test.get('opcode') == '!=':
                test = test['inner'][0]
            if self.has('do_decrement') and test['kind'] == 'UnaryOperator' and test.get('opcode') == '--' and not test.get('isPostfix'):
                require(unqual(ty(test)) == 'size_t', 'do decrement type')
                name = self.ref(test['inner'][0])
                b = node('seq', b, self.stmt(test))
                if cond is not test:
                    require(len(cond['inner']) == 2 and cond['inner'][1]['kind'] == 'ImplicitCastExpr' and self.expr(cond['inner'][1]) == node('cast', '.u64', node('lit', '0')), 'do decrement must compare with zero')
                condition = node('bin', '.ne', node('var', q(name)), node('lit', '0'))
            else:
                condition = self.expr(cond)
            return node('seq', b, node('loop', condition, b))
        raise Unsupported('unsupported statement node: ' + k)

    def function(self, n, name):
        parameters = self.p['parameters']
        expected = [t for _, t in parameters]
        require(n['kind'] == 'FunctionDecl' and n['name'] == name, 'function identity')
        cs = n.get('inner', [])
        require(len(cs) == len(expected) + 1 and [ty(c) for c in cs[:-1]] == expected, 'function parameters/attributes')
        require(ty(n) == 'void (' + ', '.join(expected) + ')', 'function signature')
        for p, (pname, _) in zip(cs[:-1], parameters):
            require(p['kind'] == 'ParmVarDecl' and p['name'] == pname, 'parameter name')
            self.initialized.add(self.declare(p))
        require(cs[-1]['kind'] == 'CompoundStmt', 'function body')
        return self.stmt(cs[-1])

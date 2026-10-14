# Shared C/intrinsic extraction

Run `python3 verification/extraction/extract.py --family all --check` from the
repository root. Use `--family qs8` (or another profile name) to select a family,
and `--write` to regenerate its Lean programs and provenance. Existing
`extract_qs8.py --check` style commands remain compatibility delegates.

## Review the trusted bridge

- `extract.py`: compiler invocation, fixed preprocessing policy, complete translation
  unit validation, output generation and dependency provenance.
- `frontend.py`: the only AST translator, with declaration-ID binding, explicit
  casts, checked signed arithmetic, short-circuit control flow and memory operations.
- `profiles.json`: admitted features/types/calls, exact entry parameters, source and
  target directive policies, and kernel/output names. Shared family data is separate
  from signed/unsigned variant overrides. Profiles contain no executable lowering.
- `intrinsics.json`: shared name/signature/primitive registry. A name may have several
  explicitly selected model specializations; matching spelling alone is insufficient.
- `abi.json`: LP64 scalar representations, element sizes, parameter field widths and
  offsets. Declaration-only `*_context.h` and `*_intrinsics.h` headers are also trusted.

Clang and the Python translation are not verified. Lean proves the generated
programs under the stated semantics, and cannot detect a wrong C-to-model mapping.
Real-header compilation, dependency hashes and mutation tests support review but
are not a semantic-preservation theorem or a proof of compiled binaries.

## Admitted language and extension

The translator has no kernel-name branch. A profile chooses capabilities in the
shared language: integer arithmetic, pointer operations, branches/loops, vector
calls, record loads, and narrow special cases. New kernels should add manifests
and operation/interface descriptions; new syntax requires one reviewed lowering
rule and negative tests. New kernels still require their own caller contracts and
whole-function proofs before coverage can be registered.

Unsupported syntax fails closed. The frontend checks exact function parameters,
trusted call declaration IDs and signatures, and rejects extra top-level declarations,
unknown directives, volatile/static locals, indirect calls and unsupported effects.
The only static local abstraction is the explicitly checked immutable reduction mask
table. Its bytes, size, alignment and declaration identity must match. The floor
bridge accepts only the checked unsigned-integer conversion composition; it is not
an implementation of arbitrary floating-point C.

Tuple fields and ordinary locals have definite-initialization checks. Branches
intersect initialization facts; potentially zero-iteration loops cannot initialize
an outer variable; a do-loop executes once before testing. Packing's load-postincrement
and decrement-loop conditions have explicit lowering rules. General expression
side effects remain unsupported, and a destination cannot use the local pointer
modified by the admitted postincrement.

## Refactor evidence

All 22 generated Lean program declarations were compared with the pre-refactor
snapshot and are unchanged (only their generated-by comment changed). The 59 existing
mutation tests remain in place, alongside shared-frontend tests for capability and
state isolation. Every provenance record includes the shared driver, frontend,
profiles, intrinsic registry, ABI descriptions, compatibility delegate and interface
headers, plus the real compiler/header dependency closure.

Run the tests with:

```sh
python3 -m unittest discover -s verification/extraction -p 'test_*.py'
```

The shared configuration is loaded fresh for each extraction. Profile selection
never mutates module-global translation tables.

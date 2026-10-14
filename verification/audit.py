#!/usr/bin/env python3
"""Check kernel inventory/provenance and report actual formal coverage.

A source hash is provenance, not a proof that a Lean model faithfully lifts C.
This tool never promotes a file to 'proved' based on names or generic lemmas.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / 'verification/coverage.json'

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest() if path.exists() else None

def inventory():
    rows = []
    for source in sorted((ROOT / 'kernels/source').glob('*.c')):
        target = ROOT / 'kernels/target' / source.name
        available = target.exists() and bool(target.read_text().strip())
        rows.append(dict(kernel=source.stem, source_sha256=digest(source),
                         target_sha256=digest(target),
                         status='pending' if available else 'excluded_missing_target',
                         theorem=None, machine_lifting=None))
    return rows

S8_THEOREM = 'Salty.Kernels.S8Clamp.Execution.behavior_equivalent'
S8_BRIDGE = 'trusted-clang-ast-intrinsics-v1'

def check_s8_proof():
    """Regenerate both models, then check the precise shared theorem type.

    The bridge is explicitly trusted. The Lean check prevents an existing but
    weakened/unrelated declaration from being accepted by its name alone.
    """
    subprocess.run([sys.executable, str(ROOT / 'verification/extraction/extract.py'), '--family', 's8', '--check'], check=True)
    lean = ROOT / 'verification/lean'
    subprocess.run(['lake', 'build'], cwd=lean, check=True)
    statement = """import Salty
open Salty Salty.CByte Salty.Kernels.S8Clamp.Execution
example (cfg : Config) (c : Call) :
  Salty.Equivalent (CByte.machine cfg) (CByte.machine cfg)
    (fun s => ⟨[Salty.Generated.S8Clamp.neon], s⟩)
    (fun s => ⟨[Salty.Generated.S8Clamp.rvv], s⟩) (fun s => Entry s c) :=
  Salty.Kernels.S8Clamp.Execution.behavior_equivalent cfg c
example : Entry witnessState witnessCall := entry_nonempty
#print axioms Salty.Kernels.S8Clamp.Execution.behavior_equivalent
#print axioms Salty.Kernels.S8Clamp.Execution.entry_nonempty
"""
    with tempfile.TemporaryDirectory(prefix='salty-proof-audit-') as folder:
        check = Path(folder) / 'Check.lean'
        check.write_text(statement)
        result = subprocess.run(['lake', 'env', 'lean', str(check)], cwd=lean,
                                check=True, capture_output=True, text=True)
    dependencies = re.findall(r'depends on axioms: \[([^\]]*)\]', result.stdout)
    if len(dependencies) != 2:
        raise ValueError('missing axiom audit for registered theorem')
    unexpected = {name.strip() for group in dependencies for name in group.split(',')} - {'propext', 'Quot.sound', 'Classical.choice'}
    if unexpected:
        raise ValueError(f'unexpected theorem axioms: {unexpected}')

X32_THEOREM = 'Salty.Kernels.X32Transpose.behavior_equivalent'
X32_BRIDGE = 'trusted-clang-ast-intrinsics-v1'

def check_x32_proof():
    """Check both independently regenerated programs, exact behavior theorem,
    and nonempty/large-empty caller witnesses for the reviewed transpose model."""
    subprocess.run([sys.executable, str(ROOT / 'verification/extraction/extract.py'), '--family', 'x32', '--check'], check=True)
    lean = ROOT / 'verification/lean'
    subprocess.run(['lake', 'build'], cwd=lean, check=True)
    statement = """import Salty
open Salty Salty.CByte Salty.Kernels.X32Transpose
example (cfg : Config) (p : MatrixCopy) :
  Salty.Equivalent (CByte.machine cfg) (CByte.machine cfg)
    (fun s => ⟨[Salty.Generated.X32Transpose.neon], s⟩)
    (fun s => ⟨[Salty.Generated.X32Transpose.rvv], s⟩) (fun s => Entry s p) :=
  Salty.Kernels.X32Transpose.behavior_equivalent cfg p
example : Entry witnessState witnessMatrix := entry_nonempty
example : Entry (stateFor emptyMatrix) emptyMatrix := entry_empty_large
#print axioms Salty.Kernels.X32Transpose.behavior_equivalent
#print axioms Salty.Kernels.X32Transpose.entry_nonempty
#print axioms Salty.Kernels.X32Transpose.entry_empty_large
"""
    with tempfile.TemporaryDirectory(prefix='salty-proof-audit-') as folder:
        check = Path(folder) / 'Check.lean'
        check.write_text(statement)
        result = subprocess.run(['lake', 'env', 'lean', str(check)], cwd=lean,
                                check=True, capture_output=True, text=True)
    dependencies = re.findall(r'depends on axioms: \[([^\]]*)\]', result.stdout)
    if len(dependencies) != 3:
        raise ValueError('missing axiom audit for registered transpose theorem/witnesses')
    unexpected = {name.strip() for group in dependencies for name in group.split(',')} - {'propext', 'Quot.sound', 'Classical.choice'}
    if unexpected:
        raise ValueError(f'unexpected theorem axioms: {unexpected}')

QS8_THEOREM = 'Salty.Kernels.QS8Convert.behavior_equivalent'
QS8_BRIDGE = 'trusted-clang-ast-intrinsics-v1'

def check_qs8_proof():
    """Check full regenerated conversion programs, exact shared behavior type,
    nonempty caller witness and the repaired saturation corner."""
    subprocess.run([sys.executable, str(ROOT / 'verification/extraction/extract.py'), '--family', 'qs8', '--check'], check=True)
    lean = ROOT / 'verification/lean'
    subprocess.run(['lake', 'build'], cwd=lean, check=True)
    statement = """import Salty
open Salty Salty.CByte Salty.Kernels.QS8Convert
example (cfg : Config) (c : Call) :
  Salty.Equivalent (CByte.machine cfg) (CByte.machine cfg)
    (fun s => ⟨[Salty.Generated.QS8Convert.neon], s⟩)
    (fun s => ⟨[Salty.Generated.QS8Convert.rvv], s⟩) (fun s => Entry s c) :=
  Salty.Kernels.QS8Convert.behavior_equivalent cfg c
example : Entry witnessState witnessCall := entry_nonempty
example : QuantizedISA.neonLane witnessCall.values 0 = 127 := witness_saturation
#print axioms Salty.Kernels.QS8Convert.behavior_equivalent
#print axioms Salty.Kernels.QS8Convert.entry_nonempty
#print axioms Salty.Kernels.QS8Convert.witness_saturation
"""
    with tempfile.TemporaryDirectory(prefix='salty-proof-audit-') as folder:
        check = Path(folder) / 'Check.lean'
        check.write_text(statement)
        result = subprocess.run(['lake', 'env', 'lean', str(check)], cwd=lean,
                                check=True, capture_output=True, text=True)
    dependencies = re.findall(r'depends on axioms: \[([^\]]*)\]', result.stdout)
    if len(dependencies) != 3:
        raise ValueError('missing axiom audit for registered conversion theorem/witness')
    unexpected = {name.strip() for group in dependencies for name in group.split(',')} - {'propext', 'Quot.sound', 'Classical.choice'}
    if unexpected:
        raise ValueError(f'unexpected theorem axioms: {unexpected}')
LRELU_THEOREM = 'Salty.Kernels.QS8Leaky.behavior_equivalent'
LRELU_BRIDGE = 'trusted-clang-ast-intrinsics-v1'

def check_lrelu_proof():
    """Check full regenerated leaky-ReLU programs, exact shared behavior type,
    nonempty caller witness and both multiplier choices."""
    subprocess.run([sys.executable, str(ROOT / 'verification/extraction/extract.py'), '--family', 'lrelu', '--check'], check=True)
    lean = ROOT / 'verification/lean'
    subprocess.run(['lake', 'build'], cwd=lean, check=True)
    statement = """import Salty
open Salty Salty.CByte Salty.Kernels.QS8Leaky
example (cfg : Config) (c : Call) :
  Salty.Equivalent (CByte.machine cfg) (CByte.machine cfg)
    (fun s => ⟨[Salty.Generated.QS8Leaky.neon], s⟩)
    (fun s => ⟨[Salty.Generated.QS8Leaky.rvv], s⟩) (fun s => Entry s c) :=
  Salty.Kernels.QS8Leaky.behavior_equivalent cfg c
example : Entry witnessState witnessCall := entry_nonempty
example : neonLane witnessCall.values 1 = 127 := witness_positive
example : neonLane witnessCall.values 255 = 192 := witness_negative
#print axioms Salty.Kernels.QS8Leaky.behavior_equivalent
#print axioms Salty.Kernels.QS8Leaky.entry_nonempty
#print axioms Salty.Kernels.QS8Leaky.witness_positive
#print axioms Salty.Kernels.QS8Leaky.witness_negative
"""
    with tempfile.TemporaryDirectory(prefix='salty-proof-audit-') as folder:
        check = Path(folder) / 'Check.lean'
        check.write_text(statement)
        result = subprocess.run(['lake', 'env', 'lean', str(check)], cwd=lean,
                                check=True, capture_output=True, text=True)
    dependencies = re.findall(r'depends on axioms: \[([^\]]*)\]', result.stdout)
    if len(dependencies) != 4:
        raise ValueError('missing axiom audit for registered leaky-ReLU theorem/witnesses')
    unexpected = {name.strip() for group in dependencies for name in group.split(',')} - {'propext', 'Quot.sound', 'Classical.choice'}
    if unexpected:
        raise ValueError(f'unexpected theorem axioms: {unexpected}')

ADD_THEOREM = 'Salty.Kernels.QS8Add.behavior_equivalent'
ADD_BRIDGE = 'trusted-clang-ast-intrinsics-v1'

def check_add_proof():
    """Check full regenerated quantized-add programs, exact shared behavior type,
    nonempty caller witness and repaired zero/left shift branches."""
    subprocess.run([sys.executable, str(ROOT / 'verification/extraction/extract.py'), '--family', 'add', '--check'], check=True)
    lean = ROOT / 'verification/lean'
    subprocess.run(['lake', 'build'], cwd=lean, check=True)
    statement = """import Salty
open Salty Salty.CByte Salty.Kernels.QS8Add
example (cfg : Config) (c : Call) :
  Salty.Equivalent (CByte.machine cfg) (CByte.machine cfg)
    (fun s => ⟨[Salty.Generated.QS8Add.neon], s⟩)
    (fun s => ⟨[Salty.Generated.QS8Add.rvv], s⟩) (fun s => Entry s c) :=
  Salty.Kernels.QS8Add.behavior_equivalent cfg c
example : Entry witnessState witnessCall := entry_nonempty
example : QuantizedAddISA.neonLane witnessCall.values 1 0 = 0 := witness_source_zero
example : ShiftISA.rvvRight (1#32) 32 = 1 := witness_old_shift_one
example : QuantizedAddISA.neonLane { witnessCall.values with shift := 255 } 1 0 = 2 := witness_left_shift
example : (resultMemory witnessState witnessCall).data 48#64 = 0 := witness_result
#print axioms Salty.Kernels.QS8Add.behavior_equivalent
#print axioms Salty.Kernels.QS8Add.entry_nonempty
#print axioms Salty.Kernels.QS8Add.witness_source_zero
#print axioms Salty.Kernels.QS8Add.witness_old_shift_one
#print axioms Salty.Kernels.QS8Add.witness_left_shift
#print axioms Salty.Kernels.QS8Add.witness_result
"""
    with tempfile.TemporaryDirectory(prefix='salty-proof-audit-') as folder:
        check = Path(folder) / 'Check.lean'
        check.write_text(statement)
        result = subprocess.run(['lake', 'env', 'lean', str(check)], cwd=lean,
                                check=True, capture_output=True, text=True)
    dependencies = re.findall(r'depends on axioms: \[([^\]]*)\]', result.stdout)
    if len(dependencies) != 6:
        raise ValueError('missing axiom audit for registered quantized-add theorem/witnesses')
    unexpected = {name.strip() for group in dependencies for name in group.split(',')} - {'propext', 'Quot.sound', 'Classical.choice'}
    if unexpected:
        raise ValueError(f'unexpected theorem axioms: {unexpected}')

UADD_THEOREM = 'Salty.Kernels.QU8Add.behavior_equivalent'
UADD_BRIDGE = 'trusted-clang-ast-intrinsics-v1'

def check_uadd_proof():
    """Check full regenerated unsigned quantized-add programs, exact shared behavior type,
    nonempty caller witness and repaired zero/left shift branches."""
    subprocess.run([sys.executable, str(ROOT / 'verification/extraction/extract.py'), '--family', 'uadd', '--check'], check=True)
    lean = ROOT / 'verification/lean'
    subprocess.run(['lake', 'build'], cwd=lean, check=True)
    statement = """import Salty
open Salty Salty.CByte Salty.Kernels.QU8Add
example (cfg : Config) (c : Call) :
  Salty.Equivalent (CByte.machine cfg) (CByte.machine cfg)
    (fun s => ⟨[Salty.Generated.QU8Add.neon], s⟩)
    (fun s => ⟨[Salty.Generated.QU8Add.rvv], s⟩) (fun s => Entry s c) :=
  Salty.Kernels.QU8Add.behavior_equivalent cfg c
example : Entry witnessState witnessCall := entry_nonempty
example : QuantizedUAddISA.neonLane witnessCall.values 1 0 = 0 := witness_source_zero
example : ShiftISA.rvvRight (1#32) 32 = 1 := witness_old_shift_one
example : QuantizedUAddISA.neonLane { witnessCall.values with shift := 255 } 1 0 = 2 := witness_left_shift
example : (resultMemory witnessState witnessCall).data 48#64 = 0 := witness_result
#print axioms Salty.Kernels.QU8Add.behavior_equivalent
#print axioms Salty.Kernels.QU8Add.entry_nonempty
#print axioms Salty.Kernels.QU8Add.witness_source_zero
#print axioms Salty.Kernels.QU8Add.witness_old_shift_one
#print axioms Salty.Kernels.QU8Add.witness_left_shift
#print axioms Salty.Kernels.QU8Add.witness_result
"""
    with tempfile.TemporaryDirectory(prefix='salty-proof-audit-') as folder:
        check = Path(folder) / 'Check.lean'
        check.write_text(statement)
        result = subprocess.run(['lake', 'env', 'lean', str(check)], cwd=lean,
                                check=True, capture_output=True, text=True)
    dependencies = re.findall(r'depends on axioms: \[([^\]]*)\]', result.stdout)
    if len(dependencies) != 6:
        raise ValueError('missing axiom audit for registered unsigned quantized-add theorem/witnesses')
    unexpected = {name.strip() for group in dependencies for name in group.split(',')} - {'propext', 'Quot.sound', 'Classical.choice'}
    if unexpected:
        raise ValueError(f'unexpected theorem axioms: {unexpected}')

def check_rsum_proof(unsigned=False):
    """Check the actual extracted programs, common behavior type, nonempty
    overlapping caller, arithmetic edge witnesses and capacity domain."""
    subprocess.run([sys.executable, str(ROOT / 'verification/extraction/extract.py'), '--family', 'rsum', '--check'], check=True)
    lean = ROOT / 'verification/lean'
    subprocess.run(['lake', 'build'], cwd=lean, check=True)
    namespace = 'QU8Rsum' if unsigned else 'QS8Rsum'
    kind = 'unsigned' if unsigned else 'signed'
    statement = f"""import Salty
open Salty Salty.CByte Salty.Kernels.Rsum
example (cfg : Config) (c : Call) (capacity : 8 ≤ cfg.capacity) :
  Salty.Equivalent (CByte.machine cfg) (CByte.machine cfg)
    (fun s => ⟨[Salty.Generated.{namespace}.neon], s⟩)
    (fun s => ⟨[Salty.Generated.{namespace}.rvv], s⟩) (fun s => Entry .{kind} s c) :=
  Salty.Kernels.{namespace}.behavior_equivalent cfg c capacity
example : Entry .{kind} witnessState witnessCall := entry_nonempty .{kind}
example : witnessCall.input = witnessCall.output := witness_overlap
example : (resultMemory .{kind} witnessState.memory witnessCall).data 16#64 = 2 := witness_result .{kind}
example : outputScalar .unsigned (4294967295#32) (1#32) = 0 := witness_unsigned_wrap
example : ¬ OutputDefined .signed (2147483647#32) (1#32) := witness_signed_overflow
example : 8 ≤ (Salty.Kernels.RsumExamples.config 32 (by decide) true).capacity := witness_capacity
#print axioms Salty.Kernels.{namespace}.behavior_equivalent
#print axioms Salty.Kernels.Rsum.entry_nonempty
#print axioms Salty.Kernels.Rsum.witness_overlap
#print axioms Salty.Kernels.Rsum.witness_result
#print axioms Salty.Kernels.Rsum.witness_unsigned_wrap
#print axioms Salty.Kernels.Rsum.witness_signed_overflow
#print axioms Salty.Kernels.Rsum.witness_capacity
"""
    with tempfile.TemporaryDirectory(prefix='salty-proof-audit-') as folder:
        check = Path(folder) / 'Check.lean'
        check.write_text(statement)
        result = subprocess.run(['lake', 'env', 'lean', str(check)], cwd=lean,
                                check=True, capture_output=True, text=True)
    dependencies = re.findall(r'depends on axioms: \[([^\]]*)\]', result.stdout)
    axiom_free = re.findall(r'does not depend on any axioms', result.stdout)
    if len(dependencies) + len(axiom_free) != 7:
        raise ValueError('missing axiom audit for registered reduction theorem/witnesses')
    unexpected = {name.strip() for group in dependencies for name in group.split(',')} - {'propext', 'Quot.sound', 'Classical.choice'}
    if unexpected:
        raise ValueError(f'unexpected theorem axioms: {unexpected}')

def check_pack_proof():
    """Check whole extracted packing, nonempty optional-bias callers, preserved
    holes/gaps and raw high-bit scalar copies under the common behavior type."""
    subprocess.run([sys.executable, str(ROOT / 'verification/extraction/extract.py'), '--family', 'pack', '--check'], check=True)
    lean = ROOT / 'verification/lean'
    subprocess.run(['lake', 'build'], cwd=lean, check=True)
    statement = """import Salty
open Salty Salty.CByte Salty.Kernels.X32Pack
example (cfg : Config) (c : Call) (capacity : 8 ≤ cfg.capacity) :
  Salty.Equivalent (CByte.machine cfg) (CByte.machine cfg)
    (fun s => ⟨[Salty.Generated.X32Pack.neon], s⟩)
    (fun s => ⟨[Salty.Generated.X32Pack.rvv], s⟩) (fun s => Entry s c) :=
  behavior_equivalent cfg c capacity
example (withBias : Bool) : Entry (witnessState withBias) (witnessCall withBias) := entry_nonempty withBias
example : (witnessResult false).data 536#64 = 0 := witness_null_header
example : (witnessResult true).data 536#64 = 165 := witness_present_header_hole
example (withBias : Bool) : (witnessResult withBias).data 540#64 = 255 := witness_odd_weight withBias
example (withBias : Bool) : (witnessResult withBias).data 544#64 = 165 := witness_weight_hole withBias
example (withBias : Bool) : (witnessResult withBias).data 548#64 = 165 := witness_extra_gap withBias
example : 8 ≤ (Salty.Kernels.RsumExamples.config 16 (by decide) true).capacity := witness_capacity
#print axioms Salty.Kernels.X32Pack.behavior_equivalent
#print axioms Salty.Kernels.X32Pack.entry_nonempty
#print axioms Salty.Kernels.X32Pack.witness_null_header
#print axioms Salty.Kernels.X32Pack.witness_present_header_hole
#print axioms Salty.Kernels.X32Pack.witness_odd_weight
#print axioms Salty.Kernels.X32Pack.witness_weight_hole
#print axioms Salty.Kernels.X32Pack.witness_extra_gap
#print axioms Salty.Kernels.X32Pack.witness_capacity
"""
    with tempfile.TemporaryDirectory(prefix='salty-proof-audit-') as folder:
        check = Path(folder) / 'Check.lean'
        check.write_text(statement)
        result = subprocess.run(['lake', 'env', 'lean', str(check)], cwd=lean,
                                check=True, capture_output=True, text=True)
    dependencies = re.findall(r'depends on axioms: \[([^\]]*)\]', result.stdout)
    axiom_free = re.findall(r'does not depend on any axioms', result.stdout)
    if len(dependencies) + len(axiom_free) != 8:
        raise ValueError('missing axiom audit for registered packing theorem/witnesses')
    unexpected = {name.strip() for group in dependencies for name in group.split(',')} - {'propext', 'Quot.sound', 'Classical.choice'}
    if unexpected:
        raise ValueError(f'unexpected theorem axioms: {unexpected}')

def check_rdsum_proof(unsigned=False):
    """Check both source-linked row sums, exact whole-function behavior, and
    nonempty caller witnesses distinguishing signed and unsigned bytes."""
    subprocess.run([sys.executable, str(ROOT / 'verification/extraction/extract.py'), '--family', 'rdsum', '--check'], check=True)
    lean = ROOT / 'verification/lean'
    subprocess.run(['lake', 'build'], cwd=lean, check=True)
    namespace, kind = ('QU8Rdsum', 'unsigned') if unsigned else ('QS8Rdsum', 'signed')
    statement = f"""import Salty
open Salty Salty.CByte Salty.Kernels.Rdsum
example (cfg : Config) (c : Call) :
  Salty.Equivalent (CByte.machine cfg) (CByte.machine cfg)
    (fun s => ⟨[Salty.Generated.{namespace}.neon], s⟩)
    (fun s => ⟨[Salty.Generated.{namespace}.rvv], s⟩) (fun s => Entry .{kind} s c) :=
  Salty.Kernels.{namespace}.behavior_equivalent cfg c
example : Entry .{kind} witnessState witnessCall := entry_nonempty .{kind}
example : (resultMemory .signed witnessState.memory witnessCall).data 513#64 = 255 := witness_signed_result
example : (resultMemory .unsigned witnessState.memory witnessCall).data 513#64 = 0 := witness_unsigned_result
#print axioms Salty.Kernels.{namespace}.behavior_equivalent
#print axioms Salty.Kernels.Rdsum.entry_nonempty
#print axioms Salty.Kernels.Rdsum.witness_signed_result
#print axioms Salty.Kernels.Rdsum.witness_unsigned_result
"""
    with tempfile.TemporaryDirectory(prefix='salty-proof-audit-') as folder:
        check = Path(folder) / 'Check.lean'
        check.write_text(statement)
        result = subprocess.run(['lake', 'env', 'lean', str(check)], cwd=lean,
                                check=True, capture_output=True, text=True)
    dependencies = re.findall(r'depends on axioms: \[([^\]]*)\]', result.stdout)
    axiom_free = re.findall(r'does not depend on any axioms', result.stdout)
    if len(dependencies) + len(axiom_free) != 4:
        raise ValueError('missing axiom audit for registered row-sum theorem/witnesses')
    unexpected = {name.strip() for group in dependencies for name in group.split(',')} - {'propext', 'Quot.sound', 'Classical.choice'}
    if unexpected:
        raise ValueError(f'unexpected theorem axioms: {unexpected}')

PROOFS = {
    'qs8-rdsum': ('Salty.Kernels.QS8Rdsum.behavior_equivalent', 'trusted-clang-ast-intrinsics-v1', check_rdsum_proof),
    'qu8-rdsum': ('Salty.Kernels.QU8Rdsum.behavior_equivalent', 'trusted-clang-ast-intrinsics-v1', lambda: check_rdsum_proof(True)),
    'x32-packw-gemm-goi': ('Salty.Kernels.X32Pack.behavior_equivalent', 'trusted-clang-ast-intrinsics-v1', check_pack_proof),
    'qs8-rsum': ('Salty.Kernels.QS8Rsum.behavior_equivalent', 'trusted-clang-ast-intrinsics-v1', check_rsum_proof),
    'qu8-rsum': ('Salty.Kernels.QU8Rsum.behavior_equivalent', 'trusted-clang-ast-intrinsics-v1', lambda: check_rsum_proof(True)),
    'qu8-vadd-minmax': (UADD_THEOREM, UADD_BRIDGE, check_uadd_proof),
    'qs8-vadd-minmax': (ADD_THEOREM, ADD_BRIDGE, check_add_proof),
    'qs8-vlrelu': (LRELU_THEOREM, LRELU_BRIDGE, check_lrelu_proof),
    'qs8-vcvt': (QS8_THEOREM, QS8_BRIDGE, check_qs8_proof),
    's8-vclamp': (S8_THEOREM, S8_BRIDGE, check_s8_proof),
    'x32-transposec': (X32_THEOREM, X32_BRIDGE, check_x32_proof),
}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--refresh', action='store_true', help='refresh hashes, resetting every proof status to pending')
    parser.add_argument('--require-complete', action='store_true')
    args = parser.parse_args()
    subprocess.run([sys.executable, str(ROOT / 'verification/check_layout.py')], check=True)
    current = inventory()
    if args.refresh:
        MANIFEST.write_text(json.dumps({'schema': 1, 'scope': 'Missing and empty targets excluded by user instruction.', 'kernels': current}, indent=2) + '\n')
    stored = json.loads(MANIFEST.read_text())['kernels']
    errors = []
    if len({r['kernel'] for r in stored}) != len(stored): errors.append('duplicate manifest entry')
    if {r['kernel'] for r in current} != {r['kernel'] for r in stored}: errors.append('kernel inventory changed')
    by_name = {r['kernel']: r for r in stored}
    proved = 0
    for row in current:
        old = by_name.get(row['kernel'], {})
        for field in ['source_sha256', 'target_sha256']:
            if row[field] != old.get(field): errors.append(f"{row['kernel']}: {field} changed; review proof provenance")
        if old.get('status') == 'proved_intrinsic':
            registration = PROOFS.get(row['kernel'])
            if (registration is None or row['status'] != 'pending'
                    or old.get('theorem') != registration[0] or old.get('machine_lifting') != registration[1]):
                errors.append(f"{row['kernel']}: unsupported proof registration")
                continue
            try:
                registration[2]()
                proved += 1
            except (subprocess.CalledProcessError, ValueError) as error:
                errors.append(f"{row['kernel']}: proof/regeneration gate failed: {error}")
        elif row['status'] != old.get('status'):
            errors.append(f"{row['kernel']}: incorrect availability/status")
        elif old.get('theorem') is not None or old.get('machine_lifting') is not None:
            errors.append(f"{row['kernel']}: unregistered proof fields")
    available = sum(r['status'] == 'pending' for r in current)
    print(f'{len(current)} sources; {available} implemented targets; {len(current)-available} excluded missing/empty targets')
    print(f'Source-linked intrinsic equivalence theorems: {proved}/{available}. Compiler/binary verification is not claimed.')
    if args.require_complete and proved != available:
        errors.append(f'full verification incomplete: {available - proved} kernel proofs are still required')
    for error in errors: print(error, file=sys.stderr)
    return bool(errors)

if __name__ == '__main__':
    sys.exit(main())

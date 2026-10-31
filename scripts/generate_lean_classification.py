#!/usr/bin/env python3
"""Generate proof branches; Lean, not this enumerator, establishes exhaustiveness.

Every split and forced value is proved from the degree equations by omega.
Each rejected matrix contradicts a corner-cover inequality. Each accepted matrix
is proved equal to one of the ten winners. Cases are separate modules so Lake
can check them concurrently.
"""
from itertools import combinations
from pathlib import Path


def module_source(lines):
    n = 0
    while n < len(lines) and lines[n].startswith('import '):
        n += 1
    return ('module\n\n' + '\n'.join('public '+l for l in lines[:n]) +
            '\n\n@[expose] public section\n' + '\n'.join(lines[n:]) + '\n')

ROOT = Path(__file__).resolve().parents[1] / 'MacMahon'
EDGES = list(combinations(range(6), 2))
solutions = []

def enumerate_degrees(n, remaining, values):
    if n == len(EDGES):
        if not any(remaining):
            solutions.append(values)
        return
    i, j = EDGES[n]
    for value in range(min(remaining[i], remaining[j]) + 1):
        rest = remaining[:]
        rest[i] -= value
        rest[j] -= value
        if any(rest[k] and not any(k in e for e in EDGES[n+1:]) for k in range(6)):
            continue
        enumerate_degrees(n+1, rest, values + [value])

enumerate_degrees(0, [2]*6, [])
parts = [{0, *p} for p in combinations(range(1, 6), 2)]
winners = [[int((i in p) == (j in p)) for i, j in EDGES] for p in parts]
patterns = sorted({tuple(s[:5]) for s in solutions})
symmetry_names = ', '.join(f's{j}{i}' for i, j in EDGES)
entry_names = ', '.join(f'e{i}{j}' for i, j in EDGES)
all_names = symmetry_names + ', ' + ', '.join(f'z{i}' for i in range(6)) + ', ' + entry_names
header = ['namespace MacMahon', 'open scoped BigOperators',
          'set_option maxHeartbeats 0', 'set_option maxRecDepth 100000']
args = ['(a : Inventory) (hz : DiagonalZero a)',
        '    (hr : ∀ i, row a i = 2) (hs : ∀ i j, a (i,j) = a (j,i))',
        '    (hp : ∀ b : Fin 10, 0 < ∑ p : Pair, winner b p * a p)']
prelude = [f'  have s{j}{i} := hs {j} {i}' for i, j in EDGES]
prelude += ['  clear hs',
    '  norm_num [DiagonalZero, row, Fin.forall_fin_succ, Fin.sum_univ_succ] at hz hr',
    '  norm_num [Fin.forall_fin_succ, winner, winningMatrix, Fintype.sum_prod_type, Fin.sum_univ_succ] at hp',
    f'  simp only [{symmetry_names}] at hr hp',
    '  rcases hz with ⟨z0,z1,z2,z3,z4,z5⟩',
    '  simp only [z0,z1,z2,z3,z4,z5, Nat.add_zero, Nat.zero_add] at hr hp',
    '  revert hp']

def emit(lines, candidates, n, indent, stop, leaf):
    pad = ' '*indent
    if n == stop:
        leaf(lines, candidates, pad)
        return
    i, j = EDGES[n]
    values = sorted({s[n] for s in candidates})
    name = f'e{i}{j}'
    if len(values) == 1:
        lines.append(pad + f'have {name} : a ({i},{j}) = {values[0]} := by omega')
        emit(lines, candidates, n+1, indent, stop, leaf)
        return
    lines.append(pad + 'have split : ' + ' ∨ '.join(f'a ({i},{j}) = {v}' for v in values) + ' := by omega')
    lines.append(pad + 'rcases split with ' + ' | '.join(name for _ in values))
    for v in values:
        lines.append(pad + '·')
        emit(lines, [s for s in candidates if s[n] == v], n+1, indent+2, stop, leaf)

def finish_matrix(lines, candidates, pad):
    matrix = candidates[0]
    if matrix not in winners:
        lines += [pad + 'intro hp', pad + f'norm_num [{entry_names}] at hp']
        return
    b = winners.index(matrix)
    lines += [pad + 'intro _hp', pad + f'refine ⟨{b}, ?_⟩',
        pad + 'funext p', pad + 'rcases p with ⟨i,j⟩',
        pad + f'fin_cases i <;> fin_cases j <;> norm_num [winner, winningMatrix, {all_names}]']

(ROOT / 'ClassificationCases').mkdir(exist_ok=True)
for b, pattern in enumerate(patterns):
    lines = ['import MacMahon.Structure'] + header
    lines += [f'lemma classify_row_{b} ' + args[0]] + args[1:]
    lines += ['    ' + ' '.join(f'(e0{j+1} : a (0,{j+1}) = {v})' for j, v in enumerate(pattern))]
    lines += ['    : ∃ b : Fin 10, a = winner b := by'] + prelude
    emit(lines, [s for s in solutions if tuple(s[:5]) == pattern], 5, 2, 15, finish_matrix)
    lines += ['end MacMahon']
    (ROOT / f'ClassificationCases/Case{b}.lean').write_text(module_source(lines))

lines = [f'import MacMahon.ClassificationCases.Case{b}' for b in range(len(patterns))] + header
lines += ['/-- Exhaustive classification of all symmetric degree-two inventories. -/',
          'lemma classify_degree_two ' + args[0]] + args[1:]
lines += ['    : ∃ b : Fin 10, a = winner b := by',
          '  have h0 := hr 0', '  have z0 := hz 0',
          '  norm_num [row, Fin.sum_univ_succ, z0] at h0']
def finish_row(lines, candidates, pad):
    b = patterns.index(tuple(candidates[0][:5]))
    lines.append(pad + f'exact classify_row_{b} a hz hr hs hp e01 e02 e03 e04 e05')
emit(lines, solutions, 0, 2, 5, finish_row)
lines += ['end MacMahon']
(ROOT / 'Classification.lean').write_text(module_source(lines))
print(f'Generated {len(solutions)} matrix branches in {len(patterns)} modules.')

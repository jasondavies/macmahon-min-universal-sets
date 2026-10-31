# The Ten Minimum Universal Sets of MacMahon Cubes

Paper and Lean formalization by Jason Davies, developed with AI assistance.
Repository: [jasondavies/macmahon-min-universal-sets](https://github.com/jasondavies/macmahon-min-universal-sets).
The URL is the intended public repository; this package does not publish it.

A universal inventory of six-coloured MacMahon cubes can build every target
variety as a 2×2×2 cube. The minimum size is **12**, and exactly **ten labelled
inventories** attain it, even when repetitions are allowed. They contain one
copy of every directed edge within each part of a 3+3 partition of Conway's
six tableau labels: two disjoint triangles. At the minimum there are no repeats.

Only exterior faces must match the target. Internal face colours are unrestricted.
Proper rotations identify cube varieties; reflections do not. The count ten uses
fixed face-colour labels, not equivalence under colour permutations. The tableau
labels A–F are not the six face colours.

- [Paper (PDF)](paper/macmahon-min-universal-sets.pdf) and [LaTeX](paper/macmahon-min-universal-sets.tex).
- [Main Lean results](MacMahon/Theorems.lean) and [physical-model interface](MacMahon/Submission.lean).
- [Independent statement surface](Challenge.lean), [proof entry point](Solution.lean), and [comparator configuration](comparator.json).
- [Provenance, scope and AI disclosure](formalization.yaml).
- Existing visualization work remains under `viz/`; `notes.txt` and `viz_prompt.md`
  are historical planning documents and can contain superseded verification status.

The classification resolves the conjectures stated by Johnson and Roldán
([2024, Conjectures 4 and 8](https://arxiv.org/abs/2407.13208v1)) and extends the
classification to arbitrary multiplicities. The lower bound twelve is prior work
of [Haraguchi](https://arxiv.org/abs/1408.3696v2). Independent human expert review
and a comprehensive publication-priority check remain outstanding.

## Build and verification

Install [Elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get
make check
make paper
```

Lean 4.35.0 and mathlib v4.35.0 are pinned in `lean-toolchain` and
`lake-manifest.json`. `make check` checks module headers and metadata, builds the
library and independent challenge, compares the axiom audit with its recorded
output, and checks that the data generator reproduces both generated modules.
Ruby, Python 3 and Lean are needed; building the paper also needs LaTeX/latexmk.
The intentional `sorry` warnings belong only to `Challenge.lean`.

`MacMahon.lean` contains guarded axiom audits. The proof library contains no
`sorry`, `admit`, custom axioms or `native_decide`; only `propext`,
`Classical.choice` and `Quot.sound` are permitted. Finite computations use
`decide +kernel`. The arithmetic tactics produce proof terms for the kernel.

## Palomar submission surface

The layout follows [PalomarTemplate](https://github.com/PalomarRegistry/PalomarTemplate)
and the author's `euclid-uniform-processes` project.

`Challenge.lean` imports **only Mathlib** and defines its own physical model and
finite geometric tables. It states ten advertised results with intentional proof
holes. `Solution.lean` imports the completed proofs under the same names.
The challenge does not import or regenerate itself from the proof library.

The comparator targets are:

| Result | Declaration in `MacMahon` |
| --- | --- |
| Minimum 12, attained | `minimum_size` |
| Lower bound for every universal inventory | `physical_minimum` |
| Exactly ten labelled minima | `physical_exactly_ten` |
| Two-triangle characterization | `physical_iff_two_triangles` |
| No repeated varieties at the minimum | `physical_minimum_has_no_repeats` |
| Table equals all proper signed-axis rotations | `proper_rotation_iff` |
| Outward-face rule for the eight positions | `exposed_face_rule` |
| Each representative uses six distinct colours | `face_colours_valid` |
| Every six-colour face assignment is represented | `face_assignment_coverage` |
| Its variety and rotation are unique | `face_assignment_unique` |

Run the local comparator on Linux with bubblewrap installed:

```sh
make comparator
```

The local run passed statement comparison and all three kernels; see the
[comparator log](validation/comparator.txt) and [verification record](validation/local-checks.json).
This is a local verification result, not Palomar registry acceptance.

The helper uses the pinned toolchain's Lean checker, NanoDa and con-ron, matching
Palomar's independent-kernel setup. Dependencies under `.lake/packages` must be
real directories rather than symlinks outside the checkout. The submitted
`comparator.json` intentionally does not set registry-owned external-kernel options.
The helper injects those options only into a temporary local configuration.

The [manual preflight workflow](.github/workflows/palomar-preflight.yml) invokes
Palomar's reusable verifier at the same immutable revision used by the reference
project. It is advisory, does not submit the result, and has not been dispatched
by preparing these files. Before submitting, publish the repository, commit the
reviewed snapshot, run preflight on that exact commit and use its full 40-character
SHA in the [Palomar submission form](https://submit.palomar-registry.org).
Author/maintainer declarations must be made by the responsible submitter.

## Proof organization and scope

`Types.lean` defines the finite domains; `Data.lean` supplies geometric constants. `Rotations.lean` checks proper rotations;
`Colourings.lean` proves that the 30 varieties × 24 rotations account for all 720
face assignments. `Geometry.lean` equates corner compatibility with face matching.
`WitnessData.lean` supplies construction certificates; `Witness.lean` checks all
300 minimum-set–target constructions. `Geometry.lean` also relates corner-based
builds to physical constructions, independently of the witness certificates.

`Counting.lean` derives necessary usability and corner-cover conditions.
`Arithmetic.lean` proves the inequalities, minimum bound and row and column sums
for arbitrary natural multiplicities; `Structure.lean` proves symmetry.
`Partitions.lean` defines the ten candidates directly as two triangles.
`Classification.lean` uses label permutations to reduce the first row to two
local configurations: a doubled edge or two distinct neighbours. The partition-cover
inequalities exclude the former and close a triangle in the latter; the degree
equations then determine the entire inventory. `Theorems.lean` assembles the
classification and exact count. `Model.lean` remains a compatibility import for
the separated counting, geometry and witness interfaces.

The model is discrete cube geometry, not a formalization of Euclidean solids in
real coordinates. Every physical construction uses an injective assignment of
physical copies, with an independent proper rotation at each position.

The paper also reports exhaustive target-count histograms for inventory sizes
8–13, including the minimum size for exactly 29 targets. **Those computational
results are not Lean theorems.** Their saved data and independent checker are
included under `results/cubes/` and `scripts/`. No square-tiling conjecture is
claimed here.

## Reproduce the computational artifacts

```sh
make cubes
python3 scripts/run_cube_experiment.py --k 12 --threads 8 --histogram --selftest \
  --output results/cubes/k12.json
python3 scripts/run_cube_experiment.py --k 12 --threads 8 --histogram \
  --matching-tables --output results/cubes/k12-matching.json
python3 -O scripts/verify_cubes.py
make regenerate
make check
```

The C++ solver uses OpenMP. Graph and matching runs share the outer enumeration
and tableau; the geometric checker is separate. Regeneration writes the finite
geometric tables and construction witnesses, whose correctness is then checked
by Lean. The generator is not a trusted proof component. The original exploration lives
in the separate `macmahon` workspace; this repository is self-contained for the
cube result and does not import that workspace.

## License and disclosure

Apache License 2.0; see [LICENSE](LICENSE). Cited sources and dependencies retain
their own licenses. The paper, formalization and supporting computation were
produced with OpenAI Codex under the author's direction. Detailed provenance,
review status and the distinction between formal and computational claims are
recorded in [formalization.yaml](formalization.yaml).

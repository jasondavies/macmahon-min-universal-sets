module

public import MacMahon.Definitions

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MacMahon

-- Separate target checks keep independent-kernel reduction within arena limits.

private theorem face_corner_01 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 0 1 k) ↔ ∃ r : Fin 24, FaceFits (0,1) p k r := by
  decide +kernel

private theorem face_corner_02 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 0 2 k) ↔ ∃ r : Fin 24, FaceFits (0,2) p k r := by
  decide +kernel

private theorem face_corner_03 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 0 3 k) ↔ ∃ r : Fin 24, FaceFits (0,3) p k r := by
  decide +kernel

private theorem face_corner_04 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 0 4 k) ↔ ∃ r : Fin 24, FaceFits (0,4) p k r := by
  decide +kernel

private theorem face_corner_05 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 0 5 k) ↔ ∃ r : Fin 24, FaceFits (0,5) p k r := by
  decide +kernel

private theorem face_corner_10 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 1 0 k) ↔ ∃ r : Fin 24, FaceFits (1,0) p k r := by
  decide +kernel

private theorem face_corner_12 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 1 2 k) ↔ ∃ r : Fin 24, FaceFits (1,2) p k r := by
  decide +kernel

private theorem face_corner_13 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 1 3 k) ↔ ∃ r : Fin 24, FaceFits (1,3) p k r := by
  decide +kernel

private theorem face_corner_14 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 1 4 k) ↔ ∃ r : Fin 24, FaceFits (1,4) p k r := by
  decide +kernel

private theorem face_corner_15 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 1 5 k) ↔ ∃ r : Fin 24, FaceFits (1,5) p k r := by
  decide +kernel

private theorem face_corner_20 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 2 0 k) ↔ ∃ r : Fin 24, FaceFits (2,0) p k r := by
  decide +kernel

private theorem face_corner_21 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 2 1 k) ↔ ∃ r : Fin 24, FaceFits (2,1) p k r := by
  decide +kernel

private theorem face_corner_23 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 2 3 k) ↔ ∃ r : Fin 24, FaceFits (2,3) p k r := by
  decide +kernel

private theorem face_corner_24 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 2 4 k) ↔ ∃ r : Fin 24, FaceFits (2,4) p k r := by
  decide +kernel

private theorem face_corner_25 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 2 5 k) ↔ ∃ r : Fin 24, FaceFits (2,5) p k r := by
  decide +kernel

private theorem face_corner_30 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 3 0 k) ↔ ∃ r : Fin 24, FaceFits (3,0) p k r := by
  decide +kernel

private theorem face_corner_31 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 3 1 k) ↔ ∃ r : Fin 24, FaceFits (3,1) p k r := by
  decide +kernel

private theorem face_corner_32 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 3 2 k) ↔ ∃ r : Fin 24, FaceFits (3,2) p k r := by
  decide +kernel

private theorem face_corner_34 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 3 4 k) ↔ ∃ r : Fin 24, FaceFits (3,4) p k r := by
  decide +kernel

private theorem face_corner_35 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 3 5 k) ↔ ∃ r : Fin 24, FaceFits (3,5) p k r := by
  decide +kernel

private theorem face_corner_40 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 4 0 k) ↔ ∃ r : Fin 24, FaceFits (4,0) p k r := by
  decide +kernel

private theorem face_corner_41 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 4 1 k) ↔ ∃ r : Fin 24, FaceFits (4,1) p k r := by
  decide +kernel

private theorem face_corner_42 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 4 2 k) ↔ ∃ r : Fin 24, FaceFits (4,2) p k r := by
  decide +kernel

private theorem face_corner_43 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 4 3 k) ↔ ∃ r : Fin 24, FaceFits (4,3) p k r := by
  decide +kernel

private theorem face_corner_45 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 4 5 k) ↔ ∃ r : Fin 24, FaceFits (4,5) p k r := by
  decide +kernel

private theorem face_corner_50 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 5 0 k) ↔ ∃ r : Fin 24, FaceFits (5,0) p k r := by
  decide +kernel

private theorem face_corner_51 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 5 1 k) ↔ ∃ r : Fin 24, FaceFits (5,1) p k r := by
  decide +kernel

private theorem face_corner_52 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 5 2 k) ↔ ∃ r : Fin 24, FaceFits (5,2) p k r := by
  decide +kernel

private theorem face_corner_53 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 5 3 k) ↔ ∃ r : Fin 24, FaceFits (5,3) p k r := by
  decide +kernel

private theorem face_corner_54 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 5 4 k) ↔ ∃ r : Fin 24, FaceFits (5,4) p k r := by
  decide +kernel

theorem face_corner_equivalence : ∀ i j : Label, i ≠ j → ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt i j k) ↔ ∃ r : Fin 24, FaceFits (i,j) p k r := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact face_corner_01
  · exact face_corner_02
  · exact face_corner_03
  · exact face_corner_04
  · exact face_corner_05
  · exact face_corner_10
  · exact (hij rfl).elim
  · exact face_corner_12
  · exact face_corner_13
  · exact face_corner_14
  · exact face_corner_15
  · exact face_corner_20
  · exact face_corner_21
  · exact (hij rfl).elim
  · exact face_corner_23
  · exact face_corner_24
  · exact face_corner_25
  · exact face_corner_30
  · exact face_corner_31
  · exact face_corner_32
  · exact (hij rfl).elim
  · exact face_corner_34
  · exact face_corner_35
  · exact face_corner_40
  · exact face_corner_41
  · exact face_corner_42
  · exact face_corner_43
  · exact (hij rfl).elim
  · exact face_corner_45
  · exact face_corner_50
  · exact face_corner_51
  · exact face_corner_52
  · exact face_corner_53
  · exact face_corner_54
  · exact (hij rfl).elim

/-- Corner matching is exactly matching the exposed faces by proper rotations. -/

theorem builds_iff_physical (a : Inventory) (i j : Label) (h : i ≠ j) :
    Builds a (i,j) ↔ PhysicalBuilds a (i,j) := by
  constructor <;> rintro ⟨f,hf⟩ <;> refine ⟨f, ?_⟩ <;> intro k
  · exact (face_corner_equivalence i j h (f k).1 k).mp (hf k)
  · exact (face_corner_equivalence i j h (f k).1 k).mpr (hf k)

theorem universal_iff_physical (a : Inventory) : Universal a ↔ PhysicalUniversal a := by
  constructor <;> intro h i j hij
  · exact (builds_iff_physical a i j hij).mp (h i j hij)
  · exact (builds_iff_physical a i j hij).mpr (h i j hij)

end MacMahon

module

public import MacMahon.Partitions

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MacMahon
theorem cornerAt_mem : ∀ i j : Label, i ≠ j → ∀ k : Slot,
    HasCorner (i,j) (cornerAt i j k) := by decide +kernel


theorem every_corner : ∀ c : Corner, ∃ i j : Label, i ≠ j ∧
    ∃ k : Slot, cornerAt i j k = c := by decide +kernel


theorem usable_rule : ∀ i j : Label, i ≠ j → ∀ p : Pair,
    Usable (i,j) p ↔ p.1 ≠ p.2 ∧
      (p = (i,j) ∨ (p.1 ≠ i ∧ p.2 ≠ j ∧ p ≠ (j,i))) := by decide +kernel



theorem partition_corner_support : ∀ b : Fin 10, ∀ p : Pair,
    HasCorner p (partitionCorner b) → winner b p = 1 := by decide +kernel


end MacMahon

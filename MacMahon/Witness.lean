module

public import MacMahon.Definitions

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MacMahon
theorem witness_facts : ∀ b : Fin 10, ∀ i j : Label, i ≠ j →
    Function.Injective (witness b i j) ∧ ∀ k : Slot,
      winner b (witness b i j k) = 1 ∧
      HasCorner (witness b i j k) (cornerAt i j k) := by decide +kernel


theorem partition_corner_support : ∀ b : Fin 10, ∀ p : Pair,
    HasCorner p (partitionCorner b) → winner b p = 1 := by decide +kernel


theorem winners_distinct : Function.Injective winner := by decide +kernel


end MacMahon

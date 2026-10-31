module

public import MacMahon.Partitions
public import MacMahon.WitnessData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MacMahon
theorem witness_facts : ∀ b : Fin 10, ∀ i j : Label, i ≠ j →
    Function.Injective (witness b i j) ∧ ∀ k : Slot,
      winner b (witness b i j k) = 1 ∧
      HasCorner (witness b i j k) (cornerAt i j k) := by decide +kernel

/-- Every known set has an explicit eight-cube construction for every target. -/
theorem winner_universal (b : Fin 10) : Universal (winner b) := by
  intro i j hij
  obtain ⟨hinj,hfit⟩ := witness_facts b i j hij
  let f : Slot → Stock (winner b) := fun k =>
    ⟨witness b i j k, ⟨0, by rw [(hfit k).1]; decide⟩⟩
  refine ⟨⟨f, ?_⟩, fun k => (hfit k).2⟩
  intro k l heq
  exact hinj (congrArg Sigma.fst heq)

end MacMahon

module

public import MacMahon.Definitions

@[expose] public section
namespace MacMahon
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The ten unordered partitions, choosing the triple containing label 0. -/
def triple : Fin 10 → Finset Label :=
  ![{0,1,2}, {0,1,3}, {0,1,4}, {0,1,5}, {0,2,3},
    {0,2,4}, {0,2,5}, {0,3,4}, {0,3,5}, {0,4,5}]

/-- One copy of each directed edge within either triple. -/
def twoTriangles (s : Finset Label) : Inventory := fun p =>
  if p.1 ≠ p.2 ∧ ((p.1 ∈ s ∧ p.2 ∈ s) ∨ (p.1 ∉ s ∧ p.2 ∉ s)) then 1 else 0

lemma winner_two_triangles : ∀ b : Fin 10,
    (triple b).card = 3 ∧ winner b = twoTriangles (triple b) := by decide +kernel

lemma partition_complete : ∀ s : Finset Label, s.card = 3 →
    ∃ b : Fin 10, twoTriangles s = winner b := by decide +kernel

lemma winners_iff_two_triangles (a : Inventory) :
    (∃ b : Fin 10, a = winner b) ↔
    ∃ s : Finset Label, s.card = 3 ∧ a = twoTriangles s := by
  constructor
  · rintro ⟨b,rfl⟩
    exact ⟨triple b, winner_two_triangles b⟩
  · rintro ⟨s,hs,rfl⟩
    exact partition_complete s hs
end MacMahon

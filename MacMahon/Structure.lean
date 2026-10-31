module

public import MacMahon.Definitions

@[expose] public section
namespace MacMahon
open scoped BigOperators

lemma entry_le_row (a : Inventory) (i j : Label) : a (i,j) ≤ row a i :=
  Finset.single_le_sum (f := fun j => a (i,j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

/-- Degree two and reciprocal support force reciprocal multiplicities. -/
lemma symmetric_of_degree_two (a : Inventory)
    (hr : ∀ i, row a i = 2) (hc : ∀ i, col a i = 2)
    (hb : ∀ i j, a (j,i) ≤ 2 * a (i,j)) : ∀ i j, a (i,j) = a (j,i) := by
  have ht : ∀ i j, a (i,j) = 2 → a (j,i) = 2 := by
    intro i j hij
    have hzero : ∀ k, k ≠ j → a (k,i) = 0 := by
      intro k hkj
      have hsum : a (i,j) + a (i,k) ≤ row a i :=
        Finset.add_le_sum (f := fun j => a (i,j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
          (Finset.mem_univ k) hkj.symm
      have := hb i k
      rw [hr i, hij] at hsum
      omega
    have hsum : col a i = a (j,i) :=
      Finset.sum_eq_single j (fun k _ hk => hzero k hk) (by simp)
    have := hc i
    omega
  intro i j
  have hi := entry_le_row a i j
  have hj := entry_le_row a j i
  rw [hr i] at hi
  rw [hr j] at hj
  have hb1 := hb i j
  have hb2 := hb j i
  have ht1 := ht i j
  have ht2 := ht j i
  omega
end MacMahon

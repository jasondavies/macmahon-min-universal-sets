module

public import MacMahon.Structure
public import MacMahon.Partitions

@[expose] public section
namespace MacMahon
open scoped BigOperators

/-!
The first row of a symmetric degree-two inventory has either one doubled edge
or two distinct neighbours. Relabel these to 01 or to 01 and 02. The ten
partition-cover inequalities exclude the doubled edge and force 12 in the
second case. The degree equations then force the two triangles completely.
-/

/-- Pull an inventory back along a permutation of the tableau labels. -/
def relabel (e : Equiv.Perm Label) (a : Inventory) : Inventory :=
  fun p => a (e p.1, e p.2)

lemma row_relabel (e : Equiv.Perm Label) (a : Inventory) (i : Label) :
    row (relabel e a) i = row a (e i) :=
  Equiv.sum_comp e (fun j => a (e i, j))

lemma partition_sum_relabel (e : Equiv.Perm Label) (a : Inventory) (s : Finset Label) :
    (∑ p, twoTriangles s p * relabel e a p) =
      ∑ p, twoTriangles (s.map e.toEmbedding) p * a p := by
  rw [← (e.prodCongr e).sum_comp (fun p => twoTriangles (s.map e.toEmbedding) p * a p)]
  apply Finset.sum_congr rfl
  intro p _
  simp [twoTriangles, relabel, Prod.map]

lemma partition_cover_relabel (e : Equiv.Perm Label) (a : Inventory)
    (hp : ∀ b : Fin 10, 0 < ∑ p : Pair, winner b p * a p) :
    ∀ b : Fin 10, 0 < ∑ p : Pair, winner b p * relabel e a p := by
  intro b
  obtain ⟨c, hc⟩ := partition_complete ((triple b).map e.toEmbedding)
    (by simp [(winner_two_triangles b).1])
  change 0 < ∑ p, twoTriangles (triple b) p * relabel e a p
  rw [partition_sum_relabel, hc]
  exact hp c

private lemma row_shape (f : Label → ℕ) (hz : f 0 = 0) (hs : ∑ i, f i = 2) :
    (∃ i, i ≠ 0 ∧ f i = 2) ∨
    (∃ i j, i ≠ 0 ∧ j ≠ 0 ∧ i ≠ j ∧ f i = 1 ∧ f j = 1) := by
  obtain ⟨i, _, hi⟩ := Finset.sum_pos_iff.mp (show 0 < ∑ i, f i by omega)
  have hi0 : i ≠ 0 := by rintro rfl; omega
  have hib : f i ≤ 2 := by
    calc f i ≤ ∑ j, f j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
         _ = 2 := hs
  by_cases hi2 : f i = 2
  · exact Or.inl ⟨i, hi0, hi2⟩
  have hi1 : f i = 1 := by omega
  have hrest : ∑ j ∈ Finset.univ.erase i, f j = 1 := by
    have := Finset.sum_erase_add (Finset.univ) f (Finset.mem_univ i)
    omega
  obtain ⟨j, hj, hjp⟩ := Finset.sum_pos_iff.mp
    (show 0 < ∑ j ∈ Finset.univ.erase i, f j by omega)
  have hj0 : j ≠ 0 := by rintro rfl; omega
  have hjb : f j ≤ 1 := by
    calc f j ≤ ∑ k ∈ Finset.univ.erase i, f k :=
           Finset.single_le_sum (fun _ _ => Nat.zero_le _) hj
         _ = 1 := hrest
  exact Or.inr ⟨i, j, hi0, hj0, (Finset.mem_erase.mp hj).1.symm, hi1, by omega⟩

set_option maxHeartbeats 1000000 in
/-- Partition cover excludes a doubled edge at the normalized position 01. -/
lemma no_normalized_doubled_edge (a : Inventory) (hz : DiagonalZero a)
    (hr : ∀ i, row a i = 2) (hs : ∀ i j, a (i,j) = a (j,i))
    (hp : ∀ b : Fin 10, 0 < ∑ p : Pair, winner b p * a p) : a (0,1) ≠ 2 := by
  norm_num [DiagonalZero, row, Fin.forall_fin_succ, Fin.sum_univ_succ] at hz hr hs
  norm_num [Fin.forall_fin_succ, winner, twoTriangles, triple,
    Fintype.sum_prod_type, Fin.sum_univ_succ, -add_pos_iff] at hp
  omega

set_option maxHeartbeats 1000000 in
/-- Two unit edges from 0 must close to the triangle on labels 0, 1 and 2. -/
lemma normalized_triangle_closes (a : Inventory) (hz : DiagonalZero a)
    (hr : ∀ i, row a i = 2) (hs : ∀ i j, a (i,j) = a (j,i))
    (hp : ∀ b : Fin 10, 0 < ∑ p : Pair, winner b p * a p)
    (h01 : a (0,1) = 1) (h02 : a (0,2) = 1) : a (1,2) = 1 := by
  norm_num [DiagonalZero, row, Fin.forall_fin_succ, Fin.sum_univ_succ] at hz hr hs
  norm_num [Fin.forall_fin_succ, winner, twoTriangles, triple,
    Fintype.sum_prod_type, Fin.sum_univ_succ, -add_pos_iff] at hp
  omega

set_option maxHeartbeats 1000000 in
/-- Two local configurations suffice after permuting the labels. -/
private lemma classify_normalized (a : Inventory) (hz : DiagonalZero a)
    (hr : ∀ i, row a i = 2) (hs : ∀ i j, a (i,j) = a (j,i))
    (hp : ∀ b : Fin 10, 0 < ∑ p : Pair, winner b p * a p)
    (hn : a (0,1) = 2 ∨ (a (0,1) = 1 ∧ a (0,2) = 1)) : a = winner 0 := by
  rcases hn with hdouble | ⟨h01, h02⟩
  · exact (no_normalized_doubled_edge a hz hr hs hp hdouble).elim
  have h12 := normalized_triangle_closes a hz hr hs hp h01 h02
  clear hp
  have s10 := hs 1 0
  have s20 := hs 2 0
  have s30 := hs 3 0
  have s40 := hs 4 0
  have s50 := hs 5 0
  have s21 := hs 2 1
  have s31 := hs 3 1
  have s41 := hs 4 1
  have s51 := hs 5 1
  have s32 := hs 3 2
  have s42 := hs 4 2
  have s52 := hs 5 2
  have s43 := hs 4 3
  have s53 := hs 5 3
  have s54 := hs 5 4
  clear hs
  norm_num [DiagonalZero, row, Fin.forall_fin_succ, Fin.sum_univ_succ] at hz hr
  simp only [s10, s20, s30, s40, s50, s21, s31, s41, s51, s32, s42, s52, s43, s53, s54] at hr
  rcases hz with ⟨z0, z1, z2, z3, z4, z5⟩
  simp only [z0, z1, z2, z3, z4, z5, Nat.add_zero, Nat.zero_add] at hr
  funext ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    norm_num [winner, twoTriangles, triple, s10, s20, s30, s40, s50, s21, s31, s41, s51, s32, s42, s52, s43, s53, s54, z0, z1, z2, z3, z4, z5] <;> omega

/-- Complete classification using two local configurations, up to relabelling. -/
lemma classify_degree_two (a : Inventory) (hz : DiagonalZero a)
    (hr : ∀ i, row a i = 2) (hs : ∀ i j, a (i,j) = a (j,i))
    (hp : ∀ b : Fin 10, 0 < ∑ p : Pair, winner b p * a p) :
    ∃ b : Fin 10, a = winner b := by
  suffices he : ∃ e : Equiv.Perm Label, relabel e a = winner 0 by
    obtain ⟨e, he⟩ := he
    apply (winners_iff_two_triangles a).mpr
    refine ⟨(triple 0).map e.toEmbedding, by simp [(winner_two_triangles 0).1], ?_⟩
    funext p
    have hh := congrFun he (e.symm p.1, e.symm p.2)
    simpa [relabel, winner, twoTriangles] using hh
  have normalize (e : Equiv.Perm Label)
      (hn : relabel e a (0,1) = 2 ∨
        (relabel e a (0,1) = 1 ∧ relabel e a (0,2) = 1)) :
      relabel e a = winner 0 :=
    classify_normalized (relabel e a) (fun i => hz (e i))
      (fun i => (row_relabel e a i).trans (hr (e i)))
      (fun i j => hs (e i) (e j)) (partition_cover_relabel e a hp) hn
  rcases row_shape (fun j => a (0,j)) (hz 0) (hr 0) with
    ⟨i, hi0, hi⟩ | ⟨i, j, hi0, hj0, hij, hi, hj⟩
  · let e : Equiv.Perm Label := Equiv.swap 1 i
    have he0 : e 0 = 0 := Equiv.swap_apply_of_ne_of_ne (by decide) hi0.symm
    refine ⟨e, normalize e (Or.inl ?_)⟩
    simpa [relabel, he0, e] using hi
  · let f : Fin 3 → Label := ![0, 1, 2]
    let g : Fin 3 → Label := ![0, i, j]
    have hf : Function.Injective f := by decide +kernel
    have hg : Function.Injective g := by
      simp [Function.Injective, Fin.forall_fin_succ, g,
        hi0, hj0, hij, hi0.symm, hj0.symm, hij.symm]
    obtain ⟨e, he⟩ := Equiv.Perm.exists_extending_pair f g hf hg
    have he0 : e 0 = 0 := he 0
    have he1 : e 1 = i := he 1
    have he2 : e 2 = j := he 2
    refine ⟨e, normalize e (Or.inr ?_)⟩
    simpa [relabel, he0, he1, he2] using And.intro hi hj

end MacMahon

module

public import MacMahon.Structure

@[expose] public section
namespace MacMahon
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma classify_row_6 (a : Inventory) (hz : DiagonalZero a)
    (hr : ∀ i, row a i = 2) (hs : ∀ i j, a (i,j) = a (j,i))
    (hp : ∀ b : Fin 10, 0 < ∑ p : Pair, winner b p * a p)
    (e01 : a (0,1) = 0) (e02 : a (0,2) = 1) (e03 : a (0,3) = 0) (e04 : a (0,4) = 0) (e05 : a (0,5) = 1)
    : ∃ b : Fin 10, a = winner b := by
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
  norm_num [Fin.forall_fin_succ, winner, winningMatrix, Fintype.sum_prod_type, Fin.sum_univ_succ] at hp
  simp only [s10, s20, s30, s40, s50, s21, s31, s41, s51, s32, s42, s52, s43, s53, s54] at hr hp
  rcases hz with ⟨z0,z1,z2,z3,z4,z5⟩
  simp only [z0,z1,z2,z3,z4,z5, Nat.add_zero, Nat.zero_add] at hr hp
  revert hp
  have split : a (1,2) = 0 ∨ a (1,2) = 1 := by omega
  rcases split with e12 | e12
  ·
    have split : a (1,3) = 0 ∨ a (1,3) = 1 ∨ a (1,3) = 2 := by omega
    rcases split with e13 | e13 | e13
    ·
      have split : a (1,4) = 1 ∨ a (1,4) = 2 := by omega
      rcases split with e14 | e14
      ·
        have e15 : a (1,5) = 1 := by omega
        have e23 : a (2,3) = 1 := by omega
        have e24 : a (2,4) = 0 := by omega
        have e25 : a (2,5) = 0 := by omega
        have e34 : a (3,4) = 1 := by omega
        have e35 : a (3,5) = 0 := by omega
        have e45 : a (4,5) = 0 := by omega
        intro hp
        norm_num [e01, e02, e03, e04, e05, e12, e13, e14, e15, e23, e24, e25, e34, e35, e45] at hp
      ·
        have e15 : a (1,5) = 0 := by omega
        have e23 : a (2,3) = 1 := by omega
        have e24 : a (2,4) = 0 := by omega
        have e25 : a (2,5) = 0 := by omega
        have e34 : a (3,4) = 0 := by omega
        have e35 : a (3,5) = 1 := by omega
        have e45 : a (4,5) = 0 := by omega
        intro hp
        norm_num [e01, e02, e03, e04, e05, e12, e13, e14, e15, e23, e24, e25, e34, e35, e45] at hp
    ·
      have split : a (1,4) = 0 ∨ a (1,4) = 1 := by omega
      rcases split with e14 | e14
      ·
        have e15 : a (1,5) = 1 := by omega
        have e23 : a (2,3) = 0 := by omega
        have e24 : a (2,4) = 1 := by omega
        have e25 : a (2,5) = 0 := by omega
        have e34 : a (3,4) = 1 := by omega
        have e35 : a (3,5) = 0 := by omega
        have e45 : a (4,5) = 0 := by omega
        intro hp
        norm_num [e01, e02, e03, e04, e05, e12, e13, e14, e15, e23, e24, e25, e34, e35, e45] at hp
      ·
        have e15 : a (1,5) = 0 := by omega
        have split : a (2,3) = 0 ∨ a (2,3) = 1 := by omega
        rcases split with e23 | e23
        ·
          have split : a (2,4) = 0 ∨ a (2,4) = 1 := by omega
          rcases split with e24 | e24
          ·
            have e25 : a (2,5) = 1 := by omega
            have e34 : a (3,4) = 1 := by omega
            have e35 : a (3,5) = 0 := by omega
            have e45 : a (4,5) = 0 := by omega
            intro _hp
            refine ⟨6, ?_⟩
            funext p
            rcases p with ⟨i,j⟩
            fin_cases i <;> fin_cases j <;> norm_num [winner, winningMatrix, s10, s20, s30, s40, s50, s21, s31, s41, s51, s32, s42, s52, s43, s53, s54, z0, z1, z2, z3, z4, z5, e01, e02, e03, e04, e05, e12, e13, e14, e15, e23, e24, e25, e34, e35, e45]
          ·
            have e25 : a (2,5) = 0 := by omega
            have e34 : a (3,4) = 0 := by omega
            have e35 : a (3,5) = 1 := by omega
            have e45 : a (4,5) = 0 := by omega
            intro hp
            norm_num [e01, e02, e03, e04, e05, e12, e13, e14, e15, e23, e24, e25, e34, e35, e45] at hp
        ·
          have e24 : a (2,4) = 0 := by omega
          have e25 : a (2,5) = 0 := by omega
          have e34 : a (3,4) = 0 := by omega
          have e35 : a (3,5) = 0 := by omega
          have e45 : a (4,5) = 1 := by omega
          intro hp
          norm_num [e01, e02, e03, e04, e05, e12, e13, e14, e15, e23, e24, e25, e34, e35, e45] at hp
    ·
      have e14 : a (1,4) = 0 := by omega
      have e15 : a (1,5) = 0 := by omega
      have e23 : a (2,3) = 0 := by omega
      have e24 : a (2,4) = 1 := by omega
      have e25 : a (2,5) = 0 := by omega
      have e34 : a (3,4) = 0 := by omega
      have e35 : a (3,5) = 0 := by omega
      have e45 : a (4,5) = 1 := by omega
      intro hp
      norm_num [e01, e02, e03, e04, e05, e12, e13, e14, e15, e23, e24, e25, e34, e35, e45] at hp
  ·
    have split : a (1,3) = 0 ∨ a (1,3) = 1 := by omega
    rcases split with e13 | e13
    ·
      have split : a (1,4) = 0 ∨ a (1,4) = 1 := by omega
      rcases split with e14 | e14
      ·
        have e15 : a (1,5) = 1 := by omega
        have e23 : a (2,3) = 0 := by omega
        have e24 : a (2,4) = 0 := by omega
        have e25 : a (2,5) = 0 := by omega
        have e34 : a (3,4) = 2 := by omega
        have e35 : a (3,5) = 0 := by omega
        have e45 : a (4,5) = 0 := by omega
        intro hp
        norm_num [e01, e02, e03, e04, e05, e12, e13, e14, e15, e23, e24, e25, e34, e35, e45] at hp
      ·
        have e15 : a (1,5) = 0 := by omega
        have e23 : a (2,3) = 0 := by omega
        have e24 : a (2,4) = 0 := by omega
        have e25 : a (2,5) = 0 := by omega
        have e34 : a (3,4) = 1 := by omega
        have e35 : a (3,5) = 1 := by omega
        have e45 : a (4,5) = 0 := by omega
        intro hp
        norm_num [e01, e02, e03, e04, e05, e12, e13, e14, e15, e23, e24, e25, e34, e35, e45] at hp
    ·
      have e14 : a (1,4) = 0 := by omega
      have e15 : a (1,5) = 0 := by omega
      have e23 : a (2,3) = 0 := by omega
      have e24 : a (2,4) = 0 := by omega
      have e25 : a (2,5) = 0 := by omega
      have e34 : a (3,4) = 1 := by omega
      have e35 : a (3,5) = 0 := by omega
      have e45 : a (4,5) = 1 := by omega
      intro hp
      norm_num [e01, e02, e03, e04, e05, e12, e13, e14, e15, e23, e24, e25, e34, e35, e45] at hp
end MacMahon

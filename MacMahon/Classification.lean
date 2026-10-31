module

public import MacMahon.ClassificationCases.Case0
public import MacMahon.ClassificationCases.Case1
public import MacMahon.ClassificationCases.Case2
public import MacMahon.ClassificationCases.Case3
public import MacMahon.ClassificationCases.Case4
public import MacMahon.ClassificationCases.Case5
public import MacMahon.ClassificationCases.Case6
public import MacMahon.ClassificationCases.Case7
public import MacMahon.ClassificationCases.Case8
public import MacMahon.ClassificationCases.Case9
public import MacMahon.ClassificationCases.Case10
public import MacMahon.ClassificationCases.Case11
public import MacMahon.ClassificationCases.Case12
public import MacMahon.ClassificationCases.Case13
public import MacMahon.ClassificationCases.Case14

@[expose] public section
namespace MacMahon
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- Exhaustive classification of all symmetric degree-two inventories. -/
lemma classify_degree_two (a : Inventory) (hz : DiagonalZero a)
    (hr : ∀ i, row a i = 2) (hs : ∀ i j, a (i,j) = a (j,i))
    (hp : ∀ b : Fin 10, 0 < ∑ p : Pair, winner b p * a p)
    : ∃ b : Fin 10, a = winner b := by
  have h0 := hr 0
  have z0 := hz 0
  norm_num [row, Fin.sum_univ_succ, z0] at h0
  have split : a (0,1) = 0 ∨ a (0,1) = 1 ∨ a (0,1) = 2 := by omega
  rcases split with e01 | e01 | e01
  ·
    have split : a (0,2) = 0 ∨ a (0,2) = 1 ∨ a (0,2) = 2 := by omega
    rcases split with e02 | e02 | e02
    ·
      have split : a (0,3) = 0 ∨ a (0,3) = 1 ∨ a (0,3) = 2 := by omega
      rcases split with e03 | e03 | e03
      ·
        have split : a (0,4) = 0 ∨ a (0,4) = 1 ∨ a (0,4) = 2 := by omega
        rcases split with e04 | e04 | e04
        ·
          have e05 : a (0,5) = 2 := by omega
          exact classify_row_0 a hz hr hs hp e01 e02 e03 e04 e05
        ·
          have e05 : a (0,5) = 1 := by omega
          exact classify_row_1 a hz hr hs hp e01 e02 e03 e04 e05
        ·
          have e05 : a (0,5) = 0 := by omega
          exact classify_row_2 a hz hr hs hp e01 e02 e03 e04 e05
      ·
        have split : a (0,4) = 0 ∨ a (0,4) = 1 := by omega
        rcases split with e04 | e04
        ·
          have e05 : a (0,5) = 1 := by omega
          exact classify_row_3 a hz hr hs hp e01 e02 e03 e04 e05
        ·
          have e05 : a (0,5) = 0 := by omega
          exact classify_row_4 a hz hr hs hp e01 e02 e03 e04 e05
      ·
        have e04 : a (0,4) = 0 := by omega
        have e05 : a (0,5) = 0 := by omega
        exact classify_row_5 a hz hr hs hp e01 e02 e03 e04 e05
    ·
      have split : a (0,3) = 0 ∨ a (0,3) = 1 := by omega
      rcases split with e03 | e03
      ·
        have split : a (0,4) = 0 ∨ a (0,4) = 1 := by omega
        rcases split with e04 | e04
        ·
          have e05 : a (0,5) = 1 := by omega
          exact classify_row_6 a hz hr hs hp e01 e02 e03 e04 e05
        ·
          have e05 : a (0,5) = 0 := by omega
          exact classify_row_7 a hz hr hs hp e01 e02 e03 e04 e05
      ·
        have e04 : a (0,4) = 0 := by omega
        have e05 : a (0,5) = 0 := by omega
        exact classify_row_8 a hz hr hs hp e01 e02 e03 e04 e05
    ·
      have e03 : a (0,3) = 0 := by omega
      have e04 : a (0,4) = 0 := by omega
      have e05 : a (0,5) = 0 := by omega
      exact classify_row_9 a hz hr hs hp e01 e02 e03 e04 e05
  ·
    have split : a (0,2) = 0 ∨ a (0,2) = 1 := by omega
    rcases split with e02 | e02
    ·
      have split : a (0,3) = 0 ∨ a (0,3) = 1 := by omega
      rcases split with e03 | e03
      ·
        have split : a (0,4) = 0 ∨ a (0,4) = 1 := by omega
        rcases split with e04 | e04
        ·
          have e05 : a (0,5) = 1 := by omega
          exact classify_row_10 a hz hr hs hp e01 e02 e03 e04 e05
        ·
          have e05 : a (0,5) = 0 := by omega
          exact classify_row_11 a hz hr hs hp e01 e02 e03 e04 e05
      ·
        have e04 : a (0,4) = 0 := by omega
        have e05 : a (0,5) = 0 := by omega
        exact classify_row_12 a hz hr hs hp e01 e02 e03 e04 e05
    ·
      have e03 : a (0,3) = 0 := by omega
      have e04 : a (0,4) = 0 := by omega
      have e05 : a (0,5) = 0 := by omega
      exact classify_row_13 a hz hr hs hp e01 e02 e03 e04 e05
  ·
    have e02 : a (0,2) = 0 := by omega
    have e03 : a (0,3) = 0 := by omega
    have e04 : a (0,4) = 0 := by omega
    have e05 : a (0,5) = 0 := by omega
    exact classify_row_14 a hz hr hs hp e01 e02 e03 e04 e05
end MacMahon

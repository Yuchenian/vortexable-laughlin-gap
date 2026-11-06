import VortexGap.Examples.RankTwoCells

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open VortexGap.Examples OAI.LaughlinGap.Occupation

private theorem even_commutes {R : Type*} [Ring R] (a b c : R)
    (ha : a*c = -(c*a)) (hb : b*c = -(c*b)) : Commute (a*b) c := by
  change (a*b)*c=c*(a*b)
  rw [mul_assoc, hb, mul_neg, ← mul_assoc, ha, neg_mul, neg_neg, mul_assoc]

private theorem slot_disjoint {k : ℕ} {i j : Fin k} (h : i ≠ j) (a b : Fin 2) :
    let p := cellPair _ (rankTwoSlot i a)
    let q := cellPair _ (rankTwoSlot j b)
    p.val.1 ≠ q.val.1 ∧ p.val.1 ≠ q.val.2 ∧ p.val.2 ≠ q.val.1 ∧ p.val.2 ≠ q.val.2 := by
  have hn : i.val ≠ j.val := fun he => h (Fin.ext he)
  dsimp [cellPair,rankTwoSlot]
  repeat' apply And.intro
  all_goals intro he; have hv := congrArg Fin.val he; dsimp at hv; omega

theorem rankTwoCell_pair_commute_adjoint {k : ℕ} {i j : Fin k} (h : i ≠ j) (a b : Fin 2) :
    Commute (pairMode (cellPair _ (rankTwoSlot i a))) (pairMode (cellPair _ (rankTwoSlot j b))).adjoint := by
  obtain ⟨h11,h12,h21,h22⟩ := slot_disjoint h a b
  rw [pairMode_adjoint,pairMode]
  exact (even_commutes _ _ _ (transition_anticommute_of_ne h21 false true)
    (transition_anticommute_of_ne h11 false true)).mul_right
    (even_commutes _ _ _ (transition_anticommute_of_ne h22 false true)
    (transition_anticommute_of_ne h12 false true))

private abbrev blockMode {k : ℕ} (i : Fin k) (a : Fin 2) := pairMode (cellPair _ (rankTwoSlot i a))

private theorem block_commute {k : ℕ} (i j : Fin k) (a b : Fin 2) :
    Commute (blockMode i a) (blockMode j b) :=
  (even_commutes _ _ _ (mode_anticommute ..) (mode_anticommute ..)).mul_right
    (even_commutes _ _ _ (mode_anticommute ..) (mode_anticommute ..))

private theorem cell_annihilate {k : ℕ} (i : Fin k) :
    pairAnnihilate (rankTwoCellPair i) = blockMode i 0 + blockMode i 1 := by
  rw [rankTwoCellPair_eq]
  change _ = pairMode _ + pairMode _
  rw [← pairAnnihilate_basis, ← pairAnnihilate_basis]
  simp [pairAnnihilate, add_smul, Finset.sum_add_distrib]

theorem rankTwoCell_cross_energy {k : ℕ} {i j : Fin k} (h : i ≠ j) (x : Space (2*(2*k))) :
    let A := pairAnnihilate (rankTwoCellPair i)
    let B := pairAnnihilate (rankTwoCellPair j)
    (inner ℂ (A.adjoint (A x)) (B.adjoint (B x))).re = ‖A (B x)‖^2 := by
  dsimp only
  let A := pairAnnihilate (rankTwoCellPair i)
  let B := pairAnnihilate (rankTwoCellPair j)
  have hab : Commute A B := by
    simp only [A,B,cell_annihilate]
    exact ((block_commute i j 0 0).add_right (block_commute i j 0 1)).add_left
      ((block_commute i j 1 0).add_right (block_commute i j 1 1))
  have had : Commute A B.adjoint := by
    simp only [A,B,cell_annihilate,map_add]
    exact ((rankTwoCell_pair_commute_adjoint h 0 0).add_right (rankTwoCell_pair_commute_adjoint h 0 1)).add_left
      ((rankTwoCell_pair_commute_adjoint h 1 0).add_right (rankTwoCell_pair_commute_adjoint h 1 1))
  change (inner ℂ (A.adjoint (A x)) (B.adjoint (B x))).re = _
  rw [LinearMap.adjoint_inner_left, show A (B.adjoint (B x)) = B.adjoint (A (B x)) from
    DFunLike.congr_fun had.eq (B x), LinearMap.adjoint_inner_right,
    show B (A x) = A (B x) from DFunLike.congr_fun hab.eq.symm x]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

end VortexGap.Fermion

import VortexGap.Examples.FinitePairs
import VortexGap.Frame.ModeFrames
import VortexGap.Transfer.SlaterTransfer
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open VortexGap.Frame VortexGap.Examples OAI.LaughlinGap.Occupation
open scoped InnerProduct ComplexConjugate ComplexOrder

/-- Twice the normalized one-cell Hamiltonian. -/
def fourModeRaw : Module.End ℂ (Space 4) :=
  (pairMode pair01 + pairMode pair23).adjoint * (pairMode pair01 + pairMode pair23)

theorem fourModeRaw_apply (x : Space 4) (A : Finset (Fin 4)) :
    fourModeRaw x A = if A = {0,1} ∨ A = {2,3} then x {0,1}+x {2,3}
      else if A.card = 3 then x A else if A.card = 4 then 2*x A else 0 := by
  rw [fourModeRaw, map_add, pairMode_adjoint, pairMode_adjoint]
  simp only [pairMode, Module.End.mul_apply, LinearMap.add_apply]
  fin_cases A <;>
    norm_num [fourModeRaw, map_add, pairMode_adjoint, pairMode, pair01, pair23,
      createMode, creation, annihilateMode, annihilation, Module.End.mul_apply, transition_apply,
      OAI.LaughlinGap.Occupation.flip, sign, Finset.filter_insert, Finset.filter_singleton,
      Finset.ext_iff, Fin.forall_fin_succ, Finset.filter, Finset.card, LinearMap.add_apply,
      PiLp.add_apply] <;> simp (config := { decide := true }) [Multiset.filter_singleton] <;> first | (apply congrArg₂ (·+·) <;> apply congrArg (fun B : Finset (Fin 4) => x B) <;> decide) | ring

theorem fourModeRaw_cubic : fourModeRaw^3 - (3:ℂ) • fourModeRaw^2 + (2:ℂ) • fourModeRaw = 0 := by
  apply LinearMap.ext
  intro x
  ext A
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.zero_apply,
    PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,PiLp.zero_apply,smul_eq_mul,pow_succ,
    pow_zero,one_mul,Module.End.mul_apply,fourModeRaw_apply]
  have h01 : ({0,1}:Finset (Fin 4)).card = 2 := by decide
  have h23 : ({2,3}:Finset (Fin 4)).card = 2 := by decide
  by_cases h : A={0,1} ∨ A={2,3}
  · rcases h with rfl | rfl <;> simp <;> ring
  · simp only [h, ite_false]
    split_ifs <;> ring

private theorem fourMode_defect_square :
    let D := fourModeRaw^2 - fourModeRaw
    D*D = (2:ℂ) • D := by
  dsimp only
  apply LinearMap.ext
  intro x
  ext A
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, PiLp.sub_apply, PiLp.smul_apply,
    smul_eq_mul, pow_two, Module.End.mul_apply, fourModeRaw_apply]
  by_cases h : A={0,1} ∨ A={2,3}
  · rcases h with rfl | rfl <;> simp <;> ring
  · simp only [h, ite_false]
    split_ifs <;> ring

theorem fourModeRaw_form (x : Space 4) :
    (inner ℂ x (fourModeRaw x)).re ≤ ‖fourModeRaw x‖^2 := by
  let T := fourModeRaw
  let D := T^2-T
  have ht : T.adjoint = T := by simp only [T, fourModeRaw, adjoint_mul, LinearMap.adjoint_adjoint]
  have hd : D.adjoint = D := by simp only [D,pow_two,map_sub,adjoint_mul,ht]
  have he : inner ℂ (D x) (D x) = 2 * inner ℂ x (D x) := by
    calc
      _ = inner ℂ x ((D*D) x) := by simpa only [hd,Module.End.mul_apply] using! LinearMap.adjoint_inner_left D (D x) x
      _ = _ := by rw [show D*D = (2:ℂ) • D from fourMode_defect_square, LinearMap.smul_apply, inner_smul_right]
  have hT : inner ℂ x ((T^2) x) = inner ℂ (T x) (T x) := by
    rw [pow_two, Module.End.mul_apply, ← LinearMap.adjoint_inner_left T, ht]
  have h := congrArg Complex.re he
  change (inner ℂ (D x) (D x)).re = (2*inner ℂ x ((T^2-T) x)).re at h
  have hh : inner ℂ x (D x) = inner ℂ (T x) (T x) - inner ℂ x (T x) := by
    change inner ℂ x ((T^2) x - T x) = _
    rw [inner_sub_right,hT]
  rw [hh] at h
  rw [two_mul,Complex.add_re,Complex.sub_re] at h
  simp only [← RCLike.re_eq_complex_re, ← norm_sq_eq_re_inner (𝕜 := ℂ)] at h
  change (inner ℂ x (T x)).re ≤ ‖T x‖^2
  change RCLike.re (inner ℂ x (T x)) ≤ _
  linarith [sq_nonneg ‖D x‖]

def fourModeFrames : Fin 2 → TwoFrame 4 := ![modeFrame pair01, modeFrame pair23]

/-- The normalization 1/2 is placed in the Hamiltonian weight. -/
def fourModePair : PairSpace 4 := slaterPair (fun _ => 1) fourModeFrames

theorem fourModePair_eq : fourModePair = pairBasis pair01 + pairBasis pair23 := by
  simp [fourModePair, slaterPair, Fin.sum_univ_two, fourModeFrames, modeFrame_wedge]

theorem fourModePair_norm_sq : ‖fourModePair‖^2 = 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), fourModePair_eq]
  simp only [inner_add_left,inner_add_right]
  norm_num [pairBasis,EuclideanSpace.inner_single_left,PiLp.single_apply,pair01,pair23]

theorem fourModeKernel : slaterKernel (fun _ => 1) (fun _ => 1) fourModeFrames fourModeFrames = 4 := by
  have h := modeFrameOverlap_zero pair01 pair23 (by decide) (by decide) (by decide) (by decide)
  have h' := modeFrameOverlap_zero pair23 pair01 (by decide) (by decide) (by decide) (by decide)
  norm_num [slaterKernel, Fin.sum_univ_two, fourModeFrames, h, h',twoFrameOverlap_self,traceNormTwo_zero,traceNormTwo_id]

theorem fourModeHamiltonian_eq :
    frameHamiltonian (fun _ : Unit => (1/2:ℝ)) (fun _ => fourModePair) = (1/2:ℂ) • fourModeRaw := by
  have ha : pairAnnihilate fourModePair = pairMode pair01 + pairMode pair23 := by
    rw [fourModePair_eq]
    have hadd (p q : PairSpace 4) : pairAnnihilate (p+q) = pairAnnihilate p + pairAnnihilate q := by
      simp [pairAnnihilate,add_smul,Finset.sum_add_distrib]
    rw [hadd,pairAnnihilate_pairBasis,pairAnnihilate_pairBasis]
  rw [frameHamiltonian,pairLift_frame]
  simp [ha,fourModeRaw]

theorem fourMode_reference (x : Space 4) :
    let H := frameHamiltonian (fun _ : Unit => (1/2:ℝ)) (fun _ => fourModePair)
    (1/2:ℝ)*(inner ℂ x (H x)).re ≤ ‖H x‖^2 := by
  dsimp only
  rw [fourModeHamiltonian_eq, LinearMap.smul_apply, inner_smul_right, norm_smul]
  have h := fourModeRaw_form x
  norm_num [Complex.mul_re, mul_pow]
  linarith

set_option maxHeartbeats 800000 in
theorem fourMode_rank_two_transfer
    (M : EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin 4)) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    {N : ℕ} {x : Space 4} (hx : InSector N x) :
    let H := filteredHamiltonian M (fun _ : Unit => (1/2:ℝ)) (fun _ => fourModePair)
    (1/2-2*‖1-M^2‖-‖1-M^2‖^2)*(inner ℂ x (H x)).re ≤ ‖H x‖^2 := by
  have hb (q : PairSpace 4) :
      (inner ℂ q (((1/2:ℂ) • pairRankOne fourModePair) q)).re ≤ 1*‖q‖^2 := by
    have h := sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) |>.mpr
      (norm_inner_le_norm (𝕜 := ℂ) fourModePair q)
    rw [mul_pow, fourModePair_norm_sq] at h
    change (inner ℂ q ((1/2:ℂ) • (inner ℂ fourModePair q • fourModePair))).re ≤ _
    rw [inner_smul_right, inner_smul_right, ← inner_conj_symm q fourModePair, Complex.mul_conj]
    norm_num [Complex.mul_re, Complex.sq_norm] at *
    linarith
  have ht := finite_slater_transfer M hM hc (fun _ : Unit => (1/2:ℝ))
    (fun _ _ => 1) (fun _ => fourModeFrames) (fun _ => by norm_num)
    (fun _ => 1) (fun _ => by norm_num) 2 (fun _ => by norm_num [fourModeKernel])
    1 (by norm_num) (fun q => by simpa [fourModePair] using! hb q)
    (1/2) (fun _ _ v _ => fourMode_reference v) hx
  simpa only [fourModePair, one_mul] using! ht

theorem fourMode_half_eigen :
    frameHamiltonian (fun _ : Unit => (1/2:ℝ)) (fun _ => fourModePair) (ket {0,1,2}) =
      (1/2:ℂ) • ket {0,1,2} := by
  rw [fourModeHamiltonian_eq,LinearMap.smul_apply]
  congr 1
  ext A
  rw [fourModeRaw_apply]
  fin_cases A <;> simp (config := {decide := true}) [ket, PiLp.single_apply]

theorem fourMode_complex_expansion :
    slaterPair ![(3/5:ℂ),4/5*Complex.I] fourModeFrames = mixedPair := by
  simp [slaterPair,fourModeFrames,Fin.sum_univ_two,modeFrame_wedge,mixedPair]

end VortexGap.Fermion

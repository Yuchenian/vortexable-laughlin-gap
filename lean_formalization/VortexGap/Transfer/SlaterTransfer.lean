import VortexGap.Frame.SlaterSynthesis
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open VortexGap.Frame
open scoped InnerProduct ComplexConjugate ComplexOrder

private theorem pairCreate_sum {n : ℕ} {α : Type*} [Fintype α] (p : α → PairSpace n) :
    pairCreate (∑ a, p a) = ∑ a, pairCreate (p a) := by
  let L : PairSpace n →ₗ[ℂ] Module.End ℂ (Space n) :=
    { toFun := pairCreate, map_add' := pairCreate_add, map_smul' := pairCreate_smul }
  exact map_sum L _ _

private theorem pairAnnihilate_sum {n : ℕ} {α : Type*} [Fintype α] (p : α → PairSpace n) :
    pairAnnihilate (∑ a, p a) = ∑ a, pairAnnihilate (p a) := by
  apply LinearMap.adjoint.injective
  simp only [map_sum, pairAnnihilate_adjoint, pairCreate_sum]

variable {n : ℕ} {α ι : Type*} [Fintype α] [Fintype ι]
variable (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)

private theorem slater_annihilate (c : α → ℂ) (U : α → TwoFrame n) (x : Space n) :
    pairAnnihilate (exteriorSquare (finiteLossEmbedding M hM hc).toLinearMap (slaterPair c U))
      ((fockSplit n n).symm (environmentVacuum n n x)) =
    (fockSplit n n).symm (environmentVacuum n n
      (pairAnnihilate (exteriorSquare M.toLinearMap (slaterPair c U)) x)) := by
  simp only [slaterPair, map_sum, map_smul, pairAnnihilate_sum, pairAnnihilate_smul,
    LinearMap.sum_apply, LinearMap.smul_apply, loss_pairAnnihilate_vacuum]

private theorem slater_create (c : α → ℂ) (U : α → TwoFrame n) (x : Space n) :
    fockSplit n n (pairCreate (exteriorSquare (finiteLossEmbedding M hM hc).toLinearMap (slaterPair c U))
      ((fockSplit n n).symm (environmentVacuum n n x))) =
    environmentVacuum n n (pairCreate (exteriorSquare M.toLinearMap (slaterPair c U)) x) +
    (∑ a, c a • oneLossCreation M (U a (PiLp.single 2 0 1)) (U a (PiLp.single 2 1 1))) x +
    twoLossCreation M (slaterPair c U) x := by
  simp only [slaterPair, map_sum, map_smul, pairCreate_sum, pairCreate_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, loss_pairCreate_vacuum, smul_add, Finset.sum_add_distrib, twoLossCreation]

variable (w : ι → ℝ) (c : ι → α → ℂ) (U : ι → α → TwoFrame n)

theorem slater_loss_vacuum (x : Space n) :
    let p := fun i => slaterPair (c i) (U i)
    fockSplit n n (lossHamiltonian M hM hc w p (lossVacuum n x)) =
      environmentVacuum n n (filteredHamiltonian M w p x) + slaterOneNoise M w c U x +
      twoLossNoise M w p x := by
  dsimp only
  simp only [lossVacuum_apply, lossHamiltonian, frameHamiltonian, pairLift_frame, LinearMap.sum_apply,
    LinearMap.smul_apply, pairAnnihilate_adjoint, Module.End.mul_apply, map_sum, map_smul,
    slater_annihilate, slater_create]
  simp only [filteredHamiltonian, frameHamiltonian, pairLift_frame, slaterOneNoise, twoLossNoise,
    LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, pairAnnihilate_adjoint,
    Module.End.mul_apply, map_sum, map_smul, smul_add, Finset.sum_add_distrib]

private theorem slater_noise_sector (x : Space n) :
    slaterOneNoise M w c U x ∈ environmentSector n n 1 := by
  simp only [slaterOneNoise, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro a _
  exact Submodule.smul_mem _ _ (oneLossCreation_sector M _ _ _)

private theorem frame_square_re {m : ℕ} (p : ι → PairSpace m) (y : Space m) :
    (inner ℂ y ((frameHamiltonian w p * frameHamiltonian w p) y)).re =
      ‖frameHamiltonian w p y‖^2 := by
  let H := frameHamiltonian w p
  have hh : H.adjoint = H := frameHamiltonian_adjoint _ _
  change (inner ℂ y (H (H y))).re = _
  rw [← LinearMap.adjoint_inner_left H, hh, ← RCLike.re_eq_complex_re, ← norm_sq_eq_re_inner (𝕜 := ℂ)]

include hM hc in
/-- Finite Slater-rank transfer with complex expansion coefficients and all cross-label overlaps. -/
theorem finite_slater_transfer {N : ℕ} (hw : ∀ i, 0 ≤ w i) (ω : ι → ℝ) (hω : ∀ i, 0 < ω i) (C : ℝ)
    (hrow : ∀ i, ∑ j, w j * slaterKernel (c i) (c j) (U i) (U j) * ω j ≤ C*ω i)
    (β : ℝ) (hβ : 0 ≤ β) (hQ : ∀ q : PairSpace n, (inner ℂ q
      ((∑ i, (w i:ℂ) • pairRankOne (slaterPair (c i) (U i))) q)).re ≤ β*‖q‖^2)
    (γ : ℝ) (hgap : ∀ K ≤ N, ∀ y : Space n, InSector K y →
      γ*(inner ℂ y (frameHamiltonian w (fun i => slaterPair (c i) (U i)) y)).re ≤
        ‖frameHamiltonian w (fun i => slaterPair (c i) (U i)) y‖^2)
    {x : Space n} (hx : InSector N x) :
    let H := filteredHamiltonian M w (fun i => slaterPair (c i) (U i))
    (γ-C*‖1-M^2‖-β*‖1-M^2‖^2)*(inner ℂ x (H x)).re ≤ ‖H x‖^2 := by
  let p := fun i => slaterPair (c i) (U i)
  let H := filteredHamiltonian M w p
  let L := lossHamiltonian M hM hc w p
  let y := lossVacuum n x
  let A := slaterOneNoise M w c U x
  let B := twoLossNoise M w p x
  have ha : A ∈ environmentSector n n 1 := slater_noise_sector M w c U x
  have hb : B ∈ environmentSector n n 2 := twoLossNoise_sector M w p x
  have h0a (z : Space n) : inner ℂ (environmentVacuum n n z) A = 0 :=
    environmentSector_orthogonal (environmentVacuum_environmentSector z) ha (by decide)
  have h0b (z : Space n) : inner ℂ (environmentVacuum n n z) B = 0 :=
    environmentSector_orthogonal (environmentVacuum_environmentSector z) hb (by decide)
  have hab : inner ℂ A B = 0 := environmentSector_orthogonal ha hb (by decide)
  have hout : fockSplit n n (L y) = environmentVacuum n n (H x) + A + B :=
    slater_loss_vacuum M hM hc w c U x
  have hfirst : inner ℂ y (L y) = inner ℂ x (H x) := by
    rw [← (fockSplit n n).inner_map_map, hout]
    change inner ℂ ((fockSplit n n) ((fockSplit n n).symm (environmentVacuum n n x))) _ = _
    simp only [(fockSplit n n).apply_symm_apply, inner_add_right, environmentVacuum_inner, h0a, h0b, add_zero]
  have hsecond : ‖L y‖^2 = ‖H x‖^2 + ‖A‖^2 + ‖B‖^2 := by
    have hz : inner ℂ (environmentVacuum n n (H x) + A) B = 0 := by rw [inner_add_left, h0b, hab, add_zero]
    simp only [pow_two]
    rw [← (fockSplit n n).norm_map (L y), hout,
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hz,
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ (h0a _)]
    rw [show ‖environmentVacuum n n (H x)‖ = ‖H x‖ from (environmentVacuumIsometry n n).norm_map _]
  have hr := lossHamiltonian_sector_inequality M hM hc w p γ
    (fun K hK v hv => (hgap K hK v hv).trans_eq (frame_square_re w p v).symm) (lossVacuum_sector hx)
  change γ*(inner ℂ y (L y)).re ≤ (inner ℂ y ((L*L) y)).re at hr
  have hsq : (inner ℂ y ((L*L) y)).re = ‖L y‖^2 := frame_square_re w _ y
  rw [hfirst, hsq, hsecond] at hr
  have h1 := slaterOneNoise_relative M w c U hM hc hw ω hω C hrow x
  have h2 := twoLossNoise_relative M hM hc w hw p β hβ hQ x
  change ‖A‖^2 ≤ C*‖1-M^2‖*(inner ℂ x (H x)).re at h1
  change ‖B‖^2 ≤ β*‖1-M^2‖^2*(inner ℂ x (H x)).re at h2
  change (γ-C*‖1-M^2‖-β*‖1-M^2‖^2)*(inner ℂ x (H x)).re ≤ ‖H x‖^2
  linarith only [hr,h1,h2]

end VortexGap.Fermion

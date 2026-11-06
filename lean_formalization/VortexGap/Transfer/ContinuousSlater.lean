import VortexGap.Frame.ContinuousSlaterNoise
import VortexGap.Transfer.SlaterTransfer
import VortexGap.Transfer.ContinuousFrame
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory VortexGap.Frame
open scoped InnerProduct ENNReal ComplexOrder
variable {n : ℕ} {X α : Type*} [MeasurableSpace X] [Fintype α]
  (μ : Measure X) (c : X → α → ℂ) (U : X → α → TwoFrame n)
  (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
  (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
  (hcL : ∀ a, MemLp (fun t => c t a) 2 μ)
  (hU : ∀ a (i : Fin 2), AEStronglyMeasurable (fun t => U t a (PiLp.single 2 i 1)) μ)

private abbrev firstAction (t : X) (x : Space n) :=
  (∑ a, c t a • oneLossCreation M (U t a (PiLp.single 2 0 1)) (U t a (PiLp.single 2 1 1)))
    (pairAnnihilate (exteriorSquare M.toLinearMap (slaterPair (c t) (U t))) x)

omit [MeasurableSpace X] in
private theorem slater_point_output (t : X) (x : Space n) :
    let p := slaterPair (c t) (U t)
    let q := exteriorSquare M.toLinearMap p
    let e := exteriorSquare (finiteLossEmbedding M hM hc).toLinearMap p
    fockSplit n n (pairCreate e (pairAnnihilate e (lossVacuum n x))) =
      environmentVacuum n n (pairCreate q (pairAnnihilate q x)) + firstAction c U M t x +
      twoLossCreation M p (pairAnnihilate q x) := by
  have h := slater_loss_vacuum M hM hc (fun _ : Unit => (1:ℝ)) (fun _ => c t) (fun _ => U t) x
  simpa only [lossHamiltonian,filteredHamiltonian,frameHamiltonian,pairLift_rankOne,slaterOneNoise,twoLossNoise,
    Fintype.sum_unique,Complex.ofReal_one,one_smul,Module.End.mul_apply,LinearMap.comp_apply,pairAnnihilate_adjoint,
    firstAction] using! h

include hcL hU in
theorem continuousSlaterOneOutput_sector (x : Space n) :
    continuousSlaterOneOutput μ c U M x ∈ environmentSector n n 1 := by
  apply environmentSector_integral μ _ (continuousSlaterOneAction_integrable μ c U M x hcL hU)
  apply Filter.Eventually.of_forall
  intro t
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  apply Submodule.sum_mem
  intro a _
  exact Submodule.smul_mem _ _ (oneLossCreation_sector M _ _ _)

include hcL hU in
theorem continuousSlater_loss_vacuum (x : Space n) :
    let p := fun t => slaterPair (c t) (U t)
    fockSplit n n (continuousLossHamiltonian M hM hc μ p (lossVacuum n x)) =
      environmentVacuum n n (continuousFrameHamiltonian μ (fun t => exteriorSquare M.toLinearMap (p t)) x) +
      continuousSlaterOneOutput μ c U M x + continuousTwoLossNoise M μ p x := by
  let p := fun t => slaterPair (c t) (U t)
  let q := fun t => exteriorSquare M.toLinearMap (p t)
  let e := fun t => exteriorSquare (finiteLossEmbedding M hM hc).toLinearMap (p t)
  let f := fun t => pairCreate (q t) (pairAnnihilate (q t) x)
  let f0 := fun t => environmentVacuum n n (f t)
  let f1 := fun t => firstAction c U M t x
  let f2 := fun t => twoLossCreation M (p t) (pairAnnihilate (q t) x)
  have hp := continuousSlaterPair_memLp μ c U hcL hU
  have he := exteriorPair_memLp μ p hp (finiteLossEmbedding M hM hc).toLinearMap
  have hq := filteredPair_memLp M μ p hp
  have hf : Integrable f μ := continuousFrameAction_integrable μ q hq x
  have h0 : Integrable f0 μ := (LinearMap.toContinuousLinearMap (environmentVacuum n n)).integrable_comp hf
  have h1 : Integrable f1 μ := continuousSlaterOneAction_integrable μ c U M x hcL hU
  have h2 : Integrable f2 μ := continuousTwoLossNoise_action_integrable M μ p hp x
  dsimp only
  rw [continuousLossHamiltonian,continuousFrameHamiltonian_apply μ _ he]
  have hsplit (g : X → Space (n+n)) : fockSplit n n (∫ t, g t ∂μ) = ∫ t, fockSplit n n (g t) ∂μ :=
    ((fockSplit n n).toLinearIsometry.integral_comp_comm g).symm
  rw [hsplit]
  change (∫ t, fockSplit n n (pairCreate (e t) (pairAnnihilate (e t) (lossVacuum n x))) ∂μ) = _
  simp_rw [show ∀ t, fockSplit n n (pairCreate (e t) (pairAnnihilate (e t) (lossVacuum n x))) =
    f0 t + f1 t + f2 t from fun t => slater_point_output c U M hM hc t x]
  have h01 : Integrable (fun t => f0 t + f1 t) μ := h0.add h1
  rw [integral_add h01 h2, integral_add h0 h1]
  have env : (∫ t, f0 t ∂μ) = environmentVacuum n n (∫ t, f t ∂μ) :=
    (LinearMap.toContinuousLinearMap (environmentVacuum n n)).integral_comp_comm hf
  rw [env, continuousFrameHamiltonian_apply μ _ hq,continuousTwoLossNoise_apply M μ p hp]
  rfl

include hcL hU hM hc in
theorem continuousSlater_transfer [SFinite μ] {N : ℕ}
    (ω : X → ℝ) (hω : ∀ a, 0 < ω a) (hωm : AEStronglyMeasurable ω μ)
    (C : ℝ)
    (hrowInt : ∀ᵐ a ∂μ, Integrable (fun b => slaterKernel (c a) (c b) (U a) (U b) * ω b) μ)
    (hrow : ∀ᵐ a ∂μ, (∫ b, slaterKernel (c a) (c b) (U a) (U b) * ω b ∂μ) ≤ C * ω a)
    (β : ℝ) (hβ : 0 ≤ β) (hQ : ∀ q : PairSpace n, (inner ℂ q
      (continuousPairOperator μ (fun t => slaterPair (c t) (U t)) q)).re ≤ β*‖q‖^2)
    (γ : ℝ) (hgap : ∀ K ≤ N, ∀ v : Space n, InSector K v →
      let T := continuousFrameHamiltonian μ (fun t => slaterPair (c t) (U t))
      γ*(inner ℂ v (T v)).re ≤ (inner ℂ v ((T*T) v)).re)
    {x : Space n} (hx : InSector N x) :
    let H := continuousFrameHamiltonian μ (fun t => exteriorSquare M.toLinearMap (slaterPair (c t) (U t)))
    (γ-C*‖1-M^2‖-β*‖1-M^2‖^2)*(inner ℂ x (H x)).re ≤ ‖H x‖^2 := by
  let p := fun t => slaterPair (c t) (U t)
  have hp : MemLp p 2 μ := continuousSlaterPair_memLp μ c U hcL hU
  let H := continuousFrameHamiltonian μ (fun t => exteriorSquare M.toLinearMap (p t))
  let L := continuousLossHamiltonian M hM hc μ p
  let y := lossVacuum n x
  let A := continuousSlaterOneOutput μ c U M x
  let B := continuousTwoLossNoise M μ p x
  have ha : A ∈ environmentSector n n 1 := continuousSlaterOneOutput_sector μ c U M hcL hU x
  have hb : B ∈ environmentSector n n 2 := continuousTwoLossNoise_sector M μ p hp x
  have h0a (z : Space n) : inner ℂ (environmentVacuum n n z) A = 0 :=
    environmentSector_orthogonal (environmentVacuum_environmentSector z) ha (by decide)
  have h0b (z : Space n) : inner ℂ (environmentVacuum n n z) B = 0 :=
    environmentSector_orthogonal (environmentVacuum_environmentSector z) hb (by decide)
  have hab : inner ℂ A B = 0 := environmentSector_orthogonal ha hb (by decide)
  have hout : fockSplit n n (L y) = environmentVacuum n n (H x) + A + B :=
    continuousSlater_loss_vacuum μ c U M hM hc hcL hU x
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
  have hr := continuousLossHamiltonian_sector_inequality M hM hc μ p hp γ hgap (lossVacuum_sector hx)
  change γ*(inner ℂ y (L y)).re ≤ (inner ℂ y (L (L y))).re at hr
  have hL : L.adjoint = L := continuousFrameHamiltonian_adjoint μ _
    (exteriorPair_memLp μ p hp (finiteLossEmbedding M hM hc).toLinearMap)
  have hsq : (inner ℂ y (L (L y))).re = ‖L y‖^2 := by
    rw [← ContinuousLinearMap.adjoint_inner_left L (L y) y,hL]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  rw [hfirst,hsq,hsecond] at hr
  have h1 := continuousSlaterOneOutput_relative μ c U M hM hc hcL hU ω hω hωm C hrowInt hrow x
  have h2 := continuousTwoLossNoise_relative M μ p hp β hβ hQ hM hc x
  change ‖A‖^2 ≤ C*‖1-M^2‖*(inner ℂ x (H x)).re at h1
  change ‖B‖^2 ≤ β*‖1-M^2‖^2*(inner ℂ x (H x)).re at h2
  change (γ-C*‖1-M^2‖-β*‖1-M^2‖^2)*(inner ℂ x (H x)).re ≤ ‖H x‖^2
  linarith only [hr,h1,h2]

end VortexGap.Fermion

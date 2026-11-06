import VortexGap.Fermion.CountableOrbitalCAR
import Mathlib.Analysis.Calculus.Deriv.Mul
import VortexGap.Frame.L2FiniteFiber
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

noncomputable section

namespace VortexGap.Fermion

/-- Distinct outgoing orbital components of a single incoming fermion field. -/
theorem orbitalColumn_contact (χ : ℝ → (CountableSpace →L[ℂ] CountableSpace))
    {D : CountableSpace →L[ℂ] CountableSpace} {r : ℝ} (hχ : HasDerivAt χ D r)
    {v : CountableOrbital} (hv : χ r = countableAnnihilate v)
    (a : ℂ) {b : ℝ → ℂ} {db : ℂ} (hb : HasDerivAt b db r) :
    (a • χ r) * deriv (fun s => b s • χ s) r =
      (a*b r) • (χ r * D) := by
  rw [(hb.fun_smul hχ).deriv, hv]
  simp only [mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
    countableAnnihilate_square]
  ext x A; simp [mul_comm]

/-- The complete orbital sum includes the off-diagonal channels. -/
theorem orbitalColumn_contact_energy {ι : Type*} [Fintype ι]
    (χ : ℝ → (CountableSpace →L[ℂ] CountableSpace))
    {D : CountableSpace →L[ℂ] CountableSpace} {r : ℝ} (hχ : HasDerivAt χ D r)
    {v : CountableOrbital} (hv : χ r = countableAnnihilate v)
    (t : ι → ℝ → ℂ) (ht : ∀ j, DifferentiableAt ℝ (t j) r) (x : CountableSpace) :
    (∑ i, ∑ j, ‖((t i r • χ r) * deriv (fun s => t j s • χ s) r) x‖^2) =
      (∑ i, ‖t i r‖^2)^2 * ‖(χ r * D) x‖^2 := by
  simp_rw [orbitalColumn_contact χ hχ hv _ (ht _).hasDerivAt, smul_apply,
    norm_smul, norm_mul, mul_pow]
  simp [pow_two, Finset.sum_mul, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

end VortexGap.Fermion

namespace VortexGap.Fermion
open MeasureTheory Filter
variable {α ι : Type*} [MeasurableSpace α] [Fintype ι] {μ : Measure α}
local notation "V" => EuclideanSpace ℂ ι

private theorem columnMemLp (n : α → V) (hm : AEStronglyMeasurable n μ)
    (hn : ∀ᵐ z ∂μ, ‖n z‖ = 1) (u : Lp ℂ 2 μ) :
    MemLp (fun z => u z • n z) 2 μ := by
  apply (Lp.memLp u).norm.mono' ((Lp.memLp u).aestronglyMeasurable.smul hm)
  filter_upwards [hn] with z hz
  simp [norm_smul, hz]

private def columnMap (n : α → V) (hm : AEStronglyMeasurable n μ)
    (hn : ∀ᵐ z ∂μ, ‖n z‖ = 1) (u : Lp ℂ 2 μ) : Lp V 2 μ :=
  (columnMemLp n hm hn u).toLp _

private theorem columnMap_ae (n : α → V) (hm : AEStronglyMeasurable n μ)
    (hn : ∀ᵐ z ∂μ, ‖n z‖ = 1) (u : Lp ℂ 2 μ) :
    (columnMap n hm hn u : α → V) =ᵐ[μ] fun z => u z • n z :=
  (columnMemLp n hm hn u).coeFn_toLp

/-- A unit column acts isometrically on the scalar ambient L² before restriction to a band. -/
def orbitalColumnIsometry (n : α → V) (hm : AEStronglyMeasurable n μ)
    (hn : ∀ᵐ z ∂μ, ‖n z‖ = 1) : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp V 2 μ where
  toFun := columnMap n hm hn
  map_add' u v := by
    apply Lp.ext
    filter_upwards [columnMap_ae n hm hn (u+v), columnMap_ae n hm hn u,
      columnMap_ae n hm hn v, Lp.coeFn_add u v, Lp.coeFn_add (columnMap n hm hn u) (columnMap n hm hn v)]
      with z h huv hv hs ht
    simp only [h, ht, Pi.add_apply, huv, hv, hs, add_smul]
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [columnMap_ae n hm hn (c • u), columnMap_ae n hm hn u,
      Lp.coeFn_smul c u, Lp.coeFn_smul c (columnMap n hm hn u)] with z h hu hs ht
    simp only [h, RingHom.id_apply, ht, Pi.smul_apply, hu, hs, smul_eq_mul, mul_smul]
  norm_map' u := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [Frame.l2_norm_sq_integral, Frame.l2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [columnMap_ae n hm hn u, hn] with z hz hnorm
    simp [hz, norm_smul, hnorm]

theorem orbitalColumnIsometry_apply (n : α → V) (hm : AEStronglyMeasurable n μ)
    (hn : ∀ᵐ z ∂μ, ‖n z‖ = 1) (u : Lp ℂ 2 μ) :
    (orbitalColumnIsometry n hm hn u : α → V) =ᵐ[μ] fun z => u z • n z :=
  columnMap_ae n hm hn u

def orbitalTexture (θ k : ℝ) (z : ℂ) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 ![(Real.cos θ : ℂ), Complex.exp (Complex.I * ((k*z.re : ℝ) : ℂ)) * (Real.sin θ : ℂ)]

theorem orbitalTexture_norm (θ k : ℝ) (z : ℂ) : ‖orbitalTexture θ k z‖ = 1 := by
  have hs : ‖orbitalTexture θ k z‖^2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    simp only [orbitalTexture, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, norm_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Complex.norm_exp, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
      zero_mul, mul_zero, sub_zero, Real.exp_zero, one_mul]
    linarith [Real.sin_sq_add_cos_sq θ]
  nlinarith [norm_nonneg (orbitalTexture θ k z)]

theorem orbitalTexture_component_smooth (θ k : ℝ) (j : Fin 2) :
    Differentiable ℝ (fun z => orbitalTexture θ k z j) := by
  fin_cases j <;> simp [orbitalTexture] <;> fun_prop

theorem orbitalTexture_continuous (θ k : ℝ) : Continuous (orbitalTexture θ k) := by
  apply (PiLp.continuous_toLp 2 _).comp
  exact continuous_pi (fun i => (orbitalTexture_component_smooth θ k i).continuous)

theorem orbitalColumn_gram {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (T : E →L[ℂ] Lp ℂ 2 μ) (n : α → V) (hm : AEStronglyMeasurable n μ)
    (hn : ∀ᵐ z ∂μ, ‖n z‖ = 1) :
    let J := (orbitalColumnIsometry n hm hn).toContinuousLinearMap
    (J.comp T).adjoint.comp (J.comp T) = T.adjoint.comp T := by
  dsimp only
  let J := (orbitalColumnIsometry n hm hn).toContinuousLinearMap
  have hJ : J.adjoint.comp J = 1 :=
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self J).mp (orbitalColumnIsometry n hm hn).norm_map
  change (J.comp T).adjoint.comp (J.comp T) = _
  rw [ContinuousLinearMap.adjoint_comp]
  ext1 x
  change T.adjoint (J.adjoint (J (T x))) = _
  change T.adjoint ((J.adjoint.comp J) (T x)) = T.adjoint (T x)
  rw [hJ]
  rfl

end VortexGap.Fermion

namespace VortexGap.Fermion

/-- Scalar path with any differentiable unit orbital texture. Both amplitude
derivatives and texture derivatives disappear from the complete contact. -/
theorem texturedColumn_contact_energy {ι : Type*} [Fintype ι]
    (χ : ℝ → (CountableSpace →L[ℂ] CountableSpace))
    {D : CountableSpace →L[ℂ] CountableSpace} {r : ℝ} (hχ : HasDerivAt χ D r)
    {v : CountableOrbital} (hv : χ r = countableAnnihilate v)
    (f : ℝ → ℂ) (hf : DifferentiableAt ℝ f r) (n : ℝ → EuclideanSpace ℂ ι)
    (hn : ∀ i, DifferentiableAt ℝ (fun s => n s i) r) (hunit : ‖n r‖ = 1)
    (x : CountableSpace) :
    (∑ i, ∑ j, ‖(((f r * n r i) • χ r) *
        deriv (fun s => (f s * n s j) • χ s) r) x‖^2) =
      ‖f r‖^4 * ‖(χ r * D) x‖^2 := by
  rw [orbitalColumn_contact_energy χ hχ hv (fun j s => f s * n s j) (fun j => hf.mul (hn j))]
  simp_rw [norm_mul, mul_pow, ← Finset.mul_sum, ← EuclideanSpace.norm_sq_eq, hunit]
  ring

theorem orbitalTexture_contact_energy (θ k : ℝ) (p : ℝ → ℂ) {r : ℝ}
    (hp : DifferentiableAt ℝ p r) (χ : ℝ → (CountableSpace →L[ℂ] CountableSpace))
    {D : CountableSpace →L[ℂ] CountableSpace} (hχ : HasDerivAt χ D r)
    {v : CountableOrbital} (hv : χ r = countableAnnihilate v)
    (f : ℝ → ℂ) (hf : DifferentiableAt ℝ f r) (x : CountableSpace) :
    (∑ i, ∑ j, ‖(((f r * orbitalTexture θ k (p r) i) • χ r) *
        deriv (fun s => (f s * orbitalTexture θ k (p s) j) • χ s) r) x‖^2) =
      ‖f r‖^4 * ‖(χ r * D) x‖^2 :=
  texturedColumn_contact_energy χ hχ hv f hf (fun s => orbitalTexture θ k (p s))
    (fun i => (orbitalTexture_component_smooth θ k i (p r)).comp r hp)
    (orbitalTexture_norm θ k (p r)) x

end VortexGap.Fermion

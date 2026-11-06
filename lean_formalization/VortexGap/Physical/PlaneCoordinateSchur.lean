import VortexGap.Physical.PlaneProjectionKernel
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory Filter
open scoped Topology
local notation "H" => Lp ℂ 2 (volume : Measure ℂ)

private theorem schur_row_sq (K : ℂ → ℂ) (x : H) (hm : Continuous K)
    (hk : Integrable (fun w => ‖K w‖)) (hC : 0 < ∫ w, ‖K w‖)
    (h2 : Integrable (fun w => ‖K w‖ * ‖x w‖^2)) :
    Integrable (fun w => K w * x w) ∧
    ‖∫ w, K w * x w‖^2 ≤ (∫ w, ‖K w‖) * ∫ w, ‖K w‖ * ‖x w‖^2 := by
  let C := ∫ w, ‖K w‖
  let t := ∫ w, ‖K w‖ * ‖x w‖
  let E := ∫ w, ‖K w‖ * ‖x w‖^2
  have h₁ : Integrable (fun w => ‖K w‖ * ‖x w‖) := by
    apply (hk.add h2).mono' (hm.norm.aestronglyMeasurable.mul (Lp.aestronglyMeasurable x).norm)
    apply Eventually.of_forall
    intro w
    change ‖‖K w‖ * ‖x w‖‖ ≤ ‖K w‖ + ‖K w‖ * ‖x w‖^2
    rw [Real.norm_of_nonneg (by positivity)]
    nlinarith [mul_nonneg (norm_nonneg (K w)) (sq_nonneg (‖x w‖ - 1)), mul_nonneg (norm_nonneg (K w)) (norm_nonneg (x w))]
  constructor
  · apply h₁.mono' (hm.aestronglyMeasurable.mul (Lp.aestronglyMeasurable x))
    exact Eventually.of_forall fun w => (norm_mul _ _).le
  have hv : 0 ≤ E - (2*(t/C))*t + (t/C)^2*C := by
    change 0 ≤ (∫ w, ‖K w‖ * ‖x w‖^2) - (2*(t/C))*(∫ w, ‖K w‖*‖x w‖) +
      (t/C)^2 * ∫ w, ‖K w‖
    have hd : Integrable (fun w => ‖K w‖ * ‖x w‖^2 - (2*(t/C))*(‖K w‖*‖x w‖)) := h2.sub (h₁.const_mul _)
    rw [← integral_const_mul, ← integral_sub h2 (h₁.const_mul _), ← integral_const_mul,
      ← integral_add hd (hk.const_mul _)]
    apply integral_nonneg
    intro w
    change 0 ≤ ‖K w‖ * ‖x w‖^2 - _ + _
    nlinarith [mul_nonneg (norm_nonneg (K w)) (sq_nonneg (‖x w‖ - t/C))]
  have hc : 0 < C := hC
  have ht : ‖∫ w, K w * x w‖ ≤ t := by
    simpa only [norm_mul, t] using norm_integral_le_integral_norm (fun w => K w * x w)
  apply (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans
  change t^2 ≤ C * E
  have he : E - (2*(t/C))*t + (t/C)^2*C = (C*E-t^2)/C := by field_simp; ring
  rw [he] at hv
  have := (le_div_iff₀ hc).mp hv
  linarith

/-- Scalar integral Schur test on planar L2, with the row and column masses
kept explicit. No integrability of the input over the whole plane is needed. -/
theorem planeIntegralSchur (K : ℂ → ℂ → ℂ) (hm : Continuous (Function.uncurry K))
    (C : ℝ) (hC : 0 < C) (hr : ∀ z, (∫ w, ‖K z w‖) = C)
    (hc : ∀ w, (∫ z, ‖K z w‖) = C) (x : H) :
    MemLp (fun z => ∫ w, K z w * x w) 2 volume ∧
    (∀ᵐ z ∂volume, Integrable (fun w => K z w * x w)) ∧
    (∫ z, ‖∫ w, K z w * x w‖^2) ≤ C^2 * ∫ w, ‖x w‖^2 := by
  let d (p : ℂ × ℂ) := ‖K p.1 p.2‖ * ‖x p.2‖^2
  have hmD : AEStronglyMeasurable d (volume.prod volume) :=
    hm.norm.aestronglyMeasurable.mul ((Lp.aestronglyMeasurable x).comp_snd.norm.pow 2)
  have hiX := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable x)).mp (Lp.memLp x)
  have hcol (w : ℂ) : Integrable (fun z => ‖K z w‖) :=
    Integrable.of_integral_ne_zero ((hc w).trans_ne hC.ne')
  have hrow (z : ℂ) : Integrable (fun w => ‖K z w‖) :=
    Integrable.of_integral_ne_zero ((hr z).trans_ne hC.ne')
  have hDcol (w : ℂ) : (∫ z, d (z,w)) = C * ‖x w‖^2 := by
    dsimp [d]
    rw [integral_mul_const, hc]
  have hD : Integrable d (volume.prod volume) := by
    apply (integrable_prod_iff' hmD).mpr
    refine ⟨Eventually.of_forall (fun w => (hcol w).mul_const (‖x w‖^2)), ?_⟩
    apply (hiX.const_mul C).congr
    apply Eventually.of_forall
    intro w
    change C * ‖x w‖^2 = ∫ z, ‖d (z,w)‖
    rw [← hDcol]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => (Real.norm_of_nonneg (by dsimp [d]; positivity : 0 ≤ d (z,w))).symm
  have hY : AEStronglyMeasurable (fun z => ∫ w, K z w * x w) volume :=
    (hm.aestronglyMeasurable.mul (Lp.aestronglyMeasurable x).comp_snd).integral_prod_right'
  have hboth : ∀ᵐ z ∂volume, Integrable (fun w => K z w * x w) ∧ ‖∫ w, K z w * x w‖^2 ≤ C * ∫ w, d (z,w) := by
    filter_upwards [hD.prod_right_ae] with z hz
    have h := schur_row_sq (K z) x (hm.comp (continuous_const.prodMk continuous_id)) (hrow z)
      ((hr z).symm ▸ hC) hz
    rwa [hr z] at h
  have hbound := hboth.mono fun _ h => h.2
  have hiY : Integrable (fun z => ‖∫ w, K z w * x w‖^2) := by
    apply (hD.integral_prod_left.const_mul C).mono' (hY.norm.pow 2)
    filter_upwards [hbound] with z hz
    change ‖‖∫ w, K z w * x w‖^2‖ ≤ _
    rwa [Real.norm_of_nonneg (sq_nonneg _)]
  refine ⟨(memLp_two_iff_integrable_sq_norm hY).mpr hiY, hboth.mono (fun _ h => h.1), ?_⟩
  calc
    _ ≤ ∫ z, C * ∫ w, d (z,w) := integral_mono_ae hiY (hD.integral_prod_left.const_mul C) hbound
    _ = _ := by
      rw [integral_const_mul, ← integral_prod _ hD, integral_prod_symm _ hD]
      simp_rw [hDcol]
      rw [integral_const_mul]
      ring

private def coordK (ell : ℝ) (z w : ℂ) := (z-w) * planeProjectionKernel ell z w

private theorem coord_bound (ell : ℝ) (hell : 0 < ell) (x : H) :
    MemLp (fun z => ∫ w, coordK ell z w * x w) 2 volume ∧
    (∀ᵐ z ∂volume, Integrable (fun w => coordK ell z w * x w)) ∧
    (∫ z, ‖∫ w, coordK ell z w * x w‖^2) ≤ (2*Real.sqrt Real.pi*ell)^2 * ∫ w, ‖x w‖^2 :=
  planeIntegralSchur (coordK ell) (by
    unfold coordK planeProjectionKernel Function.uncurry
    exact (continuous_fst.sub continuous_snd).mul
      (((planeEvaluation_continuous ell).comp continuous_fst).inner
        ((planeEvaluation_continuous ell).comp continuous_snd)))
    (2*Real.sqrt Real.pi*ell) (by positivity)
    (fun z => (planeCoordinateKernel_schur ell hell z).1)
    (fun w => (planeCoordinateKernel_schur ell hell w).2) x

private def rawComm (ell : ℝ) (hell : 0 < ell) (x : H) : H :=
  (coord_bound ell hell x).1.toLp _

private theorem rawComm_coe (ell : ℝ) (hell : 0 < ell) (x : H) :
    rawComm ell hell x =ᵐ[volume] fun z => ∫ w, coordK ell z w * x w := MemLp.coeFn_toLp _

private def commLinear (ell : ℝ) (hell : 0 < ell) : H →ₗ[ℂ] H where
  toFun := rawComm ell hell
  map_add' x y := by
    apply Lp.ext
    filter_upwards [rawComm_coe ell hell (x+y), Lp.coeFn_add (rawComm ell hell x) (rawComm ell hell y),
      rawComm_coe ell hell x, rawComm_coe ell hell y, (coord_bound ell hell x).2.1,
      (coord_bound ell hell y).2.1] with z ht ha hx hy hix hiy
    simp only [ht, ha, Pi.add_apply, hx, hy, ← integral_add hix hiy]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add x y] with w hw
    simp only [hw, Pi.add_apply, mul_add]
  map_smul' c x := by
    apply Lp.ext
    filter_upwards [rawComm_coe ell hell (c • x), Lp.coeFn_smul c (rawComm ell hell x),
      rawComm_coe ell hell x] with z ht hc hx
    change rawComm ell hell (c • x) z = (c • rawComm ell hell x) z
    simp only [ht, hc, Pi.smul_apply, smul_eq_mul, hx, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul c x] with w hw
    simp only [hw, Pi.smul_apply, smul_eq_mul, mul_left_comm]

private theorem commLinear_bound (ell : ℝ) (hell : 0 < ell) (x : H) :
    ‖commLinear ell hell x‖ ≤ (2*Real.sqrt Real.pi*ell)*‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Frame.l2_norm_sq_integral volume x, Frame.l2_norm_sq_integral]
  apply le_trans (le_of_eq (integral_congr_ae ?_)) (coord_bound ell hell x).2.2
  filter_upwards [rawComm_coe ell hell x] with z hz
  change ‖rawComm ell hell x z‖^2 = _
  rw [hz]

def planeCoordinateCommutator (ell : ℝ) (hell : 0 < ell) : H →L[ℂ] H :=
  (commLinear ell hell).mkContinuous _ (commLinear_bound ell hell)

theorem planeCoordinateCommutator_norm (ell : ℝ) (hell : 0 < ell) :
    ‖planeCoordinateCommutator ell hell‖ ≤ 2*Real.sqrt Real.pi*ell :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (commLinear_bound ell hell)

theorem planeLLLProjection_coordinateGraph (ell : ℝ) (hell : 0 < ell) (x : planeCoordinateDomain) :
    (planeLLLProjection ell hell x, planeLLLProjection ell hell (planeCoordinateMul x) +
      planeCoordinateCommutator ell hell x) ∈ planeCoordinateGraph := by
  change ∀ᵐ z ∂volume, _ = z * planeLLLProjection ell hell x z
  filter_upwards [Lp.coeFn_add (planeLLLProjection ell hell (planeCoordinateMul x))
    (planeCoordinateCommutator ell hell x), rawComm_coe ell hell x,
    planeCoordinate_commutator_integral ell hell x] with z ha hc he
  rw [ha]
  change _ + rawComm ell hell x z = _
  rw [hc]
  change _ + (∫ w, (z-w)*planeProjectionKernel ell z w*x.val w) = _
  rw [← he]
  ring

theorem planeLLLProjection_preserves_domain (ell : ℝ) (hell : 0 < ell) (x : planeCoordinateDomain) :
    planeLLLProjection ell hell x ∈ planeCoordinateDomain :=
  ⟨_, planeLLLProjection_coordinateGraph ell hell x, rfl⟩

end VortexGap.Fermion

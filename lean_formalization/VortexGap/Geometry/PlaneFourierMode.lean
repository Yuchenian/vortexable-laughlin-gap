import VortexGap.Physical.PlaneProjectionKernel
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory Filter
open scoped InnerProduct ComplexConjugate BoundedContinuousFunction

private def phaseKernel (a z w : ℂ) := a * (z * conj w - z * conj z / 2 - w * conj w / 2)
private def densityScale (ell : ℝ) : ℂ := ((2*Real.pi*ell^2 : ℝ) : ℂ)⁻¹
private def inverseArea (ell : ℝ) : ℂ := ((2*ell^2 : ℝ) : ℂ)⁻¹

theorem planeProjectionKernel_gaussian (ell : ℝ) (hell : 0 < ell) (z w : ℂ) :
    planeProjectionKernel ell z w = ((2*Real.pi*ell^2 : ℝ) : ℂ)⁻¹ *
      Complex.exp (((2*ell^2 : ℝ) : ℂ)⁻¹ * (z * conj w - z * conj z / 2 - w * conj w / 2)) := by
  let Z := planeCoordinate ell z
  let W := planeCoordinate ell w
  have hn (v : ℂ) : ((‖v‖^2 : ℝ) : ℂ) = v * conj v := by
    rw [Complex.sq_norm, Complex.mul_conj]
  have hD : ((Real.sqrt (2*Real.pi*ell^2) : ℝ) : ℂ)^2 = ((2*Real.pi*ell^2 : ℝ) : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by positivity : 0 ≤ 2*Real.pi*ell^2)
  have hs : ((Real.sqrt 2 : ℝ) : ℂ)^2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  simp only [planeProjectionKernel, planeEvaluation, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, planeCoherent_inner, Complex.norm_conj, starRingEnd_self_apply,
    map_inv₀]

  change _ * (_ * ((Real.exp (-‖Z‖^2/2) : ℂ) * (Real.exp (-‖W‖^2/2) : ℂ) * Complex.exp (Z * conj W))) = _
  rw [← mul_assoc, ← sq, inv_pow, hD]
  congr 1
  simp only [Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat, hn,
    ← Complex.exp_add]
  apply congrArg Complex.exp
  have pair (u v : ℂ) : planeCoordinate ell u * conj (planeCoordinate ell v) =
      ((2*ell^2 : ℝ) : ℂ)⁻¹ * (u * conj v) := by
    simp only [planeCoordinate, map_div₀, map_mul, Complex.conj_ofReal, div_mul_div_comm,
      ← sq, Complex.ofReal_mul, mul_pow, hs, Complex.ofReal_ofNat, Complex.ofReal_pow]
    ring
  simp only [Z, W, pair]
  ring
theorem planeProjectionKernel_reproduces (ell : ℝ) (hell : 0 < ell) (z w : ℂ) :
    (∫ u, planeProjectionKernel ell z u * planeProjectionKernel ell u w) =
      planeProjectionKernel ell z w := by
  rw [planeProjectionKernel, ← planeLLLEmbedding_inner ell hell, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [planeLLLEmbedding_coe ell hell (planeEvaluation ell z),
    planeLLLEmbedding_coe ell hell (planeEvaluation ell w)] with u hz hw
  rw [hz, hw, RCLike.inner_apply', inner_conj_symm]
  rfl

private def modeExp (ell : ℝ) (d u : ℂ) :=
  inverseArea ell * (d * conj u - u * conj d)

private theorem modeExp_re (ell : ℝ) (d u : ℂ) : (modeExp ell d u).re = 0 := by
  unfold modeExp inverseArea
  rw [← Complex.ofReal_inv]
  simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im]
  ring

/-- The plane wave indexed by its guiding-center displacement. -/
def planeDisplacementPhase (ell : ℝ) (d : ℂ) : ℂ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun u => Complex.exp (modeExp ell d u))
    (by unfold modeExp; fun_prop) 1 (fun u => by rw [Complex.norm_exp, modeExp_re, Real.exp_zero])

def planeDisplacementFactor (ell : ℝ) (d w : ℂ) :=
  Complex.exp (inverseArea ell * (d * conj w - w * conj d - d * conj d) / 2)

private theorem shifted_kernel_integral (ell : ℝ) (hell : 0 < ell) (d z w : ℂ) :
    (∫ u, planeProjectionKernel ell z u * (planeDisplacementPhase ell d u * planeProjectionKernel ell u w)) =
      planeDisplacementFactor ell d w * planeProjectionKernel ell z (w-d) := by
  let a := inverseArea ell
  let b := a * ((z+d)*conj (z+d) + (w-d)*conj (w-d) - z*conj z - w*conj w)/2
  have hshift (u : ℂ) : planeProjectionKernel ell z u * (planeDisplacementPhase ell d u * planeProjectionKernel ell u w) =
      Complex.exp b * (planeProjectionKernel ell (z+d) u * planeProjectionKernel ell u (w-d)) := by
    have he : phaseKernel a z u + (modeExp ell d u + phaseKernel a u w) =
        b + (phaseKernel a (z+d) u + phaseKernel a u (w-d)) := by
      simp only [phaseKernel,modeExp,b,a,map_add,map_sub]
      ring
    simp only [planeProjectionKernel_gaussian ell hell]
    change densityScale ell * Complex.exp (phaseKernel a z u) *
      (Complex.exp (modeExp ell d u) * (densityScale ell * Complex.exp (phaseKernel a u w))) = _
    change _ = Complex.exp b * ((densityScale ell * Complex.exp (phaseKernel a (z+d) u)) *
      (densityScale ell * Complex.exp (phaseKernel a u (w-d))))
    have h := congrArg Complex.exp he
    simp only [Complex.exp_add] at h
    linear_combination (densityScale ell)^2 * h
  simp_rw [hshift]
  rw [integral_const_mul, planeProjectionKernel_reproduces ell hell]
  have he : b + phaseKernel a (z+d) (w-d) =
      a * (d * conj w - w * conj d - d * conj d)/2 + phaseKernel a z (w-d) := by
    simp only [b, phaseKernel, map_add, map_sub]
    ring
  simp only [planeProjectionKernel_gaussian ell hell, planeDisplacementFactor]
  change Complex.exp b * (densityScale ell * Complex.exp (phaseKernel a (z+d) (w-d))) =
    Complex.exp _ * (densityScale ell * Complex.exp (phaseKernel a z (w-d)))
  have hh := congrArg Complex.exp he
  simp only [Complex.exp_add] at hh
  linear_combination densityScale ell * hh

def planeDisplacementCompression (ell : ℝ) (hell : 0 < ell) (d : ℂ) :
    CountableOrbital →L[ℂ] CountableOrbital :=
  (planeLLLEmbedding ell hell).toContinuousLinearMap.adjoint.comp
    (planeScalarEmbedding ell hell (planeDisplacementPhase ell d))

theorem planeDisplacementCompression_evaluation (ell : ℝ) (hell : 0 < ell) (d w : ℂ) :
    planeDisplacementCompression ell hell d (planeEvaluation ell w) =
      planeDisplacementFactor ell d w • planeEvaluation ell (w-d) := by
  apply (planeLLLEmbedding ell hell).injective
  apply Lp.ext
  let F := planeScalarEmbedding ell hell (planeDisplacementPhase ell d)
  filter_upwards [planeLLLProjection_integral ell hell (F (planeEvaluation ell w)),
    planeLLLEmbedding_coe ell hell (planeDisplacementFactor ell d w • planeEvaluation ell (w-d))] with z hz hR
  change planeLLLProjection ell hell (F (planeEvaluation ell w)) z = _
  rw [hz,hR,inner_smul_right]
  change _ = planeDisplacementFactor ell d w * planeProjectionKernel ell z (w-d)
  rw [← shifted_kernel_integral ell hell d z w]
  apply integral_congr_ae
  filter_upwards [planeScalarEmbedding_coe ell hell (planeDisplacementPhase ell d) (planeEvaluation ell w)] with u hu
  change _ * planeScalarEmbedding ell hell (planeDisplacementPhase ell d) (planeEvaluation ell w) u = _
  rw [hu]
  rfl

private theorem evaluation_ext (ell : ℝ) (hell : 0 < ell)
    (A B : CountableOrbital →L[ℂ] CountableOrbital)
    (h : ∀ w, A (planeEvaluation ell w) = B (planeEvaluation ell w)) : A = B := by
  have had : A.adjoint = B.adjoint := by
    ext1 x
    apply (planeLLLEmbedding ell hell).injective
    apply Lp.ext
    filter_upwards [planeLLLEmbedding_coe ell hell (A.adjoint x),
      planeLLLEmbedding_coe ell hell (B.adjoint x)] with z ha hb
    rw [ha,hb,ContinuousLinearMap.adjoint_inner_right,ContinuousLinearMap.adjoint_inner_right,h]
  simpa only [ContinuousLinearMap.adjoint_adjoint] using
    congrArg (fun L : CountableOrbital →L[ℂ] CountableOrbital => L.adjoint) had

private theorem phase_neg (ell : ℝ) (d u : ℂ) :
    planeDisplacementPhase ell (-d) u = conj (planeDisplacementPhase ell d u) := by
  change Complex.exp _ = conj (Complex.exp _)
  rw [← Complex.exp_conj]
  congr 1
  simp only [modeExp, inverseArea, map_inv₀, map_mul, map_sub, map_neg, starRingEnd_self_apply,
    Complex.conj_ofReal]
  ring

theorem planeDisplacementCompression_adjoint (ell : ℝ) (hell : 0 < ell) (d : ℂ) :
    (planeDisplacementCompression ell hell d).adjoint = planeDisplacementCompression ell hell (-d) := by
  ext1 x
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  let J := (planeLLLEmbedding ell hell).toContinuousLinearMap
  let F := fun a => planeScalarEmbedding ell hell (planeDisplacementPhase ell a)
  change inner ℂ (J.adjoint (F d y)) x = inner ℂ y (J.adjoint (F (-d) x))
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right,
    MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [planeScalarEmbedding_is_multiplication ell hell (planeDisplacementPhase ell d) y,
    planeScalarEmbedding_is_multiplication ell hell (planeDisplacementPhase ell (-d)) x] with z hy hx
  change inner ℂ (planeScalarEmbedding ell hell _ y z) (planeLLLEmbedding ell hell x z) =
    inner ℂ (planeLLLEmbedding ell hell y z) (planeScalarEmbedding ell hell _ x z)
  rw [hy,hx,phase_neg]
  simp only [RCLike.inner_apply', map_mul]
  ring

private def gain (ell : ℝ) (d : ℂ) : ℝ := Real.exp (-‖d‖^2/(4*ell^2))

private theorem factor_cancel (ell : ℝ) (d w : ℂ) :
    planeDisplacementFactor ell d w * planeDisplacementFactor ell (-d) (w-d) = ((gain ell d : ℂ))^2 := by
  rw [sq ((gain ell d : ℂ))]
  simp only [planeDisplacementFactor,gain,Complex.ofReal_exp, ← Complex.exp_add]
  apply congrArg Complex.exp
  simp only [map_neg,map_sub, Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_mul,
    Complex.ofReal_pow,Complex.ofReal_ofNat, inverseArea]
  have hd : ((‖d‖ : ℂ))^2 = d * conj d := by
    rw [← Complex.ofReal_pow, Complex.sq_norm, Complex.mul_conj]
  rw [hd]
  by_cases he : ell = 0
  · simp [he]
  · have h : (ell : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr he
    field_simp
    ring

private def shifted (ell : ℝ) (hell : 0 < ell) (d : ℂ) :=
  ((gain ell d : ℂ))⁻¹ • planeDisplacementCompression ell hell d

private theorem shifted_inverse (ell : ℝ) (hell : 0 < ell) (d : ℂ) :
    (shifted ell hell (-d)).comp (shifted ell hell d) = 1 := by
  apply evaluation_ext ell hell
  intro w
  have hc := factor_cancel ell d w
  have hn : ((gain ell d : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  have hg : gain ell (-d) = gain ell d := by simp [gain]
  simp only [ContinuousLinearMap.comp_apply, shifted, smul_apply, map_smul,
    planeDisplacementCompression_evaluation, smul_smul, hg, sub_neg_eq_add, sub_add_cancel]
  change _ • planeEvaluation ell w = planeEvaluation ell w
  conv_rhs => rw [← one_smul ℂ (planeEvaluation ell w)]
  congr 1
  field_simp
  linear_combination hc

private theorem shifted_adjoint (ell : ℝ) (hell : 0 < ell) (d : ℂ) :
    (shifted ell hell d).adjoint = shifted ell hell (-d) := by
  simp only [shifted, map_smulₛₗ, map_inv₀, Complex.conj_ofReal, planeDisplacementCompression_adjoint,
    gain, norm_neg]

/-- Guiding-center translation as a surjective linear isometry. -/
def planeGuidingDisplacement (ell : ℝ) (hell : 0 < ell) (d : ℂ) :
    CountableOrbital ≃ₗᵢ[ℂ] CountableOrbital := by
  let U := shifted ell hell d
  have h := shifted_inverse ell hell d
  rw [← shifted_adjoint] at h
  let J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital :=
    ⟨U.toLinearMap,(ContinuousLinearMap.norm_map_iff_adjoint_comp_self U).mpr h⟩
  apply LinearIsometryEquiv.ofSurjective J
  intro x
  refine ⟨shifted ell hell (-d) x, ?_⟩
  have hi := shifted_inverse ell hell (-d)
  rw [neg_neg] at hi
  exact congrArg (fun L : CountableOrbital →L[ℂ] CountableOrbital => L x) hi

/-- Position-space plane wave with wave vector (q.re,q.im). -/
def planeFourierPhase (q : ℂ) : ℂ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun z => Complex.exp (Complex.I * ((q.re*z.re + q.im*z.im : ℝ) : ℂ)))
    (by fun_prop) 1 (fun z => by simp [Complex.norm_exp])

def planeGuidingTranslation (ell : ℝ) (hell : 0 < ell) (q : ℂ) :
    CountableOrbital ≃ₗᵢ[ℂ] CountableOrbital :=
  planeGuidingDisplacement ell hell (Complex.I * (ell : ℂ)^2 * q)

private theorem physical_phase (ell : ℝ) (hell : 0 < ell) (q : ℂ) :
    planeDisplacementPhase ell (Complex.I * (ell : ℂ)^2 * q) = planeFourierPhase q := by
  ext1 z
  change Complex.exp _ = Complex.exp _
  apply congrArg Complex.exp
  unfold modeExp inverseArea
  have hl : (ell : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hell.ne'
  simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat,
    map_mul, map_pow, Complex.conj_ofReal, Complex.conj_I]
  field_simp
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

private theorem physical_gain (ell : ℝ) (hell : 0 < ell) (q : ℂ) :
    gain ell (Complex.I*(ell : ℂ)^2*q) = Real.exp (-‖q‖^2*ell^2/4) := by
  unfold gain
  simp only [norm_mul,Complex.norm_I,one_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hell]
  congr 1
  field_simp

/-- Actual LLL compression of a Fourier multiplier, including its unitary
guiding-center translation and the physical length in the Gaussian factor. -/
theorem planeFourier_compression (ell : ℝ) (hell : 0 < ell) (q : ℂ) :
    (planeLLLEmbedding ell hell).toContinuousLinearMap.adjoint.comp
      (planeScalarEmbedding ell hell (planeFourierPhase q)) =
    ((Real.exp (-‖q‖^2*ell^2/4) : ℝ) : ℂ) •
      (planeGuidingTranslation ell hell q).toLinearIsometry.toContinuousLinearMap := by
  let d := Complex.I*(ell : ℂ)^2*q
  rw [← physical_phase ell hell q, ← physical_gain ell hell q]
  change planeDisplacementCompression ell hell d = (gain ell d : ℂ) • shifted ell hell d
  have h : (gain ell d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  rw [shifted, smul_smul, mul_inv_cancel₀ h, one_smul]

end VortexGap.Fermion

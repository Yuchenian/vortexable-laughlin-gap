import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

noncomputable section

open scoped BoundedContinuousFunction
namespace VortexGap.Fermion
open MeasureTheory MeasureTheory.Measure Filter Topology

def periodicShear (a k : ℝ) (z : ℂ) : ℂ :=
  ⟨z.re + a/k * Real.sin (k*z.im), z.im⟩

theorem periodicShear_inverse (a k : ℝ) (z : ℂ) :
    periodicShear (-a) k (periodicShear a k z) = z := by
  apply Complex.ext <;> simp [periodicShear] <;> ring

/-- Each horizontal slice is translated by a constant depending only on height. -/
theorem periodicShear_preserves_area (a k : ℝ) : MeasurePreserving (periodicShear a k) := by
  let g := fun y x : ℝ => x + a/k * Real.sin (k*y)
  have hs := (MeasurePreserving.id (volume : Measure ℝ)).skew_product (g := g)
    (show Measurable (Function.uncurry g) by unfold Function.uncurry g; fun_prop)
    (ae_of_all volume (fun y => (measurePreserving_add_right (volume : Measure ℝ) (a/k * Real.sin (k*y))).map_eq))
  have sw : MeasurePreserving (@Prod.swap ℝ ℝ) volume volume := measurePreserving_swap
  have hc := Complex.volume_preserving_equiv_real_prod
  exact (hc.symm _).comp (sw.comp (hs.comp (sw.comp hc)))

def periodicShearEquiv (a k : ℝ) : ℂ ≃ᵐ ℂ where
  toFun := periodicShear a k
  invFun := periodicShear (-a) k
  left_inv := periodicShear_inverse a k
  right_inv z := by simpa using periodicShear_inverse (-a) k z
  measurable_toFun := (periodicShear_preserves_area a k).measurable
  measurable_invFun := (periodicShear_preserves_area (-a) k).measurable

local notation "H" => Lp ℂ 2 (volume : Measure ℂ)

private theorem pullback_cancel (a k : ℝ) (u : H) :
    Lp.compMeasurePreserving _ (periodicShear_preserves_area a k)
      (Lp.compMeasurePreserving _ (periodicShear_preserves_area (-a) k) u) = u := by
  rw [← Lp.compMeasurePreserving_comp_apply]
  have he : periodicShear (-a) k ∘ periodicShear a k = id := funext (periodicShear_inverse a k)
  simp [he]

/-- Unitary pullback on the ambient plane with Lebesgue measure. -/
def periodicShearUnitary (a k : ℝ) : H ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofSurjective
    (Lp.compMeasurePreservingₗᵢ ℂ _ (periodicShear_preserves_area a k))
    (fun u => ⟨Lp.compMeasurePreserving _ (periodicShear_preserves_area (-a) k) u,
      pullback_cancel a k u⟩)

theorem periodicShearUnitary_apply (a k : ℝ) (u : H) :
    (periodicShearUnitary a k u : ℂ → ℂ) =ᵐ[volume] u ∘ periodicShear a k :=
  Lp.coeFn_compMeasurePreserving _ _

theorem periodicShear_horizontal (a k : ℝ) (z : ℂ) :
    HasDerivAt (fun t : ℝ => periodicShear a k (z + (t : ℂ))) 1 0 := by
  have he : (fun t : ℝ => periodicShear a k (z + (t : ℂ))) =
      (fun t : ℝ => periodicShear a k z + (t : ℂ)) := by
    funext t; apply Complex.ext <;> simp [periodicShear] <;> ring
  rw [he]
  simpa using (Complex.ofRealCLM.hasDerivAt (x := (0:ℝ))).const_add (periodicShear a k z)

theorem periodicShear_vertical (a k : ℝ) (hk : k ≠ 0) (z : ℂ) :
    HasDerivAt (fun t : ℝ => periodicShear a k (z + (t:ℂ)*Complex.I))
      ((a*Real.cos (k*z.im) : ℝ) + Complex.I : ℂ) 0 := by
  have he : (fun t : ℝ => periodicShear a k (z + (t:ℂ)*Complex.I)) =
      (fun t : ℝ => z + (((a/k)*Real.sin (k*(z.im+t)) : ℝ) : ℂ) + (t:ℂ)*Complex.I) := by
    funext t; apply Complex.ext <;> simp only [periodicShear, Complex.add_re, Complex.add_im, Complex.mul_I_re, Complex.mul_I_im, Complex.ofReal_re, Complex.ofReal_im, neg_zero, add_zero]
  rw [he]
  have h := (((hasDerivAt_id (0:ℝ)).const_add z.im).const_mul k).sin.const_mul (a/k)

  have ht := (Complex.ofRealCLM.hasDerivAt (x := (a/k * Real.sin (k*(z.im+0))))).scomp (0:ℝ) h
  apply ((ht.const_add z).add ((Complex.ofRealCLM.hasDerivAt (x := (0:ℝ))).mul_const Complex.I)).congr_deriv
  simp only [id_eq, add_zero, mul_one, Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul, Algebra.smul_def]
  congr 2
  field_simp
  rfl

def periodicShearWeight (a k : ℝ) (z : ℂ) : ℝ := 1 + a^2/2 * Real.cos (k*z.im)^2

theorem periodicShear_contact_weight (a k : ℝ) (z : ℂ) :
    (‖(1:ℂ)‖^2 + ‖((a*Real.cos (k*z.im) : ℝ) : ℂ) + Complex.I‖^2)/2 =
      periodicShearWeight a k z := by
  rw [norm_one, one_pow, Complex.sq_norm]
  simp only [periodicShearWeight, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, add_zero, zero_add]
  ring

theorem periodicShearWeight_bounds (a k : ℝ) (z : ℂ) :
    1 ≤ periodicShearWeight a k z ∧ periodicShearWeight a k z ≤ 1+a^2/2 := by
  unfold periodicShearWeight
  constructor
  · exact le_add_of_nonneg_right (by positivity)
  · have h := Real.cos_sq_le_one (k*z.im)
    nlinarith [mul_nonneg (sq_nonneg a) (sub_nonneg.mpr h)]

/-- Graph-level conjugacy on the full multiplication domains, in Lebesgue L². -/
theorem periodicShear_coordinate_graph (a k : ℝ) (u v : H) :
    (∀ᵐ z ∂volume, periodicShearUnitary a k v z =
        periodicShear a k z * periodicShearUnitary a k u z) ↔
      ∀ᵐ z ∂volume, v z = z * u z := by
  let F := periodicShearEquiv a k
  have hF : MeasurePreserving F := periodicShear_preserves_area a k
  have h := F.measurableEmbedding.ae_map_iff (μ := (volume : Measure ℂ))
      (p := fun z => v z = z * u z)
  rw [hF.map_eq] at h
  rw [h]
  apply Filter.eventually_congr
  filter_upwards [periodicShearUnitary_apply a k u, periodicShearUnitary_apply a k v]
    with z hu hv
  change (_ = _ ↔ v (periodicShear a k z) = periodicShear a k z * u (periodicShear a k z))
  rw [hu, hv]; rfl

theorem periodicShear_maximal_domain (a k : ℝ) (u : H) :
    (∃ w : H, ∀ᵐ z ∂volume, w z = periodicShear a k z * periodicShearUnitary a k u z) ↔
      ∃ v : H, ∀ᵐ z ∂volume, v z = z * u z := by
  constructor
  · rintro ⟨w,hw⟩
    obtain ⟨v,rfl⟩ := (periodicShearUnitary a k).surjective w
    exact ⟨v,(periodicShear_coordinate_graph a k u v).mp hw⟩
  · rintro ⟨v,hv⟩
    exact ⟨_,(periodicShear_coordinate_graph a k u v).mpr hv⟩

/-- Where the shear varies with height the transformed vortex coordinate violates
the Cauchy-Riemann relation. -/
theorem periodicShear_not_complex_differentiable (a k : ℝ) (hk : k ≠ 0) (z : ℂ)
    (h : a * Real.cos (k*z.im) ≠ 0) : ¬ DifferentiableAt ℂ (periodicShear a k) z := by
  intro hd
  have chain (c : ℂ) : HasDerivAt (fun t : ℝ => periodicShear a k (z + (t:ℂ)*c))
      (c * deriv (periodicShear a k) z) 0 := by
    have hd' : DifferentiableAt ℂ (periodicShear a k) (z + ((0:ℝ):ℂ)*c) := by simpa using hd
    have drv := (hd'.hasDerivAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt (0:ℝ)
      (show HasDerivAt (fun t : ℝ => z + (t:ℂ)*c) c 0 by
        simpa using (Complex.ofRealCLM.hasDerivAt.mul_const c).const_add z)
    simpa [Function.comp_def] using! drv
  have hx := chain 1
  have hy := chain Complex.I
  simp only [one_mul, mul_one] at hx
  have h1 := hx.unique (periodicShear_horizontal a k z)
  have h2 := hy.unique (periodicShear_vertical a k hk z)
  rw [h1, mul_one] at h2
  exact h (by simpa only [Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero] using congrArg Complex.re h2.symm)

/-- Physical magnetic unit-cell translations act on the pulled-back coordinates. -/
theorem periodicShear_lattice (a k L : ℝ) (hperiod : k*L=2*Real.pi) (m n : ℤ) (z : ℂ) :
    periodicShear a k (z + (⟨m*L,n*L⟩ : ℂ)) =
      periodicShear a k z + (⟨m*L,n*L⟩ : ℂ) := by
  have he : k*(z.im+n*L) = k*z.im + n*(2*Real.pi) := by rw [← hperiod]; ring
  apply Complex.ext <;> simp only [periodicShear, Complex.add_re, Complex.add_im, he,
    Real.sin_add_int_mul_two_pi] <;> ring

def periodicShearGauge (B a k y : ℝ) : ℝ := -(B*a/k^2)*Real.cos (k*y)

theorem periodicShearGauge_periodic (B a k L y : ℝ) (hperiod : k*L=2*Real.pi) (n : ℤ) :
    periodicShearGauge B a k (y+n*L) = periodicShearGauge B a k y := by
  have he : k*(y+n*L)=k*y+n*(2*Real.pi) := by rw [← hperiod]; ring
  simp [periodicShearGauge,he,Real.cos_add_int_mul_two_pi]

/-- Exact Landau-gauge correction for the pullback of B X dY. -/
theorem periodicShearGauge_derivative (B a k : ℝ) (hk : k ≠ 0) (z : ℂ) :
    HasDerivAt (periodicShearGauge B a k)
      (B*(periodicShear a k z).re - B*z.re) z.im := by
  have ht := (((hasDerivAt_id z.im).const_mul k).cos).const_mul (-(B*a/k^2))
  apply ht.congr_deriv
  simp only [periodicShear,id_eq,mul_one]
  field_simp
  ring

/-- Integrated bounds after changing the contact-coordinate variable. -/
theorem periodicShear_integral_comparison (a k : ℝ) (d : ℂ → ℝ) (hd : Integrable d)
    (hpos : ∀ z, 0 ≤ d z) :
    let E := ∫ z, periodicShearWeight a k z * d (periodicShear a k z)
    (∫ z, d z) ≤ E ∧ E ≤ (1 + a^2/2) * ∫ z, d z := by
  let F := periodicShearEquiv a k
  have hF : MeasurePreserving F := periodicShear_preserves_area a k
  have hD : Integrable (fun z => d (periodicShear a k z)) :=
    (hF.integrable_comp_emb F.measurableEmbedding).mpr hd
  have hi := hD.const_mul (1+a^2/2)
  have hm : Continuous (periodicShearWeight a k) := by unfold periodicShearWeight; fun_prop
  have hb (z : ℂ) : periodicShearWeight a k z * d (periodicShear a k z) ≤
      (1+a^2/2) * d (periodicShear a k z) :=
    mul_le_mul_of_nonneg_right (periodicShearWeight_bounds a k z).2 (hpos _)
  have hw : Integrable (fun z => periodicShearWeight a k z * d (periodicShear a k z)) := by
    apply hi.mono' (hm.aestronglyMeasurable.mul hD.aestronglyMeasurable)
    filter_upwards with z
    change ‖periodicShearWeight a k z * d (periodicShear a k z)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith [(periodicShearWeight_bounds a k z).1]) (hpos _))]
    exact hb z
  have hchange : (∫ z, d (periodicShear a k z)) = ∫ z, d z := hF.integral_comp' d
  dsimp only
  rw [← hchange, ← integral_const_mul]
  exact ⟨integral_mono hD hw (fun z => le_mul_of_one_le_left (hpos _) (periodicShearWeight_bounds a k z).1),
    integral_mono hw hi hb⟩

/-- A nontrivial shear cannot be the quotient of two entire orbital factors.
This allows zeros of the putative denominator, including at the origin. -/
theorem periodicShear_entire_quotient_obstruction {a k : ℝ} (ha : a ≠ 0) (hk : k ≠ 0)
    (b c : ℂ → ℂ) (hb : Differentiable ℂ b) (hc : Differentiable ℂ c)
    (hbc : ∀ z, c z = periodicShear a k z * b z) : b = 0 := by
  have hn : ∀ᶠ z : ℂ in nhds 0, a * Real.cos (k*z.im) ≠ 0 := by
    have hcont : Continuous (fun z : ℂ => a * Real.cos (k*z.im)) := by fun_prop
    exact hcont.continuousAt.eventually_ne (by simpa using ha)
  have hz : b =ᶠ[nhds (0:ℂ)] (0 : ℂ → ℂ) := by
    filter_upwards [hn] with z hdir
    by_contra h
    have hne : b z ≠ 0 := h
    have he : (fun w => c w / b w) =ᶠ[nhds z] periodicShear a k := by
      filter_upwards [hb.continuous.continuousAt.eventually_ne hne] with w hw
      rw [hbc]; exact mul_div_cancel_right₀ _ hw
    exact periodicShear_not_complex_differentiable a k hk z hdir
      (((hc z).div (hb z) hne).congr_of_eventuallyEq he.symm)
  exact AnalyticOnNhd.eq_of_eventuallyEq (fun z _ => hb.analyticAt z)
    (fun _ _ => analyticAt_const) hz

theorem periodicShear_continuous (a k : ℝ) : Continuous (periodicShear a k) := by
  have he : periodicShear a k = fun z : ℂ => z + ((a/k*Real.sin (k*z.im) : ℝ) : ℂ) := by
    funext z
    apply Complex.ext <;> simp only [periodicShear, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, add_zero]
  rw [he]
  fun_prop

/-- Even an arbitrary common multiplier cannot reproduce the first two sheared
orbital shapes by multiplying two entire functions. Equalities are only a.e.;
the common nonzero vacuum envelope can include Gaussian normalizations. -/
theorem periodicShear_no_common_scalar {a k : ℝ} (ha : a ≠ 0) (hk : k ≠ 0)
    (vac : ℂ → ℂ) (hv : ∀ᵐ z ∂volume, vac z ≠ 0) :
    ¬ ∃ f b c : ℂ → ℂ, Differentiable ℂ b ∧ Differentiable ℂ c ∧
      (∀ᵐ z ∂volume, vac z = f z * b z) ∧
      (∀ᵐ z ∂volume, periodicShear a k z * vac z = f z * c z) := by
  rintro ⟨f,b,c,hb,hc,h0,h1⟩
  have he : c =ᵐ[volume] fun z => periodicShear a k z * b z := by
    filter_upwards [h0,h1,hv] with z h0z h1z hnonzero
    have hf : f z ≠ 0 := fun hz => hnonzero (by simpa [hz] using h0z)
    apply mul_left_cancel₀ hf
    rw [← h1z,h0z]; ring
  have hpoint := MeasureTheory.Measure.eq_of_ae_eq he hc.continuous
    ((periodicShear_continuous a k).mul hb.continuous)
  have hz := periodicShear_entire_quotient_obstruction ha hk b c hb hc (congrFun hpoint)
  obtain ⟨z,h0z,hnz⟩ := (h0.and hv).exists
  exact hnz (by simpa [hz] using h0z)

def shearConfiguration (a k : ℝ) {N : ℕ} (z : Fin N → ℂ) : Fin N → ℂ :=
  fun i => periodicShear a k (z i)

theorem shearConfiguration_preserves_volume (a k : ℝ) (N : ℕ) :
    MeasurePreserving (@shearConfiguration a k N) :=
  volume_preserving_pi (fun _ => periodicShear_preserves_area a k)

private abbrev ShearConfigL2 (N : ℕ) := Lp ℂ 2 (volume : Measure (Fin N → ℂ))

def shearConfigurationUnitary (a k : ℝ) (N : ℕ) : ShearConfigL2 N ≃ₗᵢ[ℂ] ShearConfigL2 N := by
  let F := @shearConfiguration a k N
  let G := @shearConfiguration (-a) k N
  have hF := shearConfiguration_preserves_volume a k N
  have hG := shearConfiguration_preserves_volume (-a) k N
  apply LinearIsometryEquiv.ofSurjective (Lp.compMeasurePreservingₗᵢ ℂ F hF)
  intro u
  refine ⟨Lp.compMeasurePreserving G hG u, ?_⟩
  change Lp.compMeasurePreserving F hF (Lp.compMeasurePreserving G hG u) = u
  rw [← Lp.compMeasurePreserving_comp_apply]
  have hid : G ∘ F = id := by
    funext z i; exact periodicShear_inverse a k _
  simp [hid]

theorem shearConfigurationUnitary_apply (a k : ℝ) (N : ℕ) (u : ShearConfigL2 N) :
    (shearConfigurationUnitary a k N u : (Fin N → ℂ) → ℂ) =ᵐ[volume] u ∘ shearConfiguration a k :=
  Lp.coeFn_compMeasurePreserving _ _

/-- Particle permutations commute with the same spatial shear on each coordinate. -/
theorem shearConfiguration_permute (a k : ℝ) {N : ℕ} (z : Fin N → ℂ) (σ : Equiv.Perm (Fin N)) :
    shearConfiguration a k (z ∘ σ) = shearConfiguration a k z ∘ σ := rfl

/-- A finite, nonzero shear with a nonconstant metric contact density. -/
theorem periodicShear_unit_example :
    periodicShearWeight 1 1 0 = 3/2 ∧
    periodicShearWeight 1 1 ((Real.pi/2 : ℝ) * Complex.I) = 1 ∧
    ¬DifferentiableAt ℂ (periodicShear 1 1) 0 := by
  refine ⟨by norm_num [periodicShearWeight], ?_, ?_⟩
  · simp [periodicShearWeight]
  · apply periodicShear_not_complex_differentiable <;> norm_num

/-- Symbol for use in a weighted *pair* operator in unchanged orthonormal
orbital coordinates. Its fourth power encodes the shear metric weight. -/
def periodicShearPairSymbol (a k : ℝ) : ℂ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun z => ((Real.sqrt (Real.sqrt (periodicShearWeight a k z)) : ℝ) : ℂ))
    (by unfold periodicShearWeight; fun_prop) (Real.sqrt (Real.sqrt (1+a^2/2))) (fun z => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (periodicShearWeight_bounds a k z).2))

theorem periodicShearPairSymbol_fourth (a k : ℝ) (z : ℂ) :
    ‖periodicShearPairSymbol a k z‖^4 = periodicShearWeight a k z := by
  change ‖((Real.sqrt (Real.sqrt _) : ℝ) : ℂ)‖^4 = _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    show (4:ℕ)=2*2 by decide, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt]
  linarith [(periodicShearWeight_bounds a k z).1]

end VortexGap.Fermion

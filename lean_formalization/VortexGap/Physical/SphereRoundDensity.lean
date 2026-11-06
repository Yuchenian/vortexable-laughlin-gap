import VortexGap.Geometry.SphereConfigurations

noncomputable section
namespace VortexGap.Fermion
open MeasureTheory Metric VortexGap.Geometry OAI.Laughlin.Rotation
open scoped ComplexConjugate

def cartesianBloch (x : sphere (0:RoundAmbient) 1) : BlochSphere :=
  ⟨(⟨x.val 0,x.val 1⟩,x.val 2),by
    have h := real_inner_self_eq_norm_sq x.val
    rw [mem_sphere_zero_iff_norm.mp x.property,PiLp.inner_apply,Fin.sum_univ_three] at h
    simp only [RCLike.inner_apply,conj_trivial] at h
    simp [Complex.normSq_apply]
    nlinarith⟩

theorem cartesianBloch_continuous : Continuous cartesianBloch := by
  apply Continuous.subtype_mk
  have hc (i : Fin 3) : Continuous (fun x : sphere (0:RoundAmbient) 1 => x.val i) :=
    (PiLp.continuous_apply 2 _ i).comp continuous_subtype_val
  apply Continuous.prodMk _ (hc 2)
  simp only [Complex.mk_eq_add_mul_I]
  exact (Complex.continuous_ofReal.comp (hc 0)).add ((Complex.continuous_ofReal.comp (hc 1)).mul continuous_const)

variable {q N : ℕ} (f : SourceSU2 → ℂ) (hf : Continuous f) (hi : sphereFiberInvariant f)
  (x : particleSector (q+1) N)

def roundDensity (p : Fin N → sphere (0:RoundAmbient) 1) : ℝ :=
  sphereQuotientDensity f hf hi x ((sphereConfigurationHomeomorph N).symm (fun i => cartesianBloch (p i)))

theorem roundDensity_lift (g : Fin N → SourceSU2) :
    roundDensity f hf hi x (fun i => roundBloch (g i)) = ‖sphereDeformedWave f hf x g‖^2 := by
  change sphereQuotientDensity f hf hi x ((sphereConfigurationHomeomorph N).symm
    (sphereConfigurationHomeomorph N (Quot.mk _ g))) = _
  rw [Homeomorph.symm_apply_apply]
  rfl

theorem roundDensity_continuous : Continuous (roundDensity f hf hi x) := by
  have hw : Continuous (sphereDeformedWave f hf x) := by
    exact continuous_finsetSum _ fun a _ => continuous_const.mul
      (continuous_finsetProd _ fun i _ => (sphereFilteredValue_continuous q f hf _).comp (continuous_apply i))
  have hd : Continuous (sphereQuotientDensity f hf hi x) := continuous_quot_lift _ (hw.norm.pow 2)
  exact hd.comp ((sphereConfigurationHomeomorph N).symm.continuous.comp
    (continuous_pi fun i => cartesianBloch_continuous.comp (continuous_apply i)))

theorem roundDensity_integral (a b : ℝ) (ha : 0<a) (hl : ∀ g, a ≤ ‖f g‖^2) (hu : ∀ g, ‖f g‖^2 ≤ b) :
    (∫ p, roundDensity f hf hi x p ∂Measure.pi (fun _ => ENNReal.ofReal ((q:ℝ)+1) • normalizedRoundArea)) = ‖x‖^2 := by
  have hm := sphereOrbital_round_configuration q N
  rw [← hm.map_eq,integral_map hm.aemeasurable (roundDensity_continuous f hf hi x).aestronglyMeasurable]
  simp_rw [roundDensity_lift]
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have h := sphereDeformedWave_inner f hf a b ha hl hu x x
  have he : inner ℂ x x = (‖x‖ : ℂ)^2 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) x
  simpa only [Complex.conj_mul',Complex.ofReal_pow] using h.trans he

theorem roundDensity_axial_three (y : particleSector (6+1) 3) (hy : ‖y‖=1) :
    (∫ p, roundDensity sphereAxialMultiplier sphereAxialMultiplier_continuous
      sphereAxial_fiberInvariant y p ∂Measure.pi (fun _ => ENNReal.ofReal ((6:ℝ)+1) • normalizedRoundArea)) = 1 := by
  have hl (g) : 1 ≤ ‖sphereAxialMultiplier g‖^2 := by
    rw [sphereAxialMultiplier_weight]; linarith [sq_nonneg (‖g.val 0 0‖)]
  have hu (g) : ‖sphereAxialMultiplier g‖^2 ≤ (1001/1000:ℝ) := by
    rw [sphereAxialMultiplier_weight]
    have h := unitary_entry_norm_le_one g.val g.property.1 0 0
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (add_nonneg (norm_nonneg (g.val 0 0)) zero_le_one)]
  simpa [hy] using roundDensity_integral (q := 6) (N := 3) _ sphereAxialMultiplier_continuous sphereAxial_fiberInvariant y _ _ zero_lt_one hl hu

end VortexGap.Fermion
end

noncomputable section
namespace VortexGap.Fermion
open MeasureTheory Metric VortexGap.Geometry OAI.Laughlin.Rotation VortexGap.SpherePolynomial
abbrev RoundPoint := sphere (0:RoundAmbient) 1

theorem cartesianBloch_injective : Function.Injective cartesianBloch := by
  intro x y h
  have hw := congrArg (fun p : BlochSphere => p.val.1) h
  have hz := congrArg (fun p : BlochSphere => p.val.2) h
  apply Subtype.ext
  ext i
  fin_cases i
  · exact congrArg Complex.re hw
  · exact congrArg Complex.im hw
  · exact hz

theorem roundBloch_onto : Function.Surjective roundBloch := by
  intro p
  obtain ⟨g,hg⟩ := sphereBloch_surjective (cartesianBloch p)
  exact ⟨g,cartesianBloch_injective hg⟩

theorem roundMultiplier_invariant (F : RoundPoint → ℂ) : sphereFiberInvariant (F ∘ roundBloch) := by
  intro g z hz
  exact congrArg F (cartesianBloch_injective (sphereBloch_phase g z hz))

def roundReferenceDensity {q N : ℕ} (l : particleSector (q+1) N) (p : Fin N → RoundPoint) : ℝ :=
  ‖sphereReferenceWave l (fun i => (roundBloch_onto (p i)).choose)‖^2

theorem round_laughlin_density (n N : ℕ) (hQ : 3*((N+2)-1) = n+1)
    (F : RoundPoint → ℂ) (hF : Continuous F) (a b : ℝ)
    (ha : 0<a) (hl : ∀ p, a ≤ ‖F p‖^2) (hu : ∀ p, ‖F p‖^2 ≤ b) :
    let f := F ∘ roundBloch
    let hf := hF.comp roundBloch_continuous
    ∃ l y : particleSector (n+2) (N+2), sectorPoly l = laughlin (N+2) ∧
      LinearMap.ker (sphereSectorHam n (N+2) (spherePhysicalPair n f hf)).toLinearMap = ℂ ∙ y ∧
      y ≠ 0 ∧ ∀ p, roundDensity f hf (roundMultiplier_invariant F) y p =
        (∏ i, ‖F (p i)‖^2) * roundReferenceDensity l p := by
  dsimp only
  obtain ⟨l,y,hp,hk,hw⟩ := sphere_laughlin_product_generator n N hQ _ (hF.comp roundBloch_continuous)
    a b ha (fun g => hl (roundBloch g)) (fun g => hu (roundBloch g))
  have hy : y ≠ 0 := by
    intro he
    have h := sphere_deformed_laughlin_unique n N hQ _ (hF.comp roundBloch_continuous)
      a b ha (fun g => hl (roundBloch g)) (fun g => hu (roundBloch g))
    rw [hk,he] at h
    rw [Submodule.span_zero_singleton] at h
    simp at h
  refine ⟨l,y,hp,hk,hy,fun p => ?_⟩
  let g := fun i => (roundBloch_onto (p i)).choose
  have hg (i) : roundBloch (g i) = p i := (roundBloch_onto (p i)).choose_spec
  have h := roundDensity_lift _ (hF.comp roundBloch_continuous) (roundMultiplier_invariant F) y g
  rw [show (fun i => roundBloch (g i)) = p from funext hg,hw] at h
  simpa only [Function.comp_apply,hg,norm_mul,norm_prod,mul_pow,Finset.prod_pow,roundReferenceDensity,g] using h

theorem roundReferenceDensity_lift {q N : ℕ} (l : particleSector (q+1) N) (g : Fin N → SourceSU2) :
    roundReferenceDensity l (fun i => roundBloch (g i)) = ‖sphereReferenceWave l g‖^2 := by
  let h := fun i => (roundBloch_onto (roundBloch (g i))).choose
  have he (i) : sphereBloch (g i) = sphereBloch (h i) :=
    congrArg cartesianBloch (roundBloch_onto (roundBloch (g i))).choose_spec.symm
  have one (i) := spinor_rotation_phase (g i) (h i)
    (congrArg (fun p : BlochSphere => p.val.2) (he i))
    (congrArg (fun p : BlochSphere => p.val.1) (he i))
  choose z hz hz' using one
  change ‖sphereReferenceWave l h‖^2 = _
  rw [funext hz',sphereReferenceWave_gauge l g z hz,norm_mul,norm_prod]
  simp [norm_pow,hz]

theorem round_laughlin_normalization {q N : ℕ} (F : RoundPoint → ℂ) (hF : Continuous F)
    (a b : ℝ) (ha : 0<a) (hl : ∀ p, a ≤ ‖F p‖^2) (hu : ∀ p, ‖F p‖^2 ≤ b)
    (l y : particleSector (q+1) N) (hy : y ≠ 0)
    (hd : ∀ p, roundDensity (F ∘ roundBloch) (hF.comp roundBloch_continuous) (roundMultiplier_invariant F) y p =
      (∏ i, ‖F (p i)‖^2) * roundReferenceDensity l p) :
    (∫ p, ((∏ i, ‖F (p i)‖^2) * roundReferenceDensity l p) / ‖y‖^2
      ∂Measure.pi (fun _ => ENNReal.ofReal ((q:ℝ)+1) • normalizedRoundArea)) = 1 := by
  simp_rw [← hd]
  rw [integral_div,roundDensity_integral (q := q) (N := N) (F ∘ roundBloch) (hF.comp roundBloch_continuous) (roundMultiplier_invariant F) y a b ha (fun g => hl (roundBloch g)) (fun g => hu (roundBloch g))]
  exact div_self (pow_ne_zero _ (norm_ne_zero_iff.mpr hy))

end VortexGap.Fermion
end

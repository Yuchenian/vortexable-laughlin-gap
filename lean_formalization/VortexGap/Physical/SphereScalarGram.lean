import VortexGap.Geometry.SphereOrbitalGram
import VortexGap.Physical.GramFilter
import VortexGap.Physical.PlaneWeightedBounds
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory OAI.Laughlin.Rotation VortexGap.Frame
open scoped InnerProduct ComplexOrder ENNReal
private abbrev Orb (q : ℕ) := EuclideanSpace ℂ (Fin (q+1))

def sphereOrbitalMeasure (q : ℕ) := ENNReal.ofReal ((q:ℝ)+1) • sourceHaar
instance (q : ℕ) : IsFiniteMeasure (sphereOrbitalMeasure q) := by
  constructor
  simp [sphereOrbitalMeasure,Measure.smul_apply]

def sphereScalarRow (q : ℕ) (f : SourceSU2 → ℂ) (g : SourceSU2) : Orb q →L[ℂ] ℂ :=
  f g • innerSL ℂ (WithLp.toLp 2 (fun i : Fin (q+1) => sourceSpinRepresentation q g i 0) : Orb q)

theorem sphereScalarRow_apply (q : ℕ) (f : SourceSU2 → ℂ) (g : SourceSU2) (x : Orb q) :
    sphereScalarRow q f g x = f g * sphereOrbitalValue q x g := by
  simp [sphereScalarRow,sphereOrbitalValue,PiLp.inner_apply,RCLike.inner_apply,mul_comm]

theorem sphereScalarRow_memLp (q : ℕ) (f : SourceSU2 → ℂ) (hf : Continuous f) :
    MemLp (sphereScalarRow q f) 2 (sphereOrbitalMeasure q) := by
  apply Continuous.memLp_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
  apply hf.smul
  apply (innerSL ℂ).continuous.comp
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (q+1) => ℂ)).comp
  exact continuous_pi (fun i => sourceSpinRepresentation_continuous q i 0)

def sphereScalarMap (q : ℕ) (f : SourceSU2 → ℂ) (hf : Continuous f) :=
  operatorAnalysis (sphereOrbitalMeasure q) (sphereScalarRow q f) (sphereScalarRow_memLp q f hf)

theorem sphereScalarMap_norm_sq (q : ℕ) (f : SourceSU2 → ℂ) (hf : Continuous f) (x : Orb q) :
    ‖sphereScalarMap q f hf x‖^2 = ((q:ℝ)+1) * ∫ g, ‖f g * sphereOrbitalValue q x g‖^2 ∂sourceHaar := by
  rw [sphereScalarMap,operatorAnalysis_norm_sq]
  simp_rw [sphereScalarRow_apply]
  rw [sphereOrbitalMeasure,integral_smul_measure]
  simp [ENNReal.toReal_ofReal (by positivity : 0 ≤ (q:ℝ)+1)]

theorem sphereScalarGram_bounds (q : ℕ) (f : SourceSU2 → ℂ) (hf : Continuous f) (a b : ℝ) (ha0 : 0 ≤ a)
    (ha : ∀ g, a ≤ ‖f g‖^2) (hb : ∀ g, ‖f g‖^2 ≤ b) :
    let G := gramOperator (sphereScalarMap q f hf)
    a • (1 : Orb q →L[ℂ] Orb q) ≤ G ∧ G ≤ b • 1 := by
  let F := sphereScalarMap q f hf
  have he (x : Orb q) : (inner ℂ x (gramOperator F x)).re = ‖F x‖^2 := by
    rw [gramOperator,ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right]
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
  have hs (c : ℝ) (x : Orb q) : (inner ℂ x ((c • (1 : Orb q →L[ℂ] Orb q)) x)).re = c*‖x‖^2 := by
    change (inner ℂ x ((c:ℂ) • x)).re = _
    rw [inner_smul_right,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    congr 1
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
  have hp (c : ℝ) (hc : 0 ≤ c) : (c • (1 : Orb q →L[ℂ] Orb q)).IsPositive := by
    change ((c : ℂ) • (1 : Orb q →L[ℂ] Orb q)).IsPositive
    exact ContinuousLinearMap.nonneg_iff_isPositive.mp
      (smul_nonneg (show 0 ≤ (c:ℂ) by exact_mod_cast hc) zero_le_one)
  have hG := ContinuousLinearMap.nonneg_iff_isPositive.mp (gramOperator_nonneg F)
  have hE (x : Orb q) : a * ‖x‖^2 ≤ ‖F x‖^2 ∧ ‖F x‖^2 ≤ b * ‖x‖^2 := by
    simpa only [F,sphereScalarMap_norm_sq,EuclideanSpace.norm_sq_eq] using
      sphereOrbitalValue_weight_bounds q x f hf a b ha hb
  constructor
  · apply positive_operator_le_of_energy _ _ (hp a ha0) hG
    intro x
    rw [hs,he]
    exact (hE x).1
  · apply positive_operator_le_of_energy _ _ hG (hp b ((sq_nonneg _).trans (hb 1)))
    intro x
    rw [hs,he]
    exact (hE x).2

theorem sphereScalarFilter_loss (q : ℕ) (f : SourceSU2 → ℂ) (hf : Continuous f) (a b : ℝ) (ha0 : 0 < a)
    (ha : ∀ g, a ≤ ‖f g‖^2) (hb : ∀ g, ‖f g‖^2 ≤ b) :
    let M := gramFilter (gramOperator (sphereScalarMap q f hf)) a
    0 ≤ M ∧ ‖M‖ ≤ 1 ∧ ‖1-M^2‖ ≤ 1-a/b := by
  obtain ⟨hl,hu⟩ := sphereScalarGram_bounds q f hf a b ha0.le ha hb
  exact ⟨gramFilter_nonneg _ _,gramFilter_contraction _ _ ha0 hl,
    gramFilter_loss_le _ _ _ ha0 ((ha 1).trans (hb 1)) hl hu⟩
/-- Physical two-direction contact energy, in the Gram-orthogonalized orbitals.
The local paths can be given in any gauges with the specified center values. -/
theorem sphereScalar_contact_integral (n : ℕ) (R : ℝ) (hR : 0 < R)
    (f : SourceSU2 → ℂ) (hf : Continuous f)
    (u v : SourceSU2 → ℝ → ℂ) (A B : SourceSU2 → ℂ)
    (hu : ∀ g, DifferentiableAt ℝ (u g) 0) (hv : ∀ g, DifferentiableAt ℝ (v g) 0)
    (hu0 : ∀ g, u g 0 = f g) (hv0 : ∀ g, v g 0 = f g) (x : PairSpace (n+2)) :
    let y := exteriorSquare (gramInvSqrt (sphereScalarMap (n+1) f hf)).toLinearMap x
    (∫ g, sphereContactAreaFactor n R *
      (‖sphereMultipliedContact n R g 1 (A g) (u g) y‖^2 +
       ‖sphereMultipliedContact n R g Complex.I (B g) (v g) y‖^2) ∂sourceHaar) =
      ∫ g, ‖f g‖^4 * ‖inner ℂ (sphereOrbitPair n g) y‖^2 ∂spherePairMeasure n := by
  dsimp only
  rw [spherePairMeasure,integral_smul_measure]
  simp only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*(n:ℝ)+1),smul_eq_mul,← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro g
  dsimp only
  rw [sphereMultipliedContact_density n R hR g _ _ _ _ (hu g) (hv g) ((hv0 g).trans (hu0 g).symm),hu0]
  ring

theorem sphereScalar_filtered_transfer (n N : ℕ) (f : SourceSU2 → ℂ) (hf : Continuous f)
    (a b : ℝ) (ha0 : 0 < a) (ha : ∀ g, a ≤ ‖f g‖^2) (hb : ∀ g, ‖f g‖^2 ≤ b)
    (γ : ℝ) (hgap : ∀ K ≤ N, ∀ y : Space (n+2), InSector K y →
      let H := pairLift (spherePairSector n).starProjection.toLinearMap
      γ*(inner ℂ y (H y)).re ≤ (inner ℂ y ((H*H) y)).re)
    {x : Space (n+2)} (hx : InSector N x) :
    let M := gramFilter (gramOperator (sphereScalarMap (n+1) f hf)) a
    let H := continuousFrameHamiltonian (spherePairMeasure n)
      (fun g => exteriorSquare M.toLinearMap (sphereOrbitPair n g))
    (γ-sphereRadialSchur n*‖1-M^2‖-‖1-M^2‖^2)*(inner ℂ x (H x)).re ≤
      (inner ℂ x ((H*H) x)).re := by
  obtain ⟨hm,hc,_⟩ := sphereScalarFilter_loss (n+1) f hf a b ha0 ha hb
  exact sphereFiltered_transfer n N _ hm hc γ hgap hx

end VortexGap.Fermion

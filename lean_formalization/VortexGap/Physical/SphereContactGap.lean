import VortexGap.Physical.SphereScalarGram
import VortexGap.Physical.KernelSpectrum
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory OAI.Laughlin.Rotation
open scoped InnerProduct ComplexOrder ENNReal
variable {n : ℕ}
local instance (m k : ℕ) : CompleteSpace (particleSector m k) := FiniteDimensional.complete ℂ _

/-- The CAR Hamiltonian on the actual N-sector for continuous spherical pair columns. -/
def sphereSectorHam (n N : ℕ) (p : SourceSU2 → PairSpace (n+2)) :=
  pairLiftSector N (continuousPairOperator (spherePairMeasure n) p).toLinearMap

theorem sphereSectorHam_apply (N : ℕ) (p : SourceSU2 → PairSpace (n+2)) (hp : Continuous p)
    (x : particleSector (n+2) N) : (sphereSectorHam n N p x : Space (n+2)) =
      continuousFrameHamiltonian (spherePairMeasure n) p x := by
  rw [continuousFrameHamiltonian_pairLift _ _ (hp.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  rfl

theorem sphereSectorHam_norm (N : ℕ) (p : SourceSU2 → PairSpace (n+2)) (hp : Continuous p)
    (x : particleSector (n+2) N) : ‖sphereSectorHam n N p x‖ =
      ‖continuousFrameHamiltonian (spherePairMeasure n) p x‖ := by
  exact congrArg (fun z : Space (n+2) => ‖z‖) (sphereSectorHam_apply N p hp x)

theorem sphereSectorHam_positive (N : ℕ) (p : SourceSU2 → PairSpace (n+2)) (hp : Continuous p) :
    ContinuousLinearMap.IsPositive (𝕜 := ℂ) (E := particleSector (n+2) N) (sphereSectorHam n N p) := by
  have h := continuousFrameHamiltonian_positive (spherePairMeasure n) p
    (hp.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  apply (ContinuousLinearMap.isPositive_iff_complex _).mpr
  intro x
  simpa only [Submodule.coe_inner,sphereSectorHam_apply N p hp] using!
    (ContinuousLinearMap.isPositive_iff_complex _).mp h (x : Space (n+2))

theorem sphereSectorHam_energy (N : ℕ) (p : SourceSU2 → PairSpace (n+2)) (hp : Continuous p)
    (x : particleSector (n+2) N) :
    (inner ℂ x (sphereSectorHam n N p x)).re = ∫ g, ‖pairAnnihilate (p g) (x:Space (n+2))‖^2 ∂spherePairMeasure n := by
  rw [Submodule.coe_inner,sphereSectorHam_apply N p hp,continuousFrameHamiltonian_energy _ _
    (hp.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]

theorem sphereSectorHam_weight_bounds (N : ℕ) (p : SourceSU2 → PairSpace (n+2)) (hp : Continuous p)
    (w : SourceSU2 → ℂ) (hw : Continuous w) (l u : ℝ)
    (hl : ∀ g, l ≤ ‖w g‖^2) (hu : ∀ g, ‖w g‖^2 ≤ u) (x : particleSector (n+2) N) :
    let B := sphereSectorHam n N p
    let A := sphereSectorHam n N (fun g => w g • p g)
    l*(inner ℂ x (B x)).re ≤ (inner ℂ x (A x)).re ∧
      (inner ℂ x (A x)).re ≤ u*(inner ℂ x (B x)).re := by
  dsimp only
  rw [sphereSectorHam_energy _ _ hp,sphereSectorHam_energy N (fun g => w g • p g) (hw.smul hp)]
  simp only [pairAnnihilate_smul,LinearMap.smul_apply,norm_smul,RCLike.norm_conj,mul_pow]
  let e := fun g => ‖pairAnnihilate (p g) (x : Space (n+2))‖^2
  have hE : Continuous e := ((pairAnnihilate_continuous.comp hp).clm_apply continuous_const).norm.pow 2
  have hi (c : ℝ) : Integrable (fun g => c * e g) (spherePairMeasure n) :=
    (continuous_const.mul hE).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hj := ((hw.norm.pow 2).mul hE).integrable_of_hasCompactSupport
    (μ := spherePairMeasure n) (HasCompactSupport.of_compactSpace _)
  rw [← integral_const_mul,← integral_const_mul]
  exact ⟨integral_mono (hi l) hj (fun g => mul_le_mul_of_nonneg_right (hl g) (sq_nonneg _)),
    integral_mono hj (hi u) (fun g => mul_le_mul_of_nonneg_right (hu g) (sq_nonneg _))⟩
def spherePhysicalPair (n : ℕ) (f : SourceSU2 → ℂ) (hf : Continuous f) (g : SourceSU2) :=
  f g ^ 2 • exteriorSquare (gramInvSqrt (sphereScalarMap (n+1) f hf)).toLinearMap (sphereOrbitPair n g)

theorem spherePhysicalPair_continuous (n : ℕ) (f : SourceSU2 → ℂ) (hf : Continuous f) :
    Continuous (spherePhysicalPair n f hf) := by
  apply (hf.pow 2).smul
  exact (exteriorSquare _).toContinuousLinearMap.continuous.comp (sphereOrbitPair_continuous n)

theorem spherePhysicalPair_rescale (n : ℕ) (f : SourceSU2 → ℂ) (hf : Continuous f) (a : ℝ)
    (ha : 0 < a) (g : SourceSU2) :
    let M := gramFilter (gramOperator (sphereScalarMap (n+1) f hf)) a
    spherePhysicalPair n f hf g = (f g ^ 2 / (a:ℂ)) • exteriorSquare M.toLinearMap (sphereOrbitPair n g) := by
  dsimp only
  rw [gramFilter_eq_normalized_inverse]
  change _ = _ • exteriorSquare ((Real.sqrt a : ℂ) • _) _
  rw [exteriorSquare_smul,LinearMap.smul_apply,smul_smul,← Complex.ofReal_pow,Real.sq_sqrt ha.le]
  simp [spherePhysicalPair,ha.ne']

private theorem sector_gap_from_full (N : ℕ) (p : SourceSU2 → PairSpace (n+2)) (hp : Continuous p)
    (c d : ℝ) (hcd : c ≤ d)
    (hg : ∀ x : particleSector (n+2) N,
      let T := continuousFrameHamiltonian (spherePairMeasure n) p
      d * (inner ℂ (x : Space (n+2)) (T x)).re ≤ (inner ℂ (x : Space (n+2)) (T (T x))).re) :
    let B := sphereSectorHam n N p
    ContinuousLinearMap.IsPositive (𝕜 := ℂ) (E := particleSector (n+2) N) (B*B-(c:ℂ) • B) := by
  let T := continuousFrameHamiltonian (spherePairMeasure n) p
  have hT := continuousFrameHamiltonian_positive (spherePairMeasure n) p
    (hp.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  apply (quadratic_positive_norm_iff _ (sphereSectorHam_positive N p hp) c).mpr
  intro x
  have hsq : (inner ℂ (x:Space (n+2)) (T (T x))).re = ‖T x‖^2 := by
    rw [← hT.inner_left_eq_inner_right (x:Space (n+2)) (T x)]
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
  rw [sphereSectorHam_norm N p hp,Submodule.coe_inner,sphereSectorHam_apply N p hp]
  exact ((mul_le_mul_of_nonneg_right hcd (hT.re_inner_nonneg_right (x : Space (n+2)))).trans
    (hg x)).trans_eq hsq

private theorem sector_comparison {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B : H →L[ℂ] H) (hA : A.IsPositive) (hB : B.IsPositive) (u c : ℝ)
    (hh : ∀ x, 1*(inner ℂ x (B x)).re ≤ (inner ℂ x (A x)).re ∧
        (inner ℂ x (A x)).re ≤ u * (inner ℂ x (B x)).re)
    (hg : (B*B-(c:ℂ) • B).IsPositive) :
    ∀ t ∈ spectrum ℝ A, t = 0 ∨ c ≤ t := by
  have ha := ContinuousLinearMap.nonneg_iff_isPositive.mpr hA
  have hb := ContinuousLinearMap.nonneg_iff_isPositive.mpr hB
  apply kernel_complement_gap_spectrum A ha c
  simpa only [one_mul] using positive_form_comparison_of_quadratic_gap A B ha hb
    1 u c zero_lt_one (fun x => (hh x).1) (fun x => (hh x).2) hg

private theorem weighted_spectrum (N : ℕ) (p : SourceSU2 → PairSpace (n+2)) (hp : Continuous p)
    (w : SourceSU2 → ℂ) (hw : Continuous w) (u γ : ℝ) (hl : ∀ g, 1 ≤ ‖w g‖^2) (hu : ∀ g, ‖w g‖^2 ≤ u)
    (hquad : let B := sphereSectorHam n N p
      ContinuousLinearMap.IsPositive (𝕜 := ℂ) (E := particleSector (n+2) N) (B*B-(γ:ℂ) • B)) :
    ∀ t ∈ spectrum ℝ (sphereSectorHam n N (fun g => w g • p g)), t = 0 ∨ γ ≤ t := by
  have compare := @sector_comparison (particleSector (n+2) N) _ _ _
    (sphereSectorHam n N (fun g => w g • p g)) (sphereSectorHam n N p)
  exact compare (sphereSectorHam_positive N (fun g => w g • p g) (hw.smul hp))
    (sphereSectorHam_positive N p hp) u γ
    (fun x => sphereSectorHam_weight_bounds N p hp w hw 1 u hl hu x) hquad

private theorem schur_loss_le (γ C δ d : ℝ) (hC : C ≤ 14) (hδ : 0 ≤ δ) (hd : δ ≤ d) :
    γ-14*d-d^2 ≤ γ-C*δ-δ^2 := by
  linarith only [mul_le_mul_of_nonneg_right hC hδ,pow_le_pow_left₀ hδ hd 2,hd]

/-- Weighted CAR lift on a fixed sector for a sphere frame after one-particle filtering. -/
theorem sphereWeighted_filter_spectrum (n N : ℕ)
    (M : EuclideanSpace ℂ (Fin (n+2)) →L[ℂ] EuclideanSpace ℂ (Fin (n+2)))
    (hm : 0 ≤ M) (hc : ‖M‖ ≤ 1) (d : ℝ) (hd : ‖1-M^2‖ ≤ d)
    (w : SourceSU2 → ℂ) (hw : Continuous w) (u : ℝ) (hl : ∀ g, 1 ≤ ‖w g‖^2) (hu : ∀ g, ‖w g‖^2 ≤ u)
    (γ : ℝ) (hgap : ∀ K ≤ N, ∀ y : Space (n+2), InSector K y →
      let H := pairLift (spherePairSector n).starProjection.toLinearMap
      γ*(inner ℂ y (H y)).re ≤ (inner ℂ y ((H*H) y)).re) :
    let p := fun g => exteriorSquare M.toLinearMap (sphereOrbitPair n g)
    ∀ t ∈ spectrum ℝ (sphereSectorHam n N (fun g => w g • p g)), t = 0 ∨ γ-14*d-d^2 ≤ t := by
  let p := fun g => exteriorSquare M.toLinearMap (sphereOrbitPair n g)
  have hp : Continuous p := (exteriorSquare M.toLinearMap).toContinuousLinearMap.continuous.comp (sphereOrbitPair_continuous n)
  have hc' : γ-14*d-d^2 ≤ γ-sphereRadialSchur n*‖1-M^2‖-‖1-M^2‖^2 :=
    schur_loss_le γ _ _ _ (sphereRadialSchur_lt_fourteen n).le (norm_nonneg _) hd
  have href (x : particleSector (n+2) N) := sphereFiltered_transfer n N M hm hc γ hgap (x := (x : Space (n+2))) x.property
  have hquad := sector_gap_from_full (n := n) N p hp (γ-14*d-d^2)
    (γ-sphereRadialSchur n*‖1-M^2‖-‖1-M^2‖^2) hc' href
  exact weighted_spectrum N p hp w hw u _ hl hu hquad

/-- Conditional sector gap for the CAR lift of the orthogonalized weighted sphere contact. -/
theorem spherePhysical_gap (n N : ℕ) (f : SourceSU2 → ℂ) (hf : Continuous f)
    (a b : ℝ) (ha0 : 0 < a) (ha : ∀ g, a ≤ ‖f g‖^2) (hb : ∀ g, ‖f g‖^2 ≤ b)
    (γ : ℝ) (hgap : ∀ K ≤ N, ∀ y : Space (n+2), InSector K y →
      let H := pairLift (spherePairSector n).starProjection.toLinearMap
      γ*(inner ℂ y (H y)).re ≤ (inner ℂ y ((H*H) y)).re) :
    let H := sphereSectorHam n N (spherePhysicalPair n f hf)
    ∀ t ∈ spectrum ℝ H, t = 0 ∨ γ-14*(1-a/b)-(1-a/b)^2 ≤ t := by
  let M := gramFilter (gramOperator (sphereScalarMap (n+1) f hf)) a
  let p := fun g => exteriorSquare M.toLinearMap (sphereOrbitPair n g)
  let w := fun g => f g ^ 2 / (a:ℂ)
  have hp : Continuous p := (exteriorSquare M.toLinearMap).toContinuousLinearMap.continuous.comp (sphereOrbitPair_continuous n)
  have hw : Continuous w := (hf.pow 2).div_const _
  have he (g) : ‖w g‖ = ‖f g‖^2/a := by simp [w,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha0]
  have hr : spherePhysicalPair n f hf = fun g => w g • p g := funext (spherePhysicalPair_rescale n f hf a ha0)
  obtain ⟨hm,hc,hd⟩ := sphereScalarFilter_loss (n+1) f hf a b ha0 ha hb
  dsimp only
  rw [hr]
  apply sphereWeighted_filter_spectrum n N M hm hc (1-a/b) hd w hw ((b/a)^2) _ _ γ hgap
  · intro g
    rw [he]
    have h1 := (one_le_div ha0).mpr (ha g)
    nlinarith [sq_nonneg (‖f g‖^2/a-1)]
  · intro g
    rw [he]
    exact pow_le_pow_left₀ (div_nonneg (sq_nonneg _) ha0.le) (div_le_div_of_nonneg_right (hb g) ha0.le) 2

theorem spherePhysicalPair_contact_operator (n : ℕ) (R : ℝ) (hR : 0 < R)
    (f : SourceSU2 → ℂ) (hf : Continuous f)
    (u v : SourceSU2 → ℝ → ℂ) (A B : SourceSU2 → ℂ)
    (hu : ∀ g, DifferentiableAt ℝ (u g) 0) (hv : ∀ g, DifferentiableAt ℝ (v g) 0)
    (hu0 : ∀ g, u g 0 = f g) (hv0 : ∀ g, v g 0 = f g) (x : PairSpace (n+2)) :
    let y := exteriorSquare (gramInvSqrt (sphereScalarMap (n+1) f hf)).toLinearMap x
    (∫ g, sphereContactAreaFactor n R *
      (‖sphereMultipliedContact n R g 1 (A g) (u g) y‖^2 +
       ‖sphereMultipliedContact n R g Complex.I (B g) (v g) y‖^2) ∂sourceHaar) =
      (inner ℂ x (continuousPairOperator (spherePairMeasure n) (spherePhysicalPair n f hf) x)).re := by
  dsimp only
  rw [sphereScalar_contact_integral n R hR f hf u v A B hu hv hu0 hv0]
  let p := spherePhysicalPair n f hf
  let F := sphereScalarMap (n+1) f hf
  have hpos : 0 ≤ gramInvSqrt F := by rw [gramInvSqrt_eq_sqrt_inverse]; exact CFC.sqrt_nonneg _
  have hs : (gramInvSqrt F).toLinearMap.adjoint = (gramInvSqrt F).toLinearMap := by
    have hh := congrArg ContinuousLinearMap.toLinearMap (show (gramInvSqrt F).adjoint = gramInvSqrt F from (IsSelfAdjoint.of_nonneg hpos).star_eq)
    rw [LinearMap.adjoint_eq_toCLM_adjoint]
    exact hh
  have hp := (spherePhysicalPair_continuous n f hf).memLp_of_hasCompactSupport
    (μ := spherePairMeasure n) (p := 2) (HasCompactSupport.of_compactSpace _)
  rw [← continuousPairAnalysis_energy _ _ hp]
  change _ = ‖VortexGap.Frame.operatorAnalysis _ _ _ x‖^2
  rw [VortexGap.Frame.operatorAnalysis_norm_sq]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro g
  change _ = ‖inner ℂ (f g ^ 2 • exteriorSquare (gramInvSqrt F).toLinearMap (sphereOrbitPair n g)) x‖^2
  have hE := congrArg exteriorSquare hs
  rw [exteriorSquare_adjoint] at hE
  rw [inner_smul_left]
  have hi := LinearMap.adjoint_inner_left (exteriorSquare (gramInvSqrt F).toLinearMap) x (sphereOrbitPair n g)
  rw [hE] at hi
  rw [hi]
  simp only [norm_mul,RCLike.norm_conj,norm_pow,mul_pow]
  ring

theorem spherePhysical_gap_weak (n N : ℕ) (f : SourceSU2 → ℂ) (hf : Continuous f)
    (hdev : ∀ g, |‖f g‖^2-1| ≤ 1/1000)
    (hgap : ∀ K ≤ N, ∀ y : Space (n+2), InSector K y →
      let H := pairLift (spherePairSector n).starProjection.toLinearMap
      (1/5:ℝ)*(inner ℂ y (H y)).re ≤ (inner ℂ y ((H*H) y)).re) :
    ∀ t ∈ spectrum ℝ (sphereSectorHam n N (spherePhysicalPair n f hf)), t = 0 ∨ (1720/10000:ℝ) ≤ t := by
  have hlo (g) : (999/1000:ℝ) ≤ ‖f g‖^2 := by linarith [(abs_le.mp (hdev g)).1]
  have hhi (g) : ‖f g‖^2 ≤ (1001/1000:ℝ) := by linarith [(abs_le.mp (hdev g)).2]
  intro t ht
  refine (spherePhysical_gap n N f hf _ _ (by norm_num) hlo hhi _ hgap t ht).imp_right (le_trans ?_)
  norm_num

end VortexGap.Fermion

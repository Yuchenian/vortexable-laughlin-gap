import VortexGap.Fermion.PairBounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VortexGap.Physical.SphereContactGap

noncomputable section

namespace VortexGap.Fermion
open MeasureTheory
open scoped ComplexConjugate

theorem finitePair_spectator_readout {n : ℕ} (p : PairSpace n) (x : Space n) (S : Finset (Fin n)) :
    pairAnnihilate p x S = inner ℂ p (pairFiber S (pairStack x)) := by
  simp only [pairAnnihilate,LinearMap.sum_apply,LinearMap.smul_apply,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul,
    PiLp.inner_apply,RCLike.inner_apply]
  change (∑ a, conj (p a) * pairMode a x S) = ∑ a, pairMode a x S * conj (p a)
  simp only [mul_comm]

/-- Lift a projected two-body form bound through an arbitrary common pair
filter by expanding the outgoing occupation basis. -/
theorem finitePair_projected_energy {α : Type*} [TopologicalSpace α] [CompactSpace α]
    [MeasurableSpace α] [BorelSpace α] (μ : Measure α) [IsFiniteMeasure μ] {n : ℕ}
    (p : α → PairSpace n) (hp : Continuous p) (w : α → ℝ) (hw : Continuous w)
    (κ : ℝ) (hpair : ∀ q : PairSpace n,
      κ*(∫ z, ‖inner ℂ (p z) q‖^2 ∂μ) ≤ ∫ z, w z*‖inner ℂ (p z) q‖^2 ∂μ)
    (A : PairSpace n →L[ℂ] PairSpace n) (x : Space n) :
    κ*(∫ z, ‖pairAnnihilate (A (p z)) x‖^2 ∂μ) ≤
      ∫ z, w z*‖pairAnnihilate (A (p z)) x‖^2 ∂μ := by
  let q := fun S => A.adjoint (pairFiber S (pairStack x))
  have expand (z : α) : ‖pairAnnihilate (A (p z)) x‖^2 = ∑ S, ‖inner ℂ (p z) (q S)‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro S _
    change ‖pairAnnihilate (A (p z)) x S‖^2 = ‖inner ℂ (p z) (A.adjoint (pairFiber S (pairStack x)))‖^2
    rw [finitePair_spectator_readout,ContinuousLinearMap.adjoint_inner_right]
  have hcont (S) : Continuous (fun z => ‖inner ℂ (p z) (q S)‖^2) := (hp.inner continuous_const).norm.pow 2
  have hwI S : Integrable (fun z => w z * ‖inner ℂ (p z) (q S)‖^2) μ := (hw.mul (hcont S)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp_rw [expand,Finset.mul_sum]
  rw [integral_finsetSum _ (fun S _ => (hcont S).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
    integral_finsetSum _ (fun S _ => hwI S), Finset.mul_sum]
  exact Finset.sum_le_sum fun S _ => hpair (q S)

end VortexGap.Fermion

namespace VortexGap.Fermion
open MeasureTheory OAI.Laughlin.Rotation
open scoped InnerProduct ComplexOrder
local instance (m k : ℕ) : CompleteSpace (particleSector m k) := FiniteDimensional.complete ℂ _

private theorem inherit_projected {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B : H →L[ℂ] H) (hA : A.IsPositive) (hB : B.IsPositive) (k U : ℝ) (hk : 0 < k)
    (hl : ∀ x, k*(inner ℂ x (B x)).re ≤ (inner ℂ x (A x)).re)
    (hu : ∀ x, (inner ℂ x (A x)).re ≤ U*(inner ℂ x (B x)).re)
    : LinearMap.ker A.toLinearMap = LinearMap.ker B.toLinearMap ∧
      ∀ c : ℝ, (∀ t ∈ spectrum ℝ B, t=0 ∨ c ≤ t) → ∀ t ∈ spectrum ℝ A, t=0 ∨ k*c ≤ t := by
  have ha := ContinuousLinearMap.nonneg_iff_isPositive.mpr hA
  have hb := ContinuousLinearMap.nonneg_iff_isPositive.mpr hB
  refine ⟨positive_form_comparison_kernel A B ha hb k U hk hl hu,?_⟩
  intro c hs
  exact kernel_complement_gap_spectrum A ha _ (positive_form_comparison_of_quadratic_gap A B ha hb
    k U c hk hl hu ((quadratic_positive_iff_spectrum_gap B hB c).mpr hs))

theorem sphere_projected_comparison (n N : ℕ)
    (E : PairSpace (n+2) →L[ℂ] PairSpace (n+2)) (w : SourceSU2 → ℂ) (hw : Continuous w)
    (k : ℝ) (hk : 0 < k)
    (hpair : ∀ q : PairSpace (n+2), k*(∫ z, ‖inner ℂ (sphereOrbitPair n z) q‖^2 ∂spherePairMeasure n) ≤
      ∫ z, ‖w z‖^2 * ‖inner ℂ (sphereOrbitPair n z) q‖^2 ∂spherePairMeasure n)
    : let B := sphereSectorHam n N (fun z => E (sphereOrbitPair n z))
      let A := sphereSectorHam n N (fun z => w z • E (sphereOrbitPair n z))
      LinearMap.ker A.toLinearMap = LinearMap.ker B.toLinearMap ∧
        ∀ c : ℝ, (∀ t ∈ spectrum ℝ B, t=0 ∨ c ≤ t) → ∀ t ∈ spectrum ℝ A, t=0 ∨ k*c ≤ t := by
  let p := fun z => E (sphereOrbitPair n z)
  have hp : Continuous p := E.continuous.comp (sphereOrbitPair_continuous n)
  let B := sphereSectorHam n N p
  let A := sphereSectorHam n N (fun z => w z • p z)
  have hA := sphereSectorHam_positive N (fun z => w z • p z) (hw.smul hp)
  have hB := sphereSectorHam_positive N p hp
  have low (x : particleSector (n+2) N) : k*(inner ℂ x (B x)).re ≤ (inner ℂ x (A x)).re := by
    dsimp only [A,B]
    rw [sphereSectorHam_energy N p hp,sphereSectorHam_energy N (fun z => w z • p z) (hw.smul hp)]
    simp only [pairAnnihilate_smul,LinearMap.smul_apply,norm_smul,RCLike.norm_conj,mul_pow]
    exact finitePair_projected_energy (spherePairMeasure n) (sphereOrbitPair n) (sphereOrbitPair_continuous n)
      (fun z => ‖w z‖^2) (hw.norm.pow 2) k hpair E (x:Space (n+2))
  obtain ⟨U,hU⟩ := (isCompact_range (hw.norm.pow 2)).bddAbove
  have high (x : particleSector (n+2) N) : (inner ℂ x (A x)).re ≤ U*(inner ℂ x (B x)).re :=
    (sphereSectorHam_weight_bounds N p hp w hw 0 U (fun _ => sq_nonneg _) (fun z => hU ⟨z,rfl⟩) x).2
  have compare := @inherit_projected (particleSector (n+2) N) _ _ _ A B
  exact compare hA hB k U hk low high

theorem sphere_projected_gap (n N : ℕ) (f : SourceSU2 → ℂ) (hf : Continuous f)
    (a b κ γ : ℝ) (ha : 0 < a) (hab : a ≤ b) (hk : 0 < κ)
    (hl : a • 1 ≤ gramOperator (sphereScalarMap (n+1) f hf))
    (hu : gramOperator (sphereScalarMap (n+1) f hf) ≤ b • 1)
    (hpair : ∀ q : PairSpace (n+2),
      κ*(∫ g, ‖inner ℂ (sphereOrbitPair n g) q‖^2 ∂spherePairMeasure n) ≤
        ∫ g, ‖f g‖^4 * ‖inner ℂ (sphereOrbitPair n g) q‖^2 ∂spherePairMeasure n)
    (href : ∀ K ≤ N, ∀ y : Space (n+2), InSector K y →
      let H := pairLift (spherePairSector n).starProjection.toLinearMap
      γ*(inner ℂ y (H y)).re ≤ (inner ℂ y ((H*H) y)).re) :
    ∀ t ∈ spectrum ℝ (sphereSectorHam n N (spherePhysicalPair n f hf)),
      t = 0 ∨ κ/a^2*(γ-14*(1-a/b)-(1-a/b)^2) ≤ t := by
  let G := gramOperator (sphereScalarMap (n+1) f hf)
  let M := gramFilter G a
  let w := fun z => f z ^ 2 / (a:ℂ)
  have hw : Continuous w := (hf.pow 2).div_const _
  have he z : ‖w z‖^2 = (a^2)⁻¹ * ‖f z‖^4 := by
    simp only [w,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha,div_pow,← pow_mul]
    ring
  have hp (q : PairSpace (n+2)) : κ/a^2*(∫ z, ‖inner ℂ (sphereOrbitPair n z) q‖^2 ∂spherePairMeasure n) ≤
        ∫ z, ‖w z‖^2*‖inner ℂ (sphereOrbitPair n z) q‖^2 ∂spherePairMeasure n := by
    simp_rw [he,mul_assoc]
    rw [integral_const_mul]
    have h := mul_le_mul_of_nonneg_left (hpair q) (show 0 ≤ (a^2)⁻¹ by positivity)
    linarith only [h,show κ/a^2*(∫ z, ‖inner ℂ (sphereOrbitPair n z) q‖^2 ∂spherePairMeasure n) =
      (a^2)⁻¹*(κ*(∫ z, ‖inner ℂ (sphereOrbitPair n z) q‖^2 ∂spherePairMeasure n)) by ring]
  have hs := sphereWeighted_filter_spectrum n N M (gramFilter_nonneg G a)
    (gramFilter_contraction G a ha hl) (1-a/b) (gramFilter_loss_le G a b ha hab hl hu)
    (fun _ => 1) continuous_const 1 (by simp) (by simp) γ href
  simp only [one_smul] at hs
  have hr := funext (spherePhysicalPair_rescale n f hf a ha)
  rw [hr]
  exact (sphere_projected_comparison n N (exteriorSquare M.toLinearMap).toContinuousLinearMap w hw
    (κ/a^2) (div_pos hk (sq_pos_of_pos ha)) hp).2 _ hs

end VortexGap.Fermion

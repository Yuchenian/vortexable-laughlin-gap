import VortexGap.Frame.ContinuousPairSynthesis
import VortexGap.Frame.L2FiniteFiber
import VortexGap.Frame.TwoNoiseFactorization

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory
open scoped InnerProduct ENNReal BigOperators

/-- Actual pair/system product in the existing l2 coordinates. -/
def pairStackProduct {n : ℕ} : PairSpace n →ₗ[ℂ] Space n →ₗ[ℂ] PairStackSpace n where
  toFun p := {
    toFun := fun x => WithLp.toLp 2 (fun aA => p aA.1 * x aA.2)
    map_add' := by intro x y; ext aA; simp [mul_add]
    map_smul' := by intro z x; ext aA; simp [mul_left_comm] }
  map_add' := by intro p q; ext x aA; simp [add_mul]
  map_smul' := by intro z p; ext x aA; simp [mul_assoc]

def pairStackProductCLM (n : ℕ) : PairSpace n →L[ℂ] Space n →L[ℂ] PairStackSpace n :=
  (((LinearMap.toContinuousLinearMap :
    (Space n →ₗ[ℂ] PairStackSpace n) ≃ₗ[ℂ] (Space n →L[ℂ] PairStackSpace n)).toLinearMap).comp
    pairStackProduct).toContinuousLinearMap

theorem pairStackProduct_norm {n : ℕ} (p : PairSpace n) (x : Space n) :
    ‖pairStackProduct p x‖ = ‖p‖ * ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow]
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, pairStackProduct,
    LinearMap.coe_mk, AddHom.coe_mk, norm_mul, mul_pow]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]

variable {α : Type*} [MeasurableSpace α] {n : ℕ}
  (μ : Measure α) (p : α → PairSpace n) (hp : MemLp p 2 μ)

include hp in
theorem pairStackProduct_integrable (f : Lp (Space n) 2 μ) :
    Integrable (fun a => pairStackProduct (p a) (f a)) μ := by
  apply (hp.norm.integrable_mul (Lp.memLp f).norm).mono'
    ((pairStackProductCLM n).aestronglyMeasurable_comp₂ hp.aestronglyMeasurable (Lp.aestronglyMeasurable f))
  exact Filter.Eventually.of_forall fun a => (pairStackProduct_norm (p a) (f a)).le

def continuousPairStackLinear : Lp (Space n) 2 μ →ₗ[ℂ] PairStackSpace n where
  toFun f := WithLp.toLp 2 (fun aA =>
    continuousPairSynthesis μ p hp (Frame.l2Coordinate μ aA.2 f) aA.1)
  map_add' f g := by ext aA; simp
  map_smul' z f := by ext aA; simp

theorem continuousPairStackLinear_fiber (f : Lp (Space n) 2 μ) (A : Finset (Fin n)) :
    pairFiber A (continuousPairStackLinear μ p hp f) =
      continuousPairSynthesis μ p hp (Frame.l2Coordinate μ A f) := rfl

theorem continuousPairStackLinear_norm_le (f : Lp (Space n) 2 μ) :
    ‖continuousPairStackLinear μ p hp f‖ ≤ ‖continuousPairSynthesis μ p hp‖ * ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [pairStackSpace_norm_sq, mul_pow, Frame.l2Finite_norm_sq μ f, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro A _
  rw [continuousPairStackLinear_fiber, ← mul_pow]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    ((continuousPairSynthesis μ p hp).le_opNorm (Frame.l2Coordinate μ A f))

/-- S acts on the pair label and leaves the system occupation unchanged. -/
def continuousPairSynthesisStack : Lp (Space n) 2 μ →L[ℂ] PairStackSpace n :=
  (continuousPairStackLinear μ p hp).mkContinuous ‖continuousPairSynthesis μ p hp‖
    (continuousPairStackLinear_norm_le μ p hp)

theorem continuousPairSynthesisStack_fiber (f : Lp (Space n) 2 μ) (A : Finset (Fin n)) :
    pairFiber A (continuousPairSynthesisStack μ p hp f) =
      continuousPairSynthesis μ p hp (Frame.l2Coordinate μ A f) := rfl

/-- The amplification has the same raw beta bound, without a Fock-dimension factor. -/
theorem continuousPairSynthesisStack_norm_sq_le (β : ℝ) (hβ : 0 ≤ β)
    (hQ : ∀ q : PairSpace n, (inner ℂ q (continuousPairOperator μ p q)).re ≤ β * ‖q‖^2)
    (f : Lp (Space n) 2 μ) : ‖continuousPairSynthesisStack μ p hp f‖^2 ≤ β * ‖f‖^2 := by
  rw [pairStackSpace_norm_sq, Frame.l2Finite_norm_sq μ f, Finset.mul_sum]
  exact Finset.sum_le_sum fun A _ => continuousPairSynthesis_norm_sq_le μ p hp β hβ hQ
    (Frame.l2Coordinate μ A f)

/-- Actual vector-valued synthesis integral, with integrability proved above. -/
theorem continuousPairSynthesisStack_integral (f : Lp (Space n) 2 μ) :
    continuousPairSynthesisStack μ p hp f = ∫ a, pairStackProduct (p a) (f a) ∂μ := by
  haveI : CompleteSpace (PairSpace n) := PiLp.completeSpace 2 (fun _ => ℂ)
  haveI : CompleteSpace (PairStackSpace n) := PiLp.completeSpace 2 (fun _ => ℂ)
  ext ⟨i,A⟩
  change continuousPairSynthesis μ p hp (Frame.l2Coordinate μ A f) i = _
  rw [continuousPairSynthesis_apply]
  change (PiLp.proj (𝕜 := ℂ) 2 (fun _ : PairIndex n => ℂ) i)
      (∫ a, (Frame.l2Coordinate μ A f a) • p a ∂μ) =
    (PiLp.proj (𝕜 := ℂ) 2 (fun _ : PairIndex n × Finset (Fin n) => ℂ) (i,A))
      (∫ a, pairStackProduct (p a) (f a) ∂μ)
  rw [← (PiLp.proj (𝕜 := ℂ) 2 (fun _ : PairIndex n => ℂ) i).integral_comp_comm
      (continuousPairSynthesis_integrable μ p hp (Frame.l2Coordinate μ A f)),
    ← (PiLp.proj (𝕜 := ℂ) 2 (fun _ : PairIndex n × Finset (Fin n) => ℂ) (i,A)).integral_comp_comm
      (pairStackProduct_integrable μ p hp f)]
  apply integral_congr_ae
  filter_upwards [Frame.l2Coordinate_ae μ A f] with a ha
  change (Frame.l2Coordinate μ A f a) * p a i = p a i * f a A
  rw [ha, mul_comm]

end VortexGap.Fermion


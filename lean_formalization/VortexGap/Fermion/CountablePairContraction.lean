import VortexGap.Fermion.CountablePairStack

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct ComplexConjugate ENNReal

theorem countablePair_holder (p : CountablePairSpace) (z : CountablePairStackSpace) :
    (Summable (fun a => ‖p a‖ * ‖z a‖)) ∧
      (∑' a, ‖p a‖ * ‖z a‖) ≤ ‖p‖ * ‖z‖ := by
  have hp : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    simpa using Real.HolderConjugate.two_two
  have h := lp.tsum_mul_le_mul_norm hp (lp.toNorm p) (lp.toNorm z)
  simp only [lp.norm_toNorm] at h
  change (Summable (fun a => ‖‖p a‖‖ * ‖‖z a‖‖)) ∧
    (∑' a, ‖‖p a‖‖ * ‖‖z a‖‖) ≤ ‖p‖ * ‖z‖ at h
  simpa only [norm_norm] using h

theorem countablePairContract_norm_summable (p : CountablePairSpace) (z : CountablePairStackSpace) :
    Summable (fun a => ‖conj (p a) • z a‖) := by
  simpa [norm_smul] using (countablePair_holder p z).1

theorem countablePairContract_summable (p : CountablePairSpace) (z : CountablePairStackSpace) :
    Summable (fun a => conj (p a) • z a) :=
  (countablePairContract_norm_summable p z).of_norm

def countablePairContractLinear (p : CountablePairSpace) :
    CountablePairStackSpace →ₗ[ℂ] CountableSpace where
  toFun z := ∑' a, conj (p a) • z a
  map_add' z w := by
    change (∑' a, conj (p a) • (z a + w a)) = _
    simp only [smul_add]
    exact (countablePairContract_summable p z).tsum_add (countablePairContract_summable p w)
  map_smul' c z := by
    change (∑' a, conj (p a) • (c • z a)) = _
    simp_rw [smul_comm (conj _) c]
    exact (countablePairContract_summable p z).tsum_const_smul c

theorem countablePairContractLinear_norm_le (p : CountablePairSpace) (z : CountablePairStackSpace) :
    ‖countablePairContractLinear p z‖ ≤ ‖p‖ * ‖z‖ := by
  calc
    _ ≤ ∑' a, ‖conj (p a) • z a‖ := norm_tsum_le_tsum_norm (countablePairContract_norm_summable p z)
    _ ≤ _ := by simpa [norm_smul] using (countablePair_holder p z).2

/-- Contract the pair index with an arbitrary l2 pair wavefunction, conjugate-linearly. -/
def countablePairContract (p : CountablePairSpace) : CountablePairStackSpace →L[ℂ] CountableSpace :=
  (countablePairContractLinear p).mkContinuous ‖p‖ (countablePairContractLinear_norm_le p)

theorem countablePairContract_apply (p : CountablePairSpace) (z : CountablePairStackSpace) :
    countablePairContract p z = ∑' a, conj (p a) • z a := rfl

theorem countablePairContract_hasSum (p : CountablePairSpace) (z : CountablePairStackSpace) :
    HasSum (fun a => conj (p a) • z a) (countablePairContract p z) :=
  (countablePairContract_summable p z).hasSum

theorem countablePairContract_opNorm_le (p : CountablePairSpace) : ‖countablePairContract p‖ ≤ ‖p‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  exact countablePairContractLinear_norm_le p

theorem countablePairContract_add (p q : CountablePairSpace) :
    countablePairContract (p + q) = countablePairContract p + countablePairContract q := by
  apply ContinuousLinearMap.ext
  intro z
  change (∑' a, conj (p a + q a) • z a) = _
  simp only [map_add, add_smul]
  exact (countablePairContract_summable p z).tsum_add (countablePairContract_summable q z)

theorem countablePairContract_smul (c : ℂ) (p : CountablePairSpace) :
    countablePairContract (c • p) = conj c • countablePairContract p := by
  apply ContinuousLinearMap.ext
  intro z
  change (∑' a, conj (c * p a) • z a) = _
  simp only [map_mul, mul_smul]
  exact (countablePairContract_summable p z).tsum_const_smul (conj c)

theorem countablePairContract_single (a : CountablePairIndex) (c : ℂ) (z : CountablePairStackSpace) :
    countablePairContract (lp.single 2 a c) z = conj c • z a := by
  rw [countablePairContract_apply, tsum_eq_single a]
  · simp
  · intro b hba
    have hz : (lp.single 2 a c : CountablePairSpace) b = 0 :=
      lp.single_apply_ne (E := fun _ : CountablePairIndex => ℂ) 2 a c hba
    change conj ((lp.single 2 a c : CountablePairSpace) b) • (z b) = (0 : CountableSpace)
    rw [hz, map_zero]
    ext A
    change (0 : ℂ) * z b A = 0
    exact zero_mul _

end VortexGap.Fermion


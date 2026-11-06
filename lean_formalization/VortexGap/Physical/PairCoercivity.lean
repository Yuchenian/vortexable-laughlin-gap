import VortexGap.Fermion.CountableContinuousLossOutput
import Mathlib.Analysis.InnerProductSpace.StarOrder
import VortexGap.Fermion.CountablePairFilterAdjoint
import VortexGap.Fermion.CountablePairLift
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct ENNReal ComplexOrder

theorem countablePairOperator_ext_wedge
    (A B : CountablePairSpace →L[ℂ] CountablePairSpace)
    (h : ∀ u v, A (countableWedge u v) = B (countableWedge u v)) : A = B := by
  apply ContinuousLinearMap.ext
  intro p
  have hp : HasSum (fun a => p a • lp.single 2 a 1) p := by
    simpa only [← lp.single_smul, smul_eq_mul, mul_one]
      using lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) p
  have hA := hp.map A.toAddMonoidHom A.continuous
  have hB := hp.map B.toAddMonoidHom B.continuous
  have he (a : CountablePairIndex) : A (lp.single 2 a 1) = B (lp.single 2 a 1) := by
    rw [← countableWedge_basis a]
    exact h _ _
  change HasSum (fun a => A (p a • lp.single 2 a 1)) (A p) at hA
  change HasSum (fun a => B (p a • lp.single 2 a 1)) (B p) at hB
  simp only [map_smul, he] at hA
  simp only [map_smul] at hB
  exact hA.unique hB

/-- Actual exterior-square covariance, proved on a dense wedge span. -/
theorem countablePairFilter_real_smul
    (R : CountableOrbital →L[ℂ] CountableOrbital) (hR : 0 ≤ R)
    (t : ℝ) (ht : 0 ≤ t) :
    countablePairFilter ((t : ℂ) • R) (smul_nonneg (show 0 ≤ (t : ℂ) by exact_mod_cast ht) hR) =
      ((t^2 : ℝ) : ℂ) • countablePairFilter R hR := by
  apply countablePairOperator_ext_wedge
  intro u v
  rw [countablePairFilter_wedge]
  simp only [smul_apply, countablePairFilter_wedge]
  rw [countableWedge_smul_smul]
  simp [pow_two]

/-- Positive congruence preserves Loewner comparison. -/
theorem pair_congruence_mono
    (D Q W : CountablePairSpace →L[ℂ] CountablePairSpace) (h : Q ≤ W) :
    D.adjoint.comp (Q.comp D) ≤ D.adjoint.comp (W.comp D) := by
  rw [ContinuousLinearMap.le_def] at h ⊢
  simpa only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub] using h.adjoint_conj D

def filteredPairHamiltonian (N : ℕ)
    (R : CountableOrbital →L[ℂ] CountableOrbital) (hR : 0 ≤ R)
    (Q : CountablePairSpace →L[ℂ] CountablePairSpace) :
    countableSector N →L[ℂ] countableSector N :=
  countablePairLift N ((countablePairFilter R hR).adjoint.comp
    (Q.comp (countablePairFilter R hR)))

theorem filteredPairHamiltonian_positive (N : ℕ)
    (R : CountableOrbital →L[ℂ] CountableOrbital) (hR : 0 ≤ R)
    (Q : CountablePairSpace →L[ℂ] CountablePairSpace) (hQ : Q.IsPositive) :
    (filteredPairHamiltonian N R hR Q).IsPositive :=
  countablePairLift_positive N _ (hQ.adjoint_conj _)

theorem filteredPairHamiltonian_mono (N : ℕ)
    (R : CountableOrbital →L[ℂ] CountableOrbital) (hR : 0 ≤ R)
    (Q W : CountablePairSpace →L[ℂ] CountablePairSpace) (h : Q ≤ W) :
    filteredPairHamiltonian N R hR Q ≤ filteredPairHamiltonian N R hR W :=
  countablePairLift_mono N (pair_congruence_mono _ Q W h)

theorem filteredPairHamiltonian_smul (N : ℕ)
    (R : CountableOrbital →L[ℂ] CountableOrbital) (hR : 0 ≤ R)
    (Q : CountablePairSpace →L[ℂ] CountablePairSpace) (c : ℂ) :
    filteredPairHamiltonian N R hR (c • Q) = c • filteredPairHamiltonian N R hR Q := by
  simp only [filteredPairHamiltonian, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul, countablePairLift_smul]

theorem filteredPairHamiltonian_coercivity (N : ℕ)
    (R : CountableOrbital →L[ℂ] CountableOrbital) (hR : 0 ≤ R)
    (Q W : CountablePairSpace →L[ℂ] CountablePairSpace) (κ K : ℝ)
    (hlo : (κ : ℂ) • Q ≤ W) (hhi : W ≤ (K : ℂ) • Q) :
    (κ : ℂ) • filteredPairHamiltonian N R hR Q ≤ filteredPairHamiltonian N R hR W ∧
    filteredPairHamiltonian N R hR W ≤ (K : ℂ) • filteredPairHamiltonian N R hR Q := by
  constructor
  · simpa only [filteredPairHamiltonian_smul] using filteredPairHamiltonian_mono N R hR _ _ hlo
  · simpa only [filteredPairHamiltonian_smul] using filteredPairHamiltonian_mono N R hR _ _ hhi

theorem filteredPairHamiltonian_scale (N : ℕ)
    (R : CountableOrbital →L[ℂ] CountableOrbital) (hR : 0 ≤ R)
    (Q : CountablePairSpace →L[ℂ] CountablePairSpace) (t : ℝ) (ht : 0 ≤ t) :
    filteredPairHamiltonian N ((t : ℂ) • R)
      (smul_nonneg (show 0 ≤ (t : ℂ) by exact_mod_cast ht) hR) Q =
      ((t^4 : ℝ) : ℂ) • filteredPairHamiltonian N R hR Q := by
  unfold filteredPairHamiltonian
  rw [countablePairFilter_adjoint, countablePairFilter_adjoint, countablePairFilter_real_smul R hR t ht]
  simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    smul_smul, countablePairLift_smul]
  congr 1
  push_cast
  ring

theorem filteredPairHamiltonian_sqrt_scale (N : ℕ)
    (R : CountableOrbital →L[ℂ] CountableOrbital) (hR : 0 ≤ R)
    (Q : CountablePairSpace →L[ℂ] CountablePairSpace) (g : ℝ) (hg : 0 ≤ g) :
    filteredPairHamiltonian N ((Real.sqrt g : ℂ) • R)
      (smul_nonneg (show 0 ≤ (Real.sqrt g : ℂ) by exact_mod_cast Real.sqrt_nonneg g) hR) Q =
      ((g^2 : ℝ) : ℂ) • filteredPairHamiltonian N R hR Q := by
  rw [filteredPairHamiltonian_scale N R hR Q (Real.sqrt g) (Real.sqrt_nonneg g)]
  have he : (Real.sqrt g)^4 = g^2 := by
    calc
      (Real.sqrt g)^4 = ((Real.sqrt g)^2)^2 := by ring
      _ = g^2 := by rw [Real.sq_sqrt hg]
  rw [he]

/-- The g^-2 energy scale follows from the actual exterior-square construction. -/
theorem filteredPairHamiltonian_normalized_coercivity (N : ℕ)
    (R : CountableOrbital →L[ℂ] CountableOrbital) (hR : 0 ≤ R)
    (Q W : CountablePairSpace →L[ℂ] CountablePairSpace) (κ K g : ℝ) (hg : 0 < g)
    (hlo : (κ : ℂ) • Q ≤ W) (hhi : W ≤ (K : ℂ) • Q) :
    let M := (Real.sqrt g : ℂ) • R
    let hM : 0 ≤ M := smul_nonneg
      (show 0 ≤ (Real.sqrt g : ℂ) by exact_mod_cast Real.sqrt_nonneg g) hR
    (((κ/g^2 : ℝ) : ℂ) • filteredPairHamiltonian N M hM Q ≤ filteredPairHamiltonian N R hR W) ∧
    (filteredPairHamiltonian N R hR W ≤ ((K/g^2 : ℝ) : ℂ) • filteredPairHamiltonian N M hM Q) := by
  dsimp only
  have he := filteredPairHamiltonian_sqrt_scale N R hR Q g hg.le
  have hscale (c : ℝ) : ((c/g^2 : ℝ) : ℂ) •
      filteredPairHamiltonian N ((Real.sqrt g : ℂ) • R)
        (smul_nonneg (show 0 ≤ (Real.sqrt g : ℂ) by exact_mod_cast Real.sqrt_nonneg g) hR) Q =
      (c : ℂ) • filteredPairHamiltonian N R hR Q := by
    rw [he, smul_smul]
    congr 1
    have hn : (g : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hg
    push_cast
    field_simp
  rw [hscale κ, hscale K]
  exact filteredPairHamiltonian_coercivity N R hR Q W κ K hlo hhi

theorem filteredPairHamiltonian_eq_continuous
    {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    (p : α → CountablePairSpace)
    (hp : ∀ q, MeasureTheory.MemLp (fun a => inner ℂ (p a) q) 2 μ)
    (β : ℝ) (hβ : 0 ≤ β)
    (hb : ∀ q, (∫ a, ‖inner ℂ (p a) q‖^2 ∂μ) ≤ β * ‖q‖^2)
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (N : ℕ) :
    filteredPairHamiltonian N M hM (countableContinuousPairOperator μ p hp β hβ hb) =
      countableContinuousFilteredHamiltonian μ p hp β hβ hb M hM N := by
  simp only [filteredPairHamiltonian, countableContinuousFilteredHamiltonian,
    countablePairFilter_adjoint]

end VortexGap.Fermion



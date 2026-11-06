import VortexGap.Operator.QuadraticNorm
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
noncomputable section
set_option autoImplicit false
namespace VortexGap
open scoped InnerProduct ComplexOrder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Polynomial functional calculus identifies the operator inequality with a condition
on the entire real spectrum, including continuous spectrum. -/
theorem quadratic_positive_iff_spectrum_gap
    (T : H →L[ℂ] H) (hT : T.IsPositive) (γ : ℝ) :
    (T*T - (γ : ℂ) • T).IsPositive ↔
      ∀ x ∈ spectrum ℝ T, x = 0 ∨ γ ≤ x := by
  have hs : IsSelfAdjoint T := hT.isSelfAdjoint
  have hcfc : cfc (fun x : ℝ => x*x - γ*x) T = T*T - (γ : ℂ) • T := by
    rw [cfc_sub (fun x : ℝ => x*x) (fun x => γ*x) T,
      cfc_mul (fun x : ℝ => x) (fun x => x) T,
      cfc_id' ℝ T hs, cfc_const_mul_id γ T hs]
    congr 1
  rw [← ContinuousLinearMap.nonneg_iff_isPositive, ← hcfc,
    cfc_nonneg_iff (fun x : ℝ => x*x - γ*x) T (by fun_prop) hs]
  constructor
  · intro h x hx
    have hn : 0 ≤ x := spectrum_nonneg_of_nonneg
      (ContinuousLinearMap.nonneg_iff_isPositive.mpr hT) hx
    have hq := h x hx
    by_cases hz : x = 0
    · exact Or.inl hz
    · right
      have hp : 0 < x := lt_of_le_of_ne hn (Ne.symm hz)
      nlinarith
  · intro h x hx
    have hn : 0 ≤ x := spectrum_nonneg_of_nonneg
      (ContinuousLinearMap.nonneg_iff_isPositive.mpr hT) hx
    rcases h x hx with hz | hγ
    · simp [hz]
    · nlinarith [mul_nonneg hn (sub_nonneg.mpr hγ)]

theorem quadratic_gap_spectrum_excludes
    (T : H →L[ℂ] H) (hT : T.IsPositive) (γ : ℝ)
    (hg : (T*T - (γ : ℂ) • T).IsPositive) :
    Disjoint (spectrum ℝ T) (Set.Ioo 0 γ) := by
  apply Set.disjoint_left.mpr
  intro x hx hi
  rcases (quadratic_positive_iff_spectrum_gap T hT γ).mp hg x hx with hz | hγ
  · exact (ne_of_gt hi.1) hz
  · exact (not_le_of_gt hi.2) hγ
end VortexGap
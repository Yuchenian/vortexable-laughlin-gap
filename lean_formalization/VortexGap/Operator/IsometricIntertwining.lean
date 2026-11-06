import Mathlib.Analysis.InnerProductSpace.Positive
noncomputable section
set_option autoImplicit false
namespace VortexGap
open scoped InnerProduct
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem positive_of_isometric_intertwining (W : E →ₗᵢ[ℂ] F)
    (T : E →L[ℂ] E) (S : F →L[ℂ] F)
    (h : ∀ x, W (T x) = S (W x)) (hS : S.IsPositive) : T.IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff_complex T).mpr
  intro x
  have hp := (ContinuousLinearMap.isPositive_iff_complex S).mp hS (W x)
  rw [← h x, W.inner_map_map] at hp
  exact hp

theorem quadratic_positive_of_isometric_intertwining (W : E →ₗᵢ[ℂ] F)
    (T : E →L[ℂ] E) (S : F →L[ℂ] F) (γ : ℝ)
    (h : ∀ x, W (T x) = S (W x))
    (hS : (S.comp S - (γ : ℂ) • S).IsPositive) :
    (T.comp T - (γ : ℂ) • T).IsPositive := by
  apply positive_of_isometric_intertwining W _ _ _ hS
  intro x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, map_sub, map_smul, h]
end VortexGap

import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic

/-! Generic Hilbert-space compression only: no CAR or frame estimates are assumed proved here. -/
noncomputable section
set_option autoImplicit false
namespace VortexGap
open ContinuousLinearMap
open scoped InnerProduct ComplexOrder

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def quadratic (A : E →L[ℂ] E) (x : E) : ℝ := (inner ℂ x (A x)).re

theorem compression_positive (A : F →L[ℂ] F) (V : E →L[ℂ] F)
    (hA : A.IsPositive) : (V.adjoint ∘L A ∘L V).IsPositive :=
  hA.adjoint_conj V

/-- The residual is constructed from S and V, rather than supplied as a variance axiom. -/
theorem compression_gram_identity (V S : E →L[ℂ] F)
    (hV : V.adjoint ∘L V = ContinuousLinearMap.id ℂ E) :
    S.adjoint ∘L S =
      (V.adjoint ∘L S).adjoint ∘L (V.adjoint ∘L S) +
      (S - V ∘L (V.adjoint ∘L S)).adjoint ∘L (S - V ∘L (V.adjoint ∘L S)) := by
  let H := V.adjoint ∘L S
  let X := S - V ∘L H
  have cancel (A : E →L[ℂ] E) : V.adjoint ∘L (V ∘L A) = A := by
    rw [← comp_assoc, hV, id_comp]
  have hx : V.adjoint ∘L X = 0 := by
    dsimp [X, H]
    rw [comp_sub, cancel, sub_self]
  have hx' : X.adjoint ∘L V = 0 := by
    have h := congrArg (fun A : E →L[ℂ] E => A.adjoint) hx
    simpa only [adjoint_comp, adjoint_adjoint, map_zero] using h
  have hs : S = V ∘L H + X := by dsimp [X]; abel
  change S.adjoint ∘L S = H.adjoint ∘L H + X.adjoint ∘L X
  conv_lhs => rw [hs]
  simp only [map_add, adjoint_comp, add_comp, comp_add, comp_assoc]
  rw [cancel, hx, comp_zero]
  rw [← comp_assoc X.adjoint V H, hx', zero_comp]
  abel

theorem compression_variance_positive (V S : E →L[ℂ] F)
    (hV : V.adjoint ∘L V = ContinuousLinearMap.id ℂ E) :
    (S.adjoint ∘L S - (V.adjoint ∘L S).adjoint ∘L (V.adjoint ∘L S)).IsPositive := by
  rw [compression_gram_identity V S hV, add_sub_cancel_left]
  exact isPositive_adjoint_comp_self _

end VortexGap

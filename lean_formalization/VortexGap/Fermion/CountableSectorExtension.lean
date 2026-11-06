import VortexGap.Fermion.CountableSpectatorSectors
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped ComplexOrder

/-- Extend a bounded operator on an actual number sector by zero on its orthogonal complement. -/
def countableSectorExtend (N : ℕ) (T : countableSector N →L[ℂ] countableSector N) :
    CountableSpace →L[ℂ] CountableSpace :=
  (countableSector N).subtypeL.comp (T.comp (countableSector N).subtypeL.adjoint)

theorem countableSectorExtend_add (N : ℕ) (T S : countableSector N →L[ℂ] countableSector N) :
    countableSectorExtend N (T+S) = countableSectorExtend N T + countableSectorExtend N S := by
  ext x
  simp [countableSectorExtend]

theorem countableSectorExtend_sub (N : ℕ) (T S : countableSector N →L[ℂ] countableSector N) :
    countableSectorExtend N (T-S) = countableSectorExtend N T - countableSectorExtend N S := by
  ext x
  simp [countableSectorExtend]

theorem countableSectorExtend_smul (N : ℕ) (c : ℂ) (T : countableSector N →L[ℂ] countableSector N) :
    countableSectorExtend N (c • T) = c • countableSectorExtend N T := by
  ext x
  simp [countableSectorExtend]

theorem countableSectorExtend_mul (N : ℕ) (T S : countableSector N →L[ℂ] countableSector N) :
    countableSectorExtend N T * countableSectorExtend N S = countableSectorExtend N (T*S) := by
  simp only [countableSectorExtend, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]
  rw [← ContinuousLinearMap.comp_assoc (countableSector N).subtypeL.adjoint
    (countableSector N).subtypeL, countableSector_adjoint_subtype_self]
  rfl

theorem countableSectorExtend_mul_other (K L : ℕ) (hKL : K ≠ L)
    (T : countableSector K →L[ℂ] countableSector K)
    (S : countableSector L →L[ℂ] countableSector L) :
    countableSectorExtend K T * countableSectorExtend L S = 0 := by
  simp only [countableSectorExtend, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]
  rw [← ContinuousLinearMap.comp_assoc (countableSector K).subtypeL.adjoint
    (countableSector L).subtypeL, countableSector_adjoint_subtype_other K L hKL]
  simp

theorem countableSectorExtend_positive (N : ℕ) (T : countableSector N →L[ℂ] countableSector N)
    (h : T.IsPositive) : (countableSectorExtend N T).IsPositive := by
  simpa only [ContinuousLinearMap.adjoint_adjoint, countableSectorExtend] using
    h.adjoint_conj (countableSector N).subtypeL.adjoint

theorem countableSectorExtend_apply_self (N : ℕ)
    (T : countableSector N →L[ℂ] countableSector N) (x : countableSector N) :
    countableSectorExtend N T (x : CountableSpace) = (T x : CountableSpace) := by
  have h := congrArg (fun A : countableSector N →L[ℂ] countableSector N => A x)
    (countableSector_adjoint_subtype_self N)
  change (countableSector N).subtypeL.adjoint (x : CountableSpace) = x at h
  simp only [countableSectorExtend, ContinuousLinearMap.comp_apply, h]
  rfl

theorem countableSectorExtend_apply_other (K L : ℕ) (hKL : K ≠ L)
    (T : countableSector K →L[ℂ] countableSector K) (x : countableSector L) :
    countableSectorExtend K T (x : CountableSpace) = 0 := by
  have h := congrArg (fun A : countableSector L →L[ℂ] countableSector K => A x)
    (countableSector_adjoint_subtype_other K L hKL)
  change (countableSector K).subtypeL.adjoint (x : CountableSpace) = 0 at h
  simp only [countableSectorExtend, ContinuousLinearMap.comp_apply, h, map_zero]
end VortexGap.Fermion

import VortexGap.Fermion.CountableWedgeCoordinates
import VortexGap.Fermion.CountableSplitOrbitalFields
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped ComplexConjugate

/-- Fixing the second orbital gives a bounded linear exterior product. -/
def countableWedgeLeft (v : CountableOrbital) : CountableOrbital →L[ℂ] CountablePairSpace :=
  countablePairCoordinates.comp
    ((ContinuousLinearMap.apply ℂ CountableSpace
      (countableCreate v (countableKet ∅))).comp countableCreate)

/-- Fixing the first orbital gives a bounded linear exterior product. -/
def countableWedgeRight (u : CountableOrbital) : CountableOrbital →L[ℂ] CountablePairSpace :=
  countablePairCoordinates.comp ((countableCreate u).comp
    ((ContinuousLinearMap.apply ℂ CountableSpace (countableKet ∅)).comp countableCreate))

theorem countableWedgeLeft_apply (u v : CountableOrbital) :
    countableWedgeLeft v u = countableWedge u v := rfl

theorem countableWedgeRight_apply (u v : CountableOrbital) :
    countableWedgeRight u v = countableWedge u v := rfl

/-- The actual CAR pair field is continuous and conjugate-linear in its pair wave. -/
def countablePairAnnihilateWave (N : ℕ) :
    CountablePairSpace →L⋆[ℂ] (countableSector N →L[ℂ] CountableSpace) := by
  let f : CountablePairSpace →ₗ⋆[ℂ] (countableSector N →L[ℂ] CountableSpace) :=
    { toFun := countablePairAnnihilate N
      map_add' := countablePairAnnihilate_add N
      map_smul' := countablePairAnnihilate_smul N }
  exact ⟨f, AddMonoidHomClass.continuous_of_bound f (Real.sqrt (N.choose 2 : ℝ))
    (countablePairAnnihilate_opNorm_le N)⟩

theorem countablePairAnnihilateWave_apply (N : ℕ) (p : CountablePairSpace) :
    countablePairAnnihilateWave N p = countablePairAnnihilate N p := rfl
end VortexGap.Fermion

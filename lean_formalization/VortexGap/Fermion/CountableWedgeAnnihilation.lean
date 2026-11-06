import VortexGap.Fermion.CountableWedgeLinear
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion

theorem countablePairAnnihilate_wedge_kets {N : ℕ} (i j : ℕ) (x : countableSector N) :
    countablePairAnnihilate N (countableWedge (orbitalKet i) (orbitalKet j)) x =
      countableAnnihilate (orbitalKet j) (countableAnnihilate (orbitalKet i) x) := by
  have ordered (a b : ℕ) (h : a < b) :
      countablePairAnnihilate N (countableWedge (orbitalKet a) (orbitalKet b)) x =
        countableAnnihilate (orbitalKet b) (countableAnnihilate (orbitalKet a) x) := by
    rw [countableWedge_basis ⟨(a,b),h⟩, countablePairAnnihilate_single]
    simp only [map_one, one_smul, countableAnnihilate_ket, countablePairMode]
    rfl
  rcases lt_trichotomy i j with h | h | h
  · exact ordered i j h
  · subst j
    rw [countableWedge_self]
    change countablePairAnnihilateWave N 0 x = _
    rw [map_zero]
    exact (congrArg (fun T : CountableSpace →L[ℂ] CountableSpace => T x)
      (countableAnnihilate_square (orbitalKet i))).symm
  · rw [countableWedge_anticommute]
    change countablePairAnnihilateWave N (-countableWedge (orbitalKet j) (orbitalKet i)) x = _
    rw [map_neg]
    change -countablePairAnnihilate N (countableWedge (orbitalKet j) (orbitalKet i)) x = _
    rw [ordered j i h]
    exact (congrArg (fun T : CountableSpace →L[ℂ] CountableSpace => T x)
      (countableAnnihilate_anticommute (orbitalKet j) (orbitalKet i))).symm

/-- The completed pair contraction agrees with the actual ordered CAR fields,
including the vacuum and one-particle sectors. -/
theorem countablePairAnnihilate_wedge {N : ℕ} (u v : CountableOrbital)
    (x : countableSector N) :
    countablePairAnnihilate N (countableWedge u v) x =
      countableAnnihilate v (countableAnnihilate u x) := by
  let ann : CountableOrbital →L⋆[ℂ] (CountableSpace →L[ℂ] CountableSpace) :=
    ContinuousLinearMap.adjoint.toLinearIsometry.toContinuousLinearMap.comp countableCreate
  let evalPair := ContinuousLinearMap.apply ℂ CountableSpace x
  let evalField := ContinuousLinearMap.apply ℂ CountableSpace (x : CountableSpace)
  have hk (i : ℕ) (w : CountableOrbital) :
      countablePairAnnihilate N (countableWedge (orbitalKet i) w) x =
        countableAnnihilate w (countableAnnihilate (orbitalKet i) x) := by
    let L : CountableOrbital →L⋆[ℂ] CountableSpace :=
      evalPair.comp ((countablePairAnnihilateWave N).comp (countableWedgeRight (orbitalKet i)))
    let R : CountableOrbital →L⋆[ℂ] CountableSpace :=
      (ContinuousLinearMap.apply ℂ CountableSpace (countableAnnihilate (orbitalKet i) x)).comp ann
    have h : L = R := countableOrbital_antilinear_ext L R (fun j =>
      countablePairAnnihilate_wedge_kets i j x)
    exact congrArg (fun T : CountableOrbital →L⋆[ℂ] CountableSpace => T w) h
  let L : CountableOrbital →L⋆[ℂ] CountableSpace :=
    evalPair.comp ((countablePairAnnihilateWave N).comp (countableWedgeLeft v))
  let R : CountableOrbital →L⋆[ℂ] CountableSpace :=
    (countableAnnihilate v).comp (evalField.comp ann)
  have h : L = R := countableOrbital_antilinear_ext L R (fun i => hk i v)
  exact congrArg (fun T : CountableOrbital →L⋆[ℂ] CountableSpace => T u) h
end VortexGap.Fermion

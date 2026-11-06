import VortexGap.Fermion.CountableWedgeAnnihilation
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped ENNReal

theorem countablePair_antilinear_ext {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (S T : CountablePairSpace →L⋆[ℂ] E)
    (h : ∀ a, S (lp.single 2 a 1) = T (lp.single 2 a 1)) : S = T := by
  ext p
  have hp : HasSum (fun a => p a • lp.single 2 a 1) p := by
    simpa only [← lp.single_smul, smul_eq_mul, mul_one]
      using lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) p
  have hs := hp.map S.toAddMonoidHom S.continuous
  have ht := hp.map T.toAddMonoidHom T.continuous
  change HasSum (fun a => S (p a • lp.single 2 a 1)) (S p) at hs
  change HasSum (fun a => T (p a • lp.single 2 a 1)) (T p) at ht
  simp only [map_smulₛₗ, h] at hs
  simp only [map_smulₛₗ] at ht
  exact hs.unique ht

/-- Pair annihilation covaries under the concrete completed Fock isometry.
This holds for arbitrary square-summable pair waves, not only decomposable ones. -/
theorem countablePairAnnihilate_covariance
    (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital) {N : ℕ}
    (p : CountablePairSpace) (x : countableSector N) :
    countablePairAnnihilate N (countablePairMap J p)
      ⟨countableFockIsometry J x, countableFockIsometry_sector J x.property⟩ =
    countableFockIsometry J (countablePairAnnihilate N p x) := by
  let y : countableSector N :=
    ⟨countableFockIsometry J x, countableFockIsometry_sector J x.property⟩
  let L : CountablePairSpace →L⋆[ℂ] CountableSpace :=
    (ContinuousLinearMap.apply ℂ CountableSpace y).comp
      ((countablePairAnnihilateWave N).comp (countablePairMap J))
  let R : CountablePairSpace →L⋆[ℂ] CountableSpace :=
    (countableFockIsometry J).toContinuousLinearMap.comp
      ((ContinuousLinearMap.apply ℂ CountableSpace x).comp (countablePairAnnihilateWave N))
  have h : L = R := by
    apply countablePair_antilinear_ext
    intro a
    change countablePairAnnihilate N (countablePairMap J (lp.single 2 a 1)) y =
      countableFockIsometry J (countablePairAnnihilate N (lp.single 2 a 1) x)
    rw [← countableWedge_basis a, countableWedge_map,
      countablePairAnnihilate_wedge, countablePairAnnihilate_wedge,
      countableFockIsometry_annihilate, countableFockIsometry_annihilate]
  exact congrArg (fun T : CountablePairSpace →L⋆[ℂ] CountableSpace => T p) h
end VortexGap.Fermion

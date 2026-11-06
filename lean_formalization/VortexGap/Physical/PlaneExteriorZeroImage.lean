import VortexGap.Fermion.CountableFockFilter
import VortexGap.Physical.PlanePairZeroImage
import VortexGap.Physical.PlaneZeroModeFibers
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct ComplexOrder BoundedContinuousFunction

def countableExteriorFilter (N : ℕ) (M : CountableOrbital →L[ℂ] CountableOrbital)
    (hM : 0 ≤ M) : countableSector N →L[ℂ] countableSector N :=
  ((countableDegreeFilter N M hM).comp (countableSector N).subtypeL).codRestrict _
    (countableDegreeFilter_sector N M hM)

theorem countableExteriorFilter_pair (n : ℕ) (M : CountableOrbital →L[ℂ] CountableOrbital)
    (hM : 0 ≤ M) (p : CountablePairSpace) (x : countableSector (n+2)) :
    countablePairAnnihilate (n+2) p (countableExteriorFilter (n+2) M hM x) =
      countableDegreeFilter n M hM (countablePairAnnihilate (n+2) (countablePairFilter M hM p) x) := by
  let y := countableExteriorFilter (n+2) M hM x
  let L := (ContinuousLinearMap.apply ℂ CountableSpace y).comp (countablePairAnnihilateWave (n+2))
  let B := (ContinuousLinearMap.apply ℂ CountableSpace x).comp (countablePairAnnihilateWave (n+2))
  let R := (countableDegreeFilter n M hM).comp (B.comp (countablePairFilter M hM))
  have h : L = R := by
    apply countablePair_antilinear_ext
    intro a
    change countablePairAnnihilate (n+2) (lp.single 2 a 1) y =
      countableDegreeFilter n M hM (countablePairAnnihilate (n+2)
        (countablePairFilter M hM (lp.single 2 a 1)) x)
    rw [← countableWedge_basis a, countablePairFilter_wedge, countablePairAnnihilate_wedge,
      countablePairAnnihilate_wedge]
    change countableAnnihilate _ (countableAnnihilate _ (countableDegreeFilter (n+2) M hM x)) = _
    rw [countableDegreeFilter_annihilate, countableDegreeFilter_annihilate]
  exact congrArg (fun T : CountablePairSpace →L⋆[ℂ] CountableSpace => T p) h

theorem countablePairFiber_test (N : ℕ) (L : CountablePairSpace →L[ℂ] CountablePairSpace)
    (x : countableSector N) :
    (∀ A, L (countablePairFiber (countablePairStack N x) A) = 0) ↔
      ∀ p, countablePairAnnihilate N (L.adjoint p) x = 0 := by
  constructor
  · intro h p
    ext A
    change countablePairContract (L.adjoint p) (countablePairStack N x) A = 0
    rw [countablePairContract_coefficient, ContinuousLinearMap.adjoint_inner_left, h, inner_zero_right]
  · intro h A
    apply ext_inner_left ℂ
    intro p
    have hp := congrArg (fun z : CountableSpace => z A) (h p)
    change countablePairContract (L.adjoint p) (countablePairStack N x) A = 0 at hp
    rwa [countablePairContract_coefficient, ContinuousLinearMap.adjoint_inner_left,
      ← inner_zero_right (𝕜 := ℂ) p] at hp

/-- The reference pair tests on the filtered state agree with weighted pair
tests on the original state, including their full spectator space. -/
theorem countableExteriorFilter_zero_iff (N : ℕ)
    (S R : CountableOrbital →L[ℂ] CountableOrbital) (hS : 0 ≤ S) (hR : 0 ≤ R)
    (hinv : S * R = 1) (Q : CountablePairSpace →L[ℂ] CountablePairSpace) (hQ : Q.IsPositive)
    (x : countableSector N) :
    countablePairLift N Q (countableExteriorFilter N R hR x) = 0 ↔
      ∀ A, Q (countablePairFilter R hR (countablePairFiber (countablePairStack N x) A)) = 0 := by
  let D := countablePairFilter R hR
  change _ ↔ ∀ A, (Q.comp D) (countablePairFiber (countablePairStack N x) A) = 0
  rw [countablePairLift_zero_iff_fibers _ _ hQ, countablePairFiber_test, countablePairFiber_test,
    ContinuousLinearMap.adjoint_comp]
  change (∀ p, countablePairAnnihilate N (Q.adjoint p) (countableExteriorFilter N R hR x) = 0) ↔
    ∀ p, countablePairAnnihilate N ((countablePairFilter R hR).adjoint (Q.adjoint p)) x = 0
  rw [countablePairFilter_adjoint]
  apply forall_congr'
  intro p
  cases N with
  | zero => simp only [countablePairAnnihilate_zero_sector, zero_apply]
  | succ n =>
    cases n with
    | zero =>
      change countablePairAnnihilate 1 _ _ = 0 ↔ countablePairAnnihilate 1 _ _ = 0
      simp only [countablePairAnnihilate_one_sector, zero_apply]
    | succ n =>
      rw [countableExteriorFilter_pair]
      let z : countableSector n := ⟨_, countablePairAnnihilate_sector
        (countablePairFilter R hR (Q.adjoint p)) x⟩
      change countableDegreeFilter n R hR z = 0 ↔ (z : CountableSpace) = 0
      constructor
      · intro hz
        rw [← countableDegreeFilter_cancel n S R hS hR hinv z, hz, map_zero]
      · intro hz
        rw [hz, map_zero]

/-- Exact image of the reference zero modes in normalized band coordinates
on each finite-N sector of the completed planar orbital space. -/
theorem planeBandContact_zero_iff_exteriorImage (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hG : IsStrictlyPositive (planeScalarGram ell hell f)) (hf : Differentiable ℝ f)
    (κ : ℝ) (hκ : 0 < κ) (hw : (κ : ℂ) • planePairOperator ≤ planeWeightedPairOperator ell f)
    (N : ℕ) (x : countableSector N) :
    planeBandContactOperator ell hell f hG hf N x = 0 ↔
      ∃ y : countableSector N, countablePairLift N planePairOperator y = 0 ∧
        countableExteriorFilter N (gramRoot (planeScalarEmbedding ell hell f))
          (gramRoot_nonneg _) y = x := by
  let F := planeScalarEmbedding ell hell f
  let R := gramInvSqrt F
  let S := gramRoot F
  have hR : 0 ≤ R := gramInvSqrt_nonneg F hG
  have hS : 0 ≤ S := gramRoot_nonneg F
  rw [planeBandContact_zero_iff_fibers ell hell f hG hf κ hκ hw,
    ← countableExteriorFilter_zero_iff N S R hS hR (gramInvSqrt_right F hG)
      planePairOperator planePairOperator_positive]
  constructor
  · intro h
    exact ⟨_, h, Subtype.ext (countableDegreeFilter_cancel N S R hS hR (gramInvSqrt_right F hG) x)⟩
  · rintro ⟨y, hy, rfl⟩
    have he : countableExteriorFilter N R hR (countableExteriorFilter N S hS y) = y :=
      Subtype.ext (countableDegreeFilter_cancel N R S hR hS (gramInvSqrt_left F hG) y)
    change countablePairLift N planePairOperator (countableExteriorFilter N R hR (countableExteriorFilter N S hS y)) = 0
    rwa [he]

theorem planeWeakCos_zero_iff_exteriorImage (ell : ℝ) (hell : 0 < ell)
    (N : ℕ) (x : countableSector N) :
    planeWeakCosContactOperator ell hell N x = 0 ↔
      ∃ y : countableSector N, countablePairLift N planePairOperator y = 0 ∧
        countableExteriorFilter N (gramRoot (planeScalarEmbedding ell hell planeWeakCos))
          (gramRoot_nonneg _) y = x :=
  planeBandContact_zero_iff_exteriorImage ell hell planeWeakCos
    (gramOperator_strict _ ((9999/10000 : ℝ)^2) (by norm_num) (planeWeakCos_gram_bounds ell hell).1)
    planeWeakCos_differentiable ((9999/10000 : ℝ)^4) (by positivity) (planeWeakCos_coercivity ell) N x

end VortexGap.Fermion

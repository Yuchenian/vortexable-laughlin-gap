import VortexGap.Fermion.SecondQuantization

/-! Pair covariance for the actual full-Fock functor. The finite-frame identity
intertwines on the embedded Fock space; it does not supply a spectator gap. -/
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators InnerProduct ComplexConjugate

def pairCreation (n : ℕ) : PairSpace n →ₗ[ℂ] Module.End ℂ (Space n) where
  toFun := pairCreate
  map_add' := pairCreate_add
  map_smul' := pairCreate_smul

theorem fockMap_pairCreate {n m : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)) (p : PairSpace n) :
    (fockMap A).comp (pairCreate p) = (pairCreate (exteriorSquare A p)).comp (fockMap A) := by
  have hc (v : EuclideanSpace ℂ (Fin n)) (x : Space n) :
      fockMap A (create v x) = create (A v) (fockMap A x) :=
    congrArg (fun T => T x) (fockMap_create A v)
  have hb (b : PairIndex n) (x : Space n) :
      fockMap A (pairCreate (pairBasis b) x) =
        pairCreate (exteriorSquare A (pairBasis b)) (fockMap A x) := by
    rw [← wedgePair_basis b, exteriorSquare_wedge, pairCreate_wedge, pairCreate_wedge]
    simp only [Module.End.mul_apply, hc]
  apply LinearMap.ext
  intro x
  change fockMap A (pairCreation n p x) = pairCreation m (exteriorSquare A p) (fockMap A x)
  conv_lhs => rw [← pairBasis_expansion p]
  conv_rhs => rw [← pairBasis_expansion p]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Finset.sum_congr rfl fun b _ => congrArg (fun y : Space m => p b • y) (hb b x)

theorem fockMap_pairAnnihilate {n m : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)) (p : PairSpace m) :
    (pairAnnihilate p).comp (fockMap A) =
      (fockMap A).comp (pairAnnihilate (exteriorSquare A.adjoint p)) := by
  have h := congrArg (LinearMap.adjoint (𝕜 := ℂ)
    (E := Space m) (F := Space n)) (fockMap_pairCreate A.adjoint p)
  simp only [LinearMap.adjoint_comp, ← fockMap_adjoint, LinearMap.adjoint_adjoint,
    ← pairAnnihilate_adjoint] at h
  simpa only [LinearMap.adjoint_adjoint] using h

theorem fockMap_pairEmbed {n m : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)) (p : PairSpace n) :
    fockMap A (pairEmbed p) = pairEmbed (exteriorSquare A p) := by
  change fockMap A (pairSectorEmbed p : Space n) = _
  rw [fockMap_on_sector A (pairSectorEmbed p)]
  exact congrArg (fun y : particleSector m 2 => (y : Space m)) (exteriorPower_pairEmbed A p)

theorem isometry_adjoint_comp {n m : ℕ}
    (U : EuclideanSpace ℂ (Fin n) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) :
    U.toLinearMap.adjoint.comp U.toLinearMap = LinearMap.id := by
  apply LinearMap.ext
  intro v
  apply ext_inner_left ℂ
  intro w
  change inner ℂ w (U.toLinearMap.adjoint (U v)) = inner ℂ w v
  rw [LinearMap.adjoint_inner_right]
  exact U.inner_map_map w v

theorem fockMap_pairAnnihilate_isometry {n m : ℕ}
    (U : EuclideanSpace ℂ (Fin n) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) (p : PairSpace n) :
    (pairAnnihilate (exteriorSquare U.toLinearMap p)).comp (fockMap U.toLinearMap) =
      (fockMap U.toLinearMap).comp (pairAnnihilate p) := by
  rw [fockMap_pairAnnihilate]
  have he : exteriorSquare U.toLinearMap.adjoint (exteriorSquare U.toLinearMap p) = p := by
    rw [← LinearMap.comp_apply, ← exteriorSquare_comp, isometry_adjoint_comp, exteriorSquare_id,
      LinearMap.id_apply]
  rw [he]

theorem fockMap_pairInteraction {n m : ℕ}
    (U : EuclideanSpace ℂ (Fin n) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) (p : PairSpace n) :
    (pairLift (pairRankOne (exteriorSquare U.toLinearMap p))).comp (fockMap U.toLinearMap) =
      (fockMap U.toLinearMap).comp (pairLift (pairRankOne p)) := by
  rw [pairLift_rankOne, pairLift_rankOne, pairAnnihilate_adjoint, pairAnnihilate_adjoint]
  change ((pairCreate (exteriorSquare U.toLinearMap p)).comp
    (pairAnnihilate (exteriorSquare U.toLinearMap p))).comp (fockMap U.toLinearMap) =
      (fockMap U.toLinearMap).comp ((pairCreate p).comp (pairAnnihilate p))
  rw [LinearMap.comp_assoc, fockMap_pairAnnihilate_isometry, ← LinearMap.comp_assoc,
    ← fockMap_pairCreate, LinearMap.comp_assoc]

theorem fockMap_frameInteraction {n m : ℕ} {ι : Type*} [Fintype ι]
    (U : EuclideanSpace ℂ (Fin n) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m))
    (w : ι → ℝ) (p : ι → PairSpace n) :
    (pairLift (∑ i, (w i : ℂ) • pairRankOne (exteriorSquare U.toLinearMap (p i)))).comp
        (fockMap U.toLinearMap) =
      (fockMap U.toLinearMap).comp (pairLift (∑ i, (w i : ℂ) • pairRankOne (p i))) := by
  have hi (i : ι) (x : Space n) :
      pairLift (pairRankOne (exteriorSquare U.toLinearMap (p i))) (fockMap U.toLinearMap x) =
        fockMap U.toLinearMap (pairLift (pairRankOne (p i)) x) :=
    congrArg (fun T => T x) (fockMap_pairInteraction U (p i))
  apply LinearMap.ext
  intro x
  change pairLiftLinear m (∑ i, (w i : ℂ) • pairRankOne (exteriorSquare U.toLinearMap (p i)))
      (fockMap U.toLinearMap x) =
    fockMap U.toLinearMap (pairLiftLinear n (∑ i, (w i : ℂ) • pairRankOne (p i)) x)
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Finset.sum_congr rfl fun i _ => congrArg (fun y : Space m => (w i : ℂ) • y) (hi i x)

theorem fockMap_vacuum {n m : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)) :
    fockMap A (ket ∅) = ket ∅ := by
  let x : particleSector n 0 := ⟨ket ∅, sector_ket ∅⟩
  let y : particleSector m 0 := ⟨ket ∅, sector_ket ∅⟩
  have he : exteriorPower A 0 x = y := by
    apply sectorRawReadout_injective
    rw [exteriorPower_rawReadout]
    ext a
    simp [tensorPower_apply, tensorKernel, sectorRawReadout,
      OAI.LaughlinGap.Occupation.rawReadout, x, y, ket, List.ofFn_zero]
  change fockMap A (x : Space n) = (y : Space m)
  rw [fockMap_on_sector, he]

end VortexGap.Fermion

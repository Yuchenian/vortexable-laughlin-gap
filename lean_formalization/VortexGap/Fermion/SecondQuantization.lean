import VortexGap.Fermion.ContractionCovariance

/-! Concrete second quantization on the full finite-mode occupation Fock space.
All particle sectors, including the vacuum, are retained. Functor, adjoint and
CAR identities are derived for every complex one-particle linear map. -/
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators InnerProduct ComplexConjugate

/-- The actual occupation-number projection, with its range in the true sector. -/
def sectorProjection (n N : ℕ) : Space n →ₗ[ℂ] particleSector n N where
  toFun x := ⟨WithLp.toLp 2 (fun B => if B.card = N then x B else 0), by
    intro B hB
    change (if B.card = N then x B else 0) = 0
    simp [hB]⟩
  map_add' x y := by
    apply Subtype.ext
    ext B
    change (if B.card = N then (x + y) B else 0) =
      (if B.card = N then x B else 0) + (if B.card = N then y B else 0)
    split_ifs <;> simp
  map_smul' z x := by
    apply Subtype.ext
    ext B
    change (if B.card = N then (z • x) B else 0) = z * (if B.card = N then x B else 0)
    split_ifs <;> simp

theorem sectorProjection_apply {n N : ℕ} (x : Space n) (B : Finset (Fin n)) :
    (sectorProjection n N x : Space n) B = if B.card = N then x B else 0 := rfl

theorem sectorProjection_on_sector {n N : ℕ} (x : particleSector n N) :
    sectorProjection n N (x : Space n) = x := by
  apply Subtype.ext
  ext B
  rw [sectorProjection_apply]
  by_cases hB : B.card = N
  · simp [hB]
  · simp [hB, x.property B hB]

theorem sectorProjection_other {n N K : ℕ} (x : particleSector n N) (hKN : K ≠ N) :
    sectorProjection n K (x : Space n) = 0 := by
  apply Subtype.ext
  ext B
  rw [sectorProjection_apply]
  by_cases hB : B.card = K
  · have hBN : B.card ≠ N := fun h => hKN (hB.symm.trans h)
    simp [hB, x.property B hBN]
  · simp [hB]

/-- The finite full-Fock map, defined by the true degree of each output occupation. -/
def fockMap {n m : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)) : Space n →ₗ[ℂ] Space m where
  toFun x := WithLp.toLp 2 (fun B =>
    (exteriorPower A B.card (sectorProjection n B.card x) : Space m) B)
  map_add' x y := by
    ext B
    change (exteriorPower A B.card (sectorProjection n B.card (x+y)) : Space m) B = _
    rw [map_add, map_add]
    rfl
  map_smul' z x := by
    ext B
    change (exteriorPower A B.card (sectorProjection n B.card (z • x)) : Space m) B = _
    rw [map_smul, map_smul]
    rfl

theorem fockMap_apply {n m : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m))
    (x : Space n) (B : Finset (Fin m)) :
    fockMap A x B = (exteriorPower A B.card (sectorProjection n B.card x) : Space m) B := rfl

theorem fockMap_on_sector {n m N : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)) (x : particleSector n N) :
    fockMap A (x : Space n) = (exteriorPower A N x : Space m) := by
  ext B
  rw [fockMap_apply]
  by_cases hB : B.card = N
  · subst N
    rw [sectorProjection_on_sector]
  · rw [(exteriorPower A N x).property B hB, sectorProjection_other x hB, map_zero]
    rfl

theorem sectorProjection_fockMap {n m : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)) (N : ℕ) (x : Space n) :
    sectorProjection m N (fockMap A x) = exteriorPower A N (sectorProjection n N x) := by
  apply Subtype.ext
  ext B
  rw [sectorProjection_apply]
  by_cases hB : B.card = N
  · subst N
    simp [fockMap_apply]
  · simp [hB, (exteriorPower A N (sectorProjection n N x)).property B hB]

theorem fockMap_id (n : ℕ) :
    fockMap (LinearMap.id : Module.End ℂ (EuclideanSpace ℂ (Fin n))) = LinearMap.id := by
  ext x B
  simp [fockMap_apply, exteriorPower_id, sectorProjection_apply]

theorem fockMap_comp {n m l : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m))
    (B : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin l)) :
    fockMap (B.comp A) = (fockMap B).comp (fockMap A) := by
  ext x C
  simp only [LinearMap.comp_apply, fockMap_apply, sectorProjection_fockMap]
  rw [exteriorPower_comp]
  rfl

theorem occupation_expansion {n : ℕ} (x : Space n) :
    ∑ B, x B • ket B = x := by
  ext C
  simp [ket, WithLp.ofLp_sum, Finset.sum_apply, Pi.single_apply]

theorem fockMap_adjoint_ket {n m : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m))
    (B : Finset (Fin m)) (C : Finset (Fin n)) :
    inner ℂ (fockMap A.adjoint (ket B)) (ket C) =
      inner ℂ (ket B) (fockMap A (ket C)) := by
  by_cases hBC : B.card = C.card
  · let x : particleSector m B.card := ⟨ket B, sector_ket B⟩
    let y : particleSector n B.card := ⟨ket C, by rw [hBC]; exact sector_ket C⟩
    change inner ℂ (fockMap A.adjoint (x : Space m)) (y : Space n) =
      inner ℂ (x : Space m) (fockMap A (y : Space n))
    rw [fockMap_on_sector, fockMap_on_sector]
    change inner ℂ (exteriorPower A.adjoint B.card x) y =
      inner ℂ x (exteriorPower A B.card y)
    rw [exteriorPower_adjoint]
    exact LinearMap.adjoint_inner_left (𝕜 := ℂ)
      (E := particleSector n B.card) (F := particleSector m B.card) _ _ _
  · rw [fockMap_on_sector A.adjoint (⟨ket B, sector_ket B⟩ : particleSector m B.card),
      fockMap_on_sector A (⟨ket C, sector_ket C⟩ : particleSector n C.card)]
    rw [sector_orthogonal (exteriorPower A.adjoint B.card _).property (sector_ket C) hBC,
      sector_orthogonal (sector_ket B) (exteriorPower A C.card _).property hBC]

theorem fockMap_adjoint {n m : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)) :
    fockMap A.adjoint = (fockMap A).adjoint := by
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  rw [← occupation_expansion x, ← occupation_expansion y]
  simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    fockMap_adjoint_ket]

theorem fockMap_isometry_inner {n m : ℕ}
    (U : EuclideanSpace ℂ (Fin n) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m))
    (x y : Space n) :
    inner ℂ (fockMap U.toLinearMap x) (fockMap U.toLinearMap y) = inner ℂ x y := by
  have hu : U.toLinearMap.adjoint.comp U.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro v
    apply ext_inner_left ℂ
    intro w
    change inner ℂ w (U.toLinearMap.adjoint (U v)) = inner ℂ w v
    rw [LinearMap.adjoint_inner_right]
    exact U.inner_map_map w v
  rw [← LinearMap.adjoint_inner_right, ← fockMap_adjoint]
  change inner ℂ x (((fockMap U.toLinearMap.adjoint).comp (fockMap U.toLinearMap)) y) = _
  rw [← fockMap_comp, hu, fockMap_id, LinearMap.id_apply]

def fockIsometry {n m : ℕ}
    (U : EuclideanSpace ℂ (Fin n) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) : Space n →ₗᵢ[ℂ] Space m where
  toLinearMap := fockMap U.toLinearMap
  norm_map' := (LinearMap.norm_map_iff_inner_map_map _).mpr (fockMap_isometry_inner U)

/-- The concrete full-Fock unitary induced by a one-particle unitary. -/
def fockEquiv {n m : ℕ}
    (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) : Space n ≃ₗᵢ[ℂ] Space m where
  toFun := fockMap U.toLinearEquiv.toLinearMap
  map_add' := map_add (fockMap U.toLinearEquiv.toLinearMap)
  map_smul' := map_smul (fockMap U.toLinearEquiv.toLinearMap)
  norm_map' := (fockIsometry U.toLinearIsometry).norm_map
  invFun := fockMap U.symm.toLinearEquiv.toLinearMap
  left_inv x := by
    have hU : U.symm.toLinearEquiv.toLinearMap.comp U.toLinearEquiv.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      exact U.symm_apply_apply
    change fockMap U.symm.toLinearEquiv.toLinearMap (fockMap U.toLinearEquiv.toLinearMap x) = x
    rw [← LinearMap.comp_apply, ← fockMap_comp, hU, fockMap_id, LinearMap.id_apply]
  right_inv x := by
    have hU : U.toLinearEquiv.toLinearMap.comp U.symm.toLinearEquiv.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      exact U.apply_symm_apply
    change fockMap U.toLinearEquiv.toLinearMap (fockMap U.symm.toLinearEquiv.toLinearMap x) = x
    rw [← LinearMap.comp_apply, ← fockMap_comp, hU, fockMap_id, LinearMap.id_apply]

theorem fockEquiv_apply {n m : ℕ}
    (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) (x : Space n) :
    fockEquiv U x = fockMap U.toLinearEquiv.toLinearMap x := rfl

theorem fockMap_create {n m : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m))
    (v : EuclideanSpace ℂ (Fin n)) :
    (fockMap A).comp (create v) = (create (A v)).comp (fockMap A) := by
  have hket (B : Finset (Fin n)) : fockMap A (create v (ket B)) = create (A v) (fockMap A (ket B)) := by
    let x : particleSector n B.card := ⟨ket B, sector_ket B⟩
    change fockMap A (createSector B.card v x : Space n) = create (A v) (fockMap A (x : Space n))
    rw [fockMap_on_sector, fockMap_on_sector]
    exact congrArg (fun y : particleSector m (B.card+1) => (y : Space m)) (exteriorPower_create A v x)
  apply LinearMap.ext
  intro x
  rw [← occupation_expansion x]
  simp only [LinearMap.comp_apply, map_sum, map_smul, hket]

theorem fockMap_annihilate {n m : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m))
    (v : EuclideanSpace ℂ (Fin m)) :
    (annihilate v).comp (fockMap A) = (fockMap A).comp (annihilate (A.adjoint v)) := by
  have h := congrArg (LinearMap.adjoint (𝕜 := ℂ)
    (E := Space m) (F := Space n)) (fockMap_create A.adjoint v)
  simp only [LinearMap.adjoint_comp, ← fockMap_adjoint, LinearMap.adjoint_adjoint,
    ← annihilate_adjoint] at h
  simpa only [LinearMap.adjoint_adjoint] using h

end VortexGap.Fermion

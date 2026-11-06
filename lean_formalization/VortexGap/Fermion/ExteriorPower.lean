import VortexGap.Fermion.TensorPower

/-! Arbitrary-degree exterior action on the actual occupation Hilbert sectors.
The action is transported from the proved antisymmetric tensor restriction.
CAR covariance and full-Fock assembly are separate obligations. -/
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion

def antisymmetricPower {n m : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)) (N : ℕ) :
    antisymmetricTensors n N →ₗ[ℂ] antisymmetricTensors m N where
  toFun ψ := ⟨tensorPower A N ψ, tensorPower_preserves_antisymmetric A ψ.property⟩
  map_add' ψ φ := Subtype.ext (map_add (tensorPower A N) (ψ : TensorSpace n N) (φ : TensorSpace n N))
  map_smul' z ψ := Subtype.ext (map_smul (tensorPower A N) z (ψ : TensorSpace n N))

theorem antisymmetricPower_id (n N : ℕ) :
    antisymmetricPower (LinearMap.id : Module.End ℂ (EuclideanSpace ℂ (Fin n))) N =
      LinearMap.id := by
  apply LinearMap.ext
  intro ψ
  apply Subtype.ext
  change tensorPower LinearMap.id N (ψ : TensorSpace n N) = (ψ : TensorSpace n N)
  rw [tensorPower_id, LinearMap.id_apply]

theorem antisymmetricPower_comp {n m l : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m))
    (B : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin l)) (N : ℕ) :
    antisymmetricPower (B.comp A) N = (antisymmetricPower B N).comp (antisymmetricPower A N) := by
  apply LinearMap.ext
  intro ψ
  apply Subtype.ext
  exact congrArg (fun T => T (ψ : TensorSpace n N)) (tensorPower_comp A B N)

def antisymmetricPowerIsometry {n m : ℕ}
    (U : EuclideanSpace ℂ (Fin n) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) (N : ℕ) :
    antisymmetricTensors n N →ₗᵢ[ℂ] antisymmetricTensors m N where
  toLinearMap := antisymmetricPower U.toLinearMap N
  norm_map' ψ := (tensorPowerIsometry U N).norm_map (ψ : TensorSpace n N)

/-- Transport the actual tensor action to the actual occupation N-sector. -/
def exteriorPower {n m : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)) (N : ℕ) :
    particleSector n N →ₗ[ℂ] particleSector m N :=
  (sectorTensorIsometry m N).symm.toLinearEquiv.toLinearMap ∘ₗ
    (antisymmetricPower A N) ∘ₗ (sectorTensorIsometry n N).toLinearEquiv.toLinearMap

theorem exteriorPower_tensor {n m : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)) (N : ℕ)
    (x : particleSector n N) :
    sectorTensorIsometry m N (exteriorPower A N x) =
      antisymmetricPower A N (sectorTensorIsometry n N x) := by
  change (sectorTensorIsometry m N) ((sectorTensorIsometry m N).symm _) = _
  exact (sectorTensorIsometry m N).apply_symm_apply _

theorem exteriorPower_id (n N : ℕ) :
    exteriorPower (LinearMap.id : Module.End ℂ (EuclideanSpace ℂ (Fin n))) N =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply (sectorTensorIsometry n N).injective
  rw [exteriorPower_tensor, antisymmetricPower_id]
  rfl

theorem exteriorPower_comp {n m l : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m))
    (B : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin l)) (N : ℕ) :
    exteriorPower (B.comp A) N = (exteriorPower B N).comp (exteriorPower A N) := by
  apply LinearMap.ext
  intro x
  change exteriorPower (B.comp A) N x = exteriorPower B N (exteriorPower A N x)
  apply (sectorTensorIsometry l N).injective
  rw [exteriorPower_tensor, exteriorPower_tensor, exteriorPower_tensor, antisymmetricPower_comp]
  rfl

def exteriorPowerIsometry {n m : ℕ}
    (U : EuclideanSpace ℂ (Fin n) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) (N : ℕ) :
    particleSector n N →ₗᵢ[ℂ] particleSector m N :=
  (sectorTensorIsometry m N).symm.toLinearIsometry.comp
    ((antisymmetricPowerIsometry U N).comp (sectorTensorIsometry n N).toLinearIsometry)

theorem exteriorPowerIsometry_apply {n m : ℕ}
    (U : EuclideanSpace ℂ (Fin n) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) (N : ℕ)
    (x : particleSector n N) :
    exteriorPowerIsometry U N x = exteriorPower U.toLinearMap N x := rfl

theorem exteriorPower_norm {n m : ℕ}
    (U : EuclideanSpace ℂ (Fin n) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) (N : ℕ)
    (x : particleSector n N) :
    ‖exteriorPower U.toLinearMap N x‖ = ‖x‖ :=
  (exteriorPowerIsometry U N).norm_map x

/-- Every one-particle unitary induces a unitary on the complete actual N-sector. -/
def exteriorPowerEquiv {n m : ℕ}
    (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) (N : ℕ) :
    particleSector n N ≃ₗᵢ[ℂ] particleSector m N where
  toFun := exteriorPower U.toLinearEquiv.toLinearMap N
  map_add' := map_add (exteriorPower U.toLinearEquiv.toLinearMap N)
  map_smul' := map_smul (exteriorPower U.toLinearEquiv.toLinearMap N)
  norm_map' := exteriorPower_norm U.toLinearIsometry N
  invFun := exteriorPower U.symm.toLinearEquiv.toLinearMap N
  left_inv x := by
    have hU : U.symm.toLinearEquiv.toLinearMap.comp U.toLinearEquiv.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro v
      exact U.symm_apply_apply v
    change exteriorPower U.symm.toLinearEquiv.toLinearMap N
      (exteriorPower U.toLinearEquiv.toLinearMap N x) = x
    rw [← LinearMap.comp_apply, ← exteriorPower_comp, hU, exteriorPower_id, LinearMap.id_apply]
  right_inv x := by
    have hU : U.toLinearEquiv.toLinearMap.comp U.symm.toLinearEquiv.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro v
      exact U.apply_symm_apply v
    change exteriorPower U.toLinearEquiv.toLinearMap N
      (exteriorPower U.symm.toLinearEquiv.toLinearMap N x) = x
    rw [← LinearMap.comp_apply, ← exteriorPower_comp, hU, exteriorPower_id, LinearMap.id_apply]

theorem exteriorPowerEquiv_apply {n m : ℕ}
    (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) (N : ℕ)
    (x : particleSector n N) :
    exteriorPowerEquiv U N x = exteriorPower U.toLinearEquiv.toLinearMap N x := rfl

end VortexGap.Fermion

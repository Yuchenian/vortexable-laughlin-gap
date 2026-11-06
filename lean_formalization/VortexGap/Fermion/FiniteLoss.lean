import VortexGap.Fermion.Spectator
import VortexGap.Operator.LossDefect

/-! The CFC loss dilation transported to the finite orbital coordinates used by CAR,
then second-quantized on the full occupation Fock space. -/
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators InnerProduct ComplexOrder

/-- Finite orbital coordinates, with the environment block first. -/
def orbitalSplit (n m : ℕ) : EuclideanSpace ℂ (Fin (n+m)) ≃ₗᵢ[ℂ]
    WithLp 2 (EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin m)) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ finSumFinEquiv.symm).trans
    (PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℂ) 2 (fun _ : Fin n ⊕ Fin m => ℂ))

theorem orbitalSplit_fst {n m : ℕ} (x : EuclideanSpace ℂ (Fin (n+m))) (i : Fin n) :
    (orbitalSplit n m x).fst i = x (Fin.castAdd m i) := rfl

theorem orbitalSplit_snd {n m : ℕ} (x : EuclideanSpace ℂ (Fin (n+m))) (i : Fin m) :
    (orbitalSplit n m x).snd i = x (Fin.natAdd n i) := rfl

def orbitalEnv (n m : ℕ) : EuclideanSpace ℂ (Fin n) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (n+m)) where
  toFun v := (orbitalSplit n m).symm (WithLp.toLp 2 (v,0))
  map_add' v w := by
    change (orbitalSplit n m).symm (WithLp.toLp 2 (v+w,0)) = _
    rw [← map_add]
    apply congrArg (orbitalSplit n m).symm
    apply WithLp.ofLp_injective 2
    simp
  map_smul' z v := by
    change (orbitalSplit n m).symm (WithLp.toLp 2 (z • v,0)) = _
    rw [← map_smul]
    apply congrArg (orbitalSplit n m).symm
    apply WithLp.ofLp_injective 2
    simp
  norm_map' v := by
    change ‖(orbitalSplit n m).symm (WithLp.toLp 2 (v,0))‖ = ‖v‖
    rw [(orbitalSplit n m).symm.norm_map]
    simp

def orbitalSys (n m : ℕ) : EuclideanSpace ℂ (Fin m) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (n+m)) where
  toFun v := (orbitalSplit n m).symm (WithLp.toLp 2 (0,v))
  map_add' v w := by
    change (orbitalSplit n m).symm (WithLp.toLp 2 (0,v+w)) = _
    rw [← map_add]
    apply congrArg (orbitalSplit n m).symm
    apply WithLp.ofLp_injective 2
    simp
  map_smul' z v := by
    change (orbitalSplit n m).symm (WithLp.toLp 2 (0,z • v)) = _
    rw [← map_smul]
    apply congrArg (orbitalSplit n m).symm
    apply WithLp.ofLp_injective 2
    simp
  norm_map' v := by
    change ‖(orbitalSplit n m).symm (WithLp.toLp 2 (0,v))‖ = ‖v‖
    rw [(orbitalSplit n m).symm.norm_map]
    simp

theorem orbitalSplit_env {n m : ℕ} (v : EuclideanSpace ℂ (Fin n)) :
    orbitalSplit n m (orbitalEnv n m v) = WithLp.toLp 2 (v,0) :=
  (orbitalSplit n m).apply_symm_apply _

theorem orbitalSplit_sys {n m : ℕ} (v : EuclideanSpace ℂ (Fin m)) :
    orbitalSplit n m (orbitalSys n m v) = WithLp.toLp 2 (0,v) :=
  (orbitalSplit n m).apply_symm_apply _

theorem orbitalEnv_left {n m : ℕ} (v : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    orbitalEnv n m v (Fin.castAdd m i) = v i := by
  rw [← orbitalSplit_fst, orbitalSplit_env]
  rfl

theorem orbitalEnv_right {n m : ℕ} (v : EuclideanSpace ℂ (Fin n)) (i : Fin m) :
    orbitalEnv n m v (Fin.natAdd n i) = 0 := by
  rw [← orbitalSplit_snd, orbitalSplit_env]
  rfl

theorem orbitalSys_left {n m : ℕ} (v : EuclideanSpace ℂ (Fin m)) (i : Fin n) :
    orbitalSys n m v (Fin.castAdd m i) = 0 := by
  rw [← orbitalSplit_fst, orbitalSplit_sys]
  rfl

theorem orbitalSys_right {n m : ℕ} (v : EuclideanSpace ℂ (Fin m)) (i : Fin m) :
    orbitalSys n m v (Fin.natAdd n i) = v i := by
  rw [← orbitalSplit_snd, orbitalSplit_sys]
  rfl

theorem orbitalSplit_pair {n m : ℕ} (u : EuclideanSpace ℂ (Fin n)) (v : EuclideanSpace ℂ (Fin m)) :
    (orbitalSplit n m).symm (WithLp.toLp 2 (u,v)) = orbitalEnv n m u + orbitalSys n m v := by
  apply (orbitalSplit n m).injective
  rw [(orbitalSplit n m).apply_symm_apply, map_add, orbitalSplit_env, orbitalSplit_sys]
  apply WithLp.ofLp_injective 2
  simp

/-- The CFC-constructed loss unitary in the same finite coordinates as CAR. -/
def finiteLossRotation {n : ℕ} (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) : EuclideanSpace ℂ (Fin (n+n)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (n+n)) :=
  ((orbitalSplit n n).trans (lossRotation M hM hc)).trans (orbitalSplit n n).symm

def finiteLossEmbedding {n : ℕ} (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) : EuclideanSpace ℂ (Fin n) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (n+n)) :=
  (orbitalSplit n n).symm.toLinearIsometry.comp (lossEmbedding M hM hc)

theorem finiteLossRotation_split {n : ℕ} (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) (x : EuclideanSpace ℂ (Fin (n+n))) :
    orbitalSplit n n (finiteLossRotation M hM hc x) = lossRotation M hM hc (orbitalSplit n n x) :=
  (orbitalSplit n n).apply_symm_apply _

theorem finiteLossEmbedding_apply {n : ℕ} (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) (v : EuclideanSpace ℂ (Fin n)) :
    finiteLossEmbedding M hM hc v = orbitalEnv n n (lossDefect M v) + orbitalSys n n (M v) :=
  orbitalSplit_pair _ _

theorem finiteLossRotation_env {n : ℕ} (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) (v : EuclideanSpace ℂ (Fin n)) :
    finiteLossRotation M hM hc (orbitalEnv n n v) = finiteLossEmbedding M hM hc v := by
  change (orbitalSplit n n).symm (lossRotation M hM hc (orbitalSplit n n (orbitalEnv n n v))) = _
  rw [orbitalSplit_env, lossRotation_first_axis]
  rfl

theorem finiteLossRotation_involutive {n : ℕ}
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) :
    Function.Involutive (finiteLossRotation M hM hc) := by
  intro x
  apply (orbitalSplit n n).injective
  rw [finiteLossRotation_split, finiteLossRotation_split]
  exact lossRotation_involutive M hM hc _

/-- Genuine full-Fock unitary induced by the constructed loss rotation. -/
def finiteLossFock {n : ℕ} (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) : Space (n+n) ≃ₗᵢ[ℂ] Space (n+n) :=
  fockEquiv (finiteLossRotation M hM hc)

theorem fockMap_preserves_sector {n m N : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m))
    {x : Space n} (hx : InSector N x) : InSector N (fockMap A x) := by
  have he := fockMap_on_sector A (⟨x,hx⟩ : particleSector n N)
  rw [he]
  exact (exteriorPower A N ⟨x,hx⟩).property

theorem finiteLossFock_sector {n N : ℕ} (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) {x : Space (n+n)} (hx : InSector N x) :
    InSector N (finiteLossFock M hM hc x) :=
  fockMap_preserves_sector (finiteLossRotation M hM hc).toLinearEquiv.toLinearMap hx

theorem finiteLossFock_involutive {n : ℕ}
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) :
    Function.Involutive (finiteLossFock M hM hc) := by
  let A := (finiteLossRotation M hM hc).toLinearEquiv.toLinearMap
  have he : A.comp A = LinearMap.id := by
    apply LinearMap.ext
    exact finiteLossRotation_involutive M hM hc
  intro x
  change fockMap A (fockMap A x) = x
  rw [← LinearMap.comp_apply, ← fockMap_comp, he, fockMap_id, LinearMap.id_apply]

theorem finiteLossFock_create {n : ℕ} (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) (v : EuclideanSpace ℂ (Fin n)) (x : Space (n+n)) :
    finiteLossFock M hM hc (create (orbitalEnv n n v) x) =
      create (finiteLossEmbedding M hM hc v) (finiteLossFock M hM hc x) := by
  have h := congrArg (fun T => T x)
    (fockMap_create (finiteLossRotation M hM hc).toLinearEquiv.toLinearMap (orbitalEnv n n v))
  change finiteLossFock M hM hc (create (orbitalEnv n n v) x) =
    create (finiteLossRotation M hM hc (orbitalEnv n n v)) (finiteLossFock M hM hc x) at h
  rw [finiteLossRotation_env] at h
  exact h

end VortexGap.Fermion

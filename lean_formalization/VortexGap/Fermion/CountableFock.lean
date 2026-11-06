import VortexGap.Fermion.CountableOccupationImages
import Mathlib.Analysis.InnerProductSpace.l2Space

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open Filter
open scoped InnerProduct

theorem countableIsometry_orbitals_orthonormal
    (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital) :
    Orthonormal ℂ (fun j => J (orbitalKet j)) := by
  apply orthonormal_iff_ite.mpr
  intro i j
  rw [J.inner_map_map]
  exact orthonormal_iff_ite.mp orbitalKet_orthonormal i j

/-- Second quantization constructed from the proved orthonormal creation-word images.
The one-particle isometry need not be onto. -/
def countableFockIsometry (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital) :
    CountableSpace →ₗᵢ[ℂ] CountableSpace :=
  (countableOccupationImage_orthonormal (fun j => J (orbitalKet j))
    (countableIsometry_orbitals_orthonormal J)).orthogonalFamily.linearIsometry

theorem countableFockIsometry_ket (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital)
    (A : Finset ℕ) :
    countableFockIsometry J (countableKet A) =
      countableOccupationImage (fun j => J (orbitalKet j)) A := by
  rw [countableFockIsometry, countableKet, OrthogonalFamily.linearIsometry_apply_single,
    LinearIsometry.toSpanSingleton_apply, one_smul]

theorem countableFockIsometry_hasSum (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital)
    (x : CountableSpace) :
    HasSum (fun A => x A • countableOccupationImage (fun j => J (orbitalKet j)) A)
      (countableFockIsometry J x) := by
  have h := (countableSpace_hasSum x).map
    (countableFockIsometry J).toContinuousLinearMap.toAddMonoidHom
    (countableFockIsometry J).continuous
  change HasSum (fun A => countableFockIsometry J (x A • countableKet A))
    (countableFockIsometry J x) at h
  simpa only [map_smul, countableFockIsometry_ket] using h

theorem countableFockIsometry_norm (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital)
    (x : CountableSpace) : ‖countableFockIsometry J x‖ = ‖x‖ :=
  (countableFockIsometry J).norm_map x

theorem countableFockIsometry_inner (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital)
    (x y : CountableSpace) :
    inner ℂ (countableFockIsometry J x) (countableFockIsometry J y) = inner ℂ x y :=
  (countableFockIsometry J).inner_map_map x y

theorem countableFockIsometry_vacuum (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital) :
    countableFockIsometry J (countableKet ∅) = countableKet ∅ := by
  rw [countableFockIsometry_ket, countableOccupationImage_empty]

theorem countableFockIsometry_sector (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital)
    {N : ℕ} {x : CountableSpace} (hx : x ∈ countableSector N) :
    countableFockIsometry J x ∈ countableSector N := by
  apply (countableSector_isClosed N).mem_of_tendsto (countableFockIsometry_hasSum J x)
  apply Eventually.of_forall
  intro s
  apply (countableSector N).sum_mem
  intro A hA
  by_cases hc : A.card = N
  · exact (countableSector N).smul_mem (x A)
      (hc ▸ countableOccupationImage_sector (fun j => J (orbitalKet j)) A)
  · rw [hx A hc, zero_smul]
    exact (countableSector N).zero_mem

def countableFockSector (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital) (N : ℕ) :
    countableSector N →ₗᵢ[ℂ] countableSector N where
  toFun x := ⟨countableFockIsometry J x, countableFockIsometry_sector J x.property⟩
  map_add' x y := Subtype.ext ((countableFockIsometry J).map_add x y)
  map_smul' c x := Subtype.ext ((countableFockIsometry J).map_smul c x)
  norm_map' x := (countableFockIsometry J).norm_map x

theorem countableFockSector_apply (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital)
    (N : ℕ) (x : countableSector N) :
    (countableFockSector J N x : CountableSpace) = countableFockIsometry J x := rfl

theorem countableFockSector_norm (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital)
    (N : ℕ) (x : countableSector N) : ‖countableFockSector J N x‖ = ‖x‖ :=
  (countableFockSector J N).norm_map x

/-- Equality on every occupation ket determines a bounded map on the entire completion. -/
theorem countableSpace_clm_ext {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (A B : CountableSpace →L[ℂ] F)
    (h : ∀ S, A (countableKet S) = B (countableKet S)) : A = B := by
  apply ContinuousLinearMap.ext
  intro x
  have hA : HasSum (fun S => x S • B (countableKet S)) (A x) := by
    have ht := (countableSpace_hasSum x).map A.toAddMonoidHom A.continuous
    change HasSum (fun S => A (x S • countableKet S)) (A x) at ht
    simpa only [map_smul, h] using ht
  have hB : HasSum (fun S => x S • B (countableKet S)) (B x) := by
    have ht := (countableSpace_hasSum x).map B.toAddMonoidHom B.continuous
    change HasSum (fun S => B (x S • countableKet S)) (B x) at ht
    simpa only [map_smul] using ht
  exact hA.unique hB

theorem countableFockIsometry_id :
    countableFockIsometry (LinearIsometry.id : CountableOrbital →ₗᵢ[ℂ] CountableOrbital) =
      (LinearIsometry.id : CountableSpace →ₗᵢ[ℂ] CountableSpace) := by
  have h := countableSpace_clm_ext
    (countableFockIsometry (LinearIsometry.id : CountableOrbital →ₗᵢ[ℂ] CountableOrbital)).toContinuousLinearMap
    (ContinuousLinearMap.id ℂ CountableSpace) (fun A => by
      change countableFockIsometry (LinearIsometry.id : CountableOrbital →ₗᵢ[ℂ] CountableOrbital) (countableKet A) =
        countableKet A
      rw [countableFockIsometry_ket]
      exact countableOccupationImage_orbitalKet A)
  apply LinearIsometry.ext
  intro x
  exact congrArg (fun T : CountableSpace →L[ℂ] CountableSpace => T x) h

theorem countableFockIsometry_adjoint_self
    (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital) :
    (countableFockIsometry J).toContinuousLinearMap.adjoint.comp
      (countableFockIsometry J).toContinuousLinearMap = 1 :=
  (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp (countableFockIsometry J).norm_map

theorem countableFockIsometry_coefficient (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital)
    (A : Finset ℕ) (x : CountableSpace) :
    inner ℂ (countableOccupationImage (fun j => J (orbitalKet j)) A)
      (countableFockIsometry J x) = x A := by
  rw [← countableFockIsometry_ket, countableFockIsometry_inner, countableKet_inner_left]

end VortexGap.Fermion

import VortexGap.Fermion.CountableFock
import VortexGap.Fermion.CountableCreationRules

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators InnerProduct ComplexConjugate

theorem countableFockIsometry_createMode_map
    (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital) (j : ℕ) :
    (countableFockIsometry J).toContinuousLinearMap.comp (countableCreateMode j) =
      (countableCreate (J (orbitalKet j))).comp
        (countableFockIsometry J).toContinuousLinearMap := by
  apply countableSpace_clm_ext
  intro A
  change countableFockIsometry J (countableCreateMode j (countableKet A)) =
    countableCreate (J (orbitalKet j)) (countableFockIsometry J (countableKet A))
  rw [countableFockIsometry_ket]
  by_cases hj : j ∈ A
  · rw [countableCreateMode_ket_of_mem j A hj, map_zero,
      countableCreate_image_of_mem (fun k => J (orbitalKet k)) j A hj]
  · rw [countableCreateMode_ket j A hj, map_smul, countableFockIsometry_ket,
      countableCreate_image_of_not_mem (fun k => J (orbitalKet k)) j A hj]

theorem countableFockIsometry_createMode
    (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital) (j : ℕ) (x : CountableSpace) :
    countableFockIsometry J (countableCreateMode j x) =
      countableCreate (J (orbitalKet j)) (countableFockIsometry J x) :=
  congrArg (fun T : CountableSpace →L[ℂ] CountableSpace => T x)
    (countableFockIsometry_createMode_map J j)

/-- Annihilation covariance is proved on occupation kets, including for non-surjective J. -/
theorem countableFockIsometry_annihilateMode_map
    (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital) (j : ℕ) :
    (countableFockIsometry J).toContinuousLinearMap.comp (countableAnnihilateMode j) =
      (countableAnnihilate (J (orbitalKet j))).comp
        (countableFockIsometry J).toContinuousLinearMap := by
  apply countableSpace_clm_ext
  intro A
  change countableFockIsometry J (countableAnnihilateMode j (countableKet A)) =
    countableAnnihilate (J (orbitalKet j)) (countableFockIsometry J (countableKet A))
  rw [countableFockIsometry_ket]
  by_cases hj : j ∈ A
  · rw [countableAnnihilateMode_ket j A hj, map_smul, countableFockIsometry_ket,
      countableAnnihilate_image_of_mem (fun k => J (orbitalKet k))
        (countableIsometry_orbitals_orthonormal J) j A hj]
  · rw [countableAnnihilateMode_ket_of_not_mem j A hj, map_zero,
      countableAnnihilate_image_of_not_mem (fun k => J (orbitalKet k))
        (countableIsometry_orbitals_orthonormal J) j A hj]

theorem countableFockIsometry_annihilateMode
    (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital) (j : ℕ) (x : CountableSpace) :
    countableFockIsometry J (countableAnnihilateMode j x) =
      countableAnnihilate (J (orbitalKet j)) (countableFockIsometry J x) :=
  congrArg (fun T : CountableSpace →L[ℂ] CountableSpace => T x)
    (countableFockIsometry_annihilateMode_map J j)

theorem countableFockIsometry_create
    (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital) (v : CountableOrbital) (x : CountableSpace) :
    countableFockIsometry J (countableCreate v x) =
      countableCreate (J v) (countableFockIsometry J x) := by
  refine orbitalEmbed_dense.induction_on v ?_ ?_
  · apply isClosed_eq <;> fun_prop
  · intro a
    have hJ : J (orbitalEmbed a) = ∑ j ∈ a.support, a j • J (orbitalKet j) := by
      change J (∑ j ∈ a.support, a j • orbitalKet j) = _
      simp only [map_sum, map_smul]
    rw [countableCreate_embed, finiteOrbitalCreate_sum, hJ]
    simp only [map_sum, sum_apply, map_smul, ContinuousLinearMap.smul_apply,
      countableFockIsometry_createMode]

theorem countableAnnihilate_sum {ι : Type*} (s : Finset ι) (v : ι → CountableOrbital) :
    countableAnnihilate (∑ j ∈ s, v j) = ∑ j ∈ s, countableAnnihilate (v j) := by
  simp only [countableAnnihilate, map_sum]

theorem countableFockIsometry_annihilate
    (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital) (v : CountableOrbital) (x : CountableSpace) :
    countableFockIsometry J (countableAnnihilate v x) =
      countableAnnihilate (J v) (countableFockIsometry J x) := by
  refine orbitalEmbed_dense.induction_on v ?_ ?_
  · apply isClosed_eq <;> fun_prop
  · intro a
    have hJ : J (orbitalEmbed a) = ∑ j ∈ a.support, a j • J (orbitalKet j) := by
      change J (∑ j ∈ a.support, a j • orbitalKet j) = _
      simp only [map_sum, map_smul]
    rw [countableAnnihilate_embed, finiteOrbitalAnnihilate_sum, hJ]
    simp only [countableAnnihilate_sum, countableAnnihilate_smul, map_sum, sum_apply,
      map_smul, ContinuousLinearMap.smul_apply, countableFockIsometry_annihilateMode]

theorem countableFockIsometry_create_map
    (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital) (v : CountableOrbital) :
    (countableFockIsometry J).toContinuousLinearMap.comp (countableCreate v) =
      (countableCreate (J v)).comp (countableFockIsometry J).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  exact countableFockIsometry_create J v

theorem countableFockIsometry_annihilate_map
    (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital) (v : CountableOrbital) :
    (countableFockIsometry J).toContinuousLinearMap.comp (countableAnnihilate v) =
      (countableAnnihilate (J v)).comp (countableFockIsometry J).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  exact countableFockIsometry_annihilate J v

theorem countableFockIsometry_word
    (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital)
    (v : ℕ → CountableOrbital) (js : List ℕ) :
    countableFockIsometry J (countableWord v js) = countableWord (fun j => J (v j)) js := by
  induction js with
  | nil => exact countableFockIsometry_vacuum J
  | cons j js ih => rw [countableWord_cons, countableFockIsometry_create, ih, countableWord_cons]

theorem countableFockIsometry_occupationImage
    (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital) (v : ℕ → CountableOrbital) (A : Finset ℕ) :
    countableFockIsometry J (countableOccupationImage v A) =
      countableOccupationImage (fun j => J (v j)) A :=
  countableFockIsometry_word J v (A.sort (· ≤ ·))

end VortexGap.Fermion

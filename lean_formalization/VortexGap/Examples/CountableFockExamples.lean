import VortexGap.Fermion.CountableParity
import VortexGap.Fermion.CountableFockPullback
import VortexGap.Examples.CountablePairs

noncomputable section
set_option autoImplicit false
namespace VortexGap.Examples
open Fermion
open scoped InnerProduct

theorem shiftedOrbitals_orthonormal : Orthonormal ℂ (fun j : ℕ => orbitalKet (j + 1)) := by
  apply orthonormal_iff_ite.mpr
  intro i j
  rw [orthonormal_iff_ite.mp orbitalKet_orthonormal (i + 1) (j + 1)]
  simp

/-- A proper one-particle isometric embedding, with range orthogonal to e_0. -/
def shiftOrbital : CountableOrbital →ₗᵢ[ℂ] CountableOrbital :=
  shiftedOrbitals_orthonormal.orthogonalFamily.linearIsometry

theorem shiftOrbital_ket (j : ℕ) : shiftOrbital (orbitalKet j) = orbitalKet (j + 1) := by
  rw [shiftOrbital, orbitalKet, OrthogonalFamily.linearIsometry_apply_single,
    LinearIsometry.toSpanSingleton_apply, one_smul]

theorem shiftOrbital_hasSum (v : CountableOrbital) :
    HasSum (fun j => v j • orbitalKet (j + 1)) (shiftOrbital v) := by
  have h := (orbital_hasSum v).map shiftOrbital.toContinuousLinearMap.toAddMonoidHom
    shiftOrbital.continuous
  change HasSum (fun j => shiftOrbital (v j • orbitalKet j)) (shiftOrbital v) at h
  simpa only [map_smul, shiftOrbital_ket] using h

theorem shiftOrbital_zero_coordinate (v : CountableOrbital) : shiftOrbital v 0 = 0 := by
  have hs := (shiftOrbital_hasSum v).map
    (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 0).toAddMonoidHom
    (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 0).continuous
  change HasSum (fun j => (v j • orbitalKet (j + 1)) 0) (shiftOrbital v 0) at hs
  have ht (j : ℕ) : (v j • orbitalKet (j + 1)) 0 = 0 := by
    simp [lp.coeFn_smul, orbitalKet, lp.single_apply]
  simp only [ht] at hs
  exact hs.unique hasSum_zero

theorem shiftOrbital_succ_coordinate (v : CountableOrbital) (j : ℕ) :
    shiftOrbital v (j + 1) = v j := by
  calc
    _ = inner ℂ (orbitalKet (j + 1)) (shiftOrbital v) := (orbitalKet_inner_left _ _).symm
    _ = inner ℂ (shiftOrbital (orbitalKet j)) (shiftOrbital v) := by rw [shiftOrbital_ket]
    _ = inner ℂ (orbitalKet j) v := shiftOrbital.inner_map_map _ _
    _ = _ := orbitalKet_inner_left j v

theorem shiftOrbital_not_surjective : ¬ Function.Surjective shiftOrbital := by
  intro h
  obtain ⟨v, hv⟩ := h (orbitalKet 0)
  have hz := shiftOrbital_zero_coordinate v
  rw [hv] at hz
  norm_num [orbitalKet, lp.single_apply] at hz

theorem shiftFock_pair :
    countableFockIsometry shiftOrbital (countableKet {0, 1}) = countableKet {1, 2} := by
  have hp : countableKet {0, 1} =
      countableCreate (orbitalKet 0) (countableCreate (orbitalKet 1) (countableKet ∅)) := by
    rw [countableCreate_ket, countableCreate_ket,
      countableCreateMode_ket 1 ∅ (by simp), Finset.insert_empty, map_smul,
      countableCreateMode_ket 0 {1} (by simp)]
    norm_num [countableSign, Finset.filter_singleton]
  rw [hp, countableFockIsometry_create, countableFockIsometry_create, countableFockIsometry_vacuum,
    shiftOrbital_ket, shiftOrbital_ket, countableCreate_ket, countableCreate_ket,
    countableCreateMode_ket 2 ∅ (by simp), Finset.insert_empty, map_smul,
    countableCreateMode_ket 1 {2} (by simp)]
  norm_num [countableSign, Finset.filter_singleton]

theorem createVacuum_singleton_coefficient (v : CountableOrbital) (j : ℕ) :
    countableCreate v (countableKet ∅) {j} = v j := by
  have hk : countableCreate (orbitalKet j) (countableKet ∅) = countableKet {j} := by
    rw [← countableOccupationImage_singleton orbitalKet j, countableOccupationImage_orbitalKet]
  rw [← countableKet_inner_left {j} (countableCreate v (countableKet ∅)), ← hk,
    countableCreate_inner, countableAnnihilate_create_vacuum, inner_smul_right,
    orbitalKet_inner_left, countableKet_inner]
  simp

def shiftedGeometricState : CountableSpace := countableFockIsometry shiftOrbital geometricOneParticle

theorem shiftedGeometricState_norm_sq : ‖shiftedGeometricState‖ ^ 2 = (4 / 3 : ℝ) := by
  rw [shiftedGeometricState, countableFockIsometry_norm, geometricOneParticle_norm_sq]

theorem shiftedGeometricState_coefficient (j : ℕ) :
    shiftedGeometricState {j + 1} = (Complex.I / 2 : ℂ)^j := by
  rw [shiftedGeometricState, geometricOneParticle, countableFockIsometry_create,
    countableFockIsometry_vacuum, createVacuum_singleton_coefficient,
    shiftOrbital_succ_coordinate, geometricOrbital_coefficient]

theorem shiftedGeometricState_coefficient_ne_zero (j : ℕ) :
    shiftedGeometricState {j + 1} ≠ 0 := by
  rw [shiftedGeometricState_coefficient]
  exact pow_ne_zero j (by norm_num)

theorem shiftedGeometricState_annihilate_zero :
    countableAnnihilate (orbitalKet 0) shiftedGeometricState = 0 := by
  rw [shiftedGeometricState, geometricOneParticle, countableFockIsometry_create,
    countableFockIsometry_vacuum, countableAnnihilate_create_vacuum,
    orbitalKet_inner_left, shiftOrbital_zero_coordinate, zero_smul]

theorem shiftedGeometricState_annihilate_one :
    countableAnnihilate (orbitalKet 1) shiftedGeometricState = countableKet ∅ := by
  rw [shiftedGeometricState, geometricOneParticle, countableFockIsometry_create,
    countableFockIsometry_vacuum, countableAnnihilate_create_vacuum, orbitalKet_inner_left]
  change shiftOrbital geometricOrbital (0 + 1) • countableKet ∅ = _
  rw [shiftOrbital_succ_coordinate, geometricOrbital_coefficient, pow_zero, one_smul]

def phaseOrbitalEquiv : CountableOrbital ≃ₗᵢ[ℂ] CountableOrbital where
  toFun v := Complex.I • v
  invFun v := (-Complex.I) • v
  map_add' v w := smul_add Complex.I v w
  map_smul' c v := smul_comm Complex.I c v
  norm_map' v := by
    change ‖Complex.I • v‖ = ‖v‖
    rw [norm_smul, Complex.norm_I, one_mul]
  left_inv v := by norm_num [smul_smul, neg_mul, ← pow_two]
  right_inv v := by norm_num [smul_smul, mul_neg, ← pow_two]

theorem phaseOrbitalEquiv_isometry :
    phaseOrbitalEquiv.toLinearIsometry = countablePhaseOrbital Complex.I (by norm_num) := by
  apply LinearIsometry.ext
  intro v
  rfl

theorem geometricPair_phase_unitary :
    countableFockEquiv phaseOrbitalEquiv geometricPairState = -geometricPairState := by
  rw [countableFockEquiv_apply, phaseOrbitalEquiv_isometry,
    countableFock_phase_sector Complex.I (by norm_num) geometricPairState_sector,
    Complex.I_sq, neg_one_smul]

theorem shiftedPhase_pair :
    countableFockIsometry (shiftOrbital.comp phaseOrbitalEquiv.toLinearIsometry)
      (countableKet {0, 1}) = -countableKet {1, 2} := by
  rw [countableFockIsometry_comp_apply, phaseOrbitalEquiv_isometry, countableFock_phase_ket]
  have hc : ({0, 1} : Finset ℕ).card = 2 := by decide
  rw [hc, Complex.I_sq, neg_one_smul, map_neg, shiftFock_pair]

theorem countableParity_three_particles :
    countableParity (countableKet {0, 1, 2}) = -countableKet {0, 1, 2} := by
  rw [countableParity_sector (countableKet_sector {0, 1, 2})]
  norm_num

theorem countableParity_geometric_pair :
    countableParity geometricPairState = geometricPairState := by
  rw [countableParity_sector geometricPairState_sector]
  norm_num


theorem phase_conjugate_geometric_annihilation :
    countableFockEquiv phaseOrbitalEquiv
      (countableAnnihilate geometricOrbital
        ((countableFockEquiv phaseOrbitalEquiv).symm geometricOneParticle)) =
      (-Complex.I * (4 / 3 : ℂ)) • countableKet ∅ := by
  rw [countableFockEquiv_conjugate_annihilate]
  change countableAnnihilate (Complex.I • geometricOrbital)
    (countableCreate geometricOrbital (countableKet ∅)) = _
  rw [countableAnnihilate_smul, smul_apply, countableAnnihilate_create_vacuum,
    inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, geometricOrbital_norm_sq,
    Complex.conj_I, smul_smul]
  norm_num

end VortexGap.Examples

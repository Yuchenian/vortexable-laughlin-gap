import VortexGap.Fermion.CountableFockFunctor

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators ComplexConjugate

theorem countableWord_smul (z : ℂ) (v : ℕ → CountableOrbital) (js : List ℕ) :
    countableWord (fun j => z • v j) js = z ^ js.length • countableWord v js := by
  induction js with
  | nil => simp only [countableWord_nil, List.length_nil, pow_zero, one_smul]
  | cons j js ih =>
      simp only [countableWord_cons, map_smul, smul_apply, ih, smul_smul, List.length_cons, pow_succ]

theorem countableOccupationImage_smul (z : ℂ) (v : ℕ → CountableOrbital) (A : Finset ℕ) :
    countableOccupationImage (fun j => z • v j) A =
      z ^ A.card • countableOccupationImage v A := by
  simpa only [countableOccupationImage, Finset.length_sort] using
    countableWord_smul z v (A.sort (· ≤ ·))

def countablePhaseOrbital (z : ℂ) (hz : ‖z‖ = 1) :
    CountableOrbital →ₗᵢ[ℂ] CountableOrbital where
  toLinearMap := z • LinearMap.id
  norm_map' x := by
    change ‖z • x‖ = ‖x‖
    rw [norm_smul, hz, one_mul]

theorem countablePhaseOrbital_apply (z : ℂ) (hz : ‖z‖ = 1) (v : CountableOrbital) :
    countablePhaseOrbital z hz v = z • v := rfl

theorem countableFock_phase_ket (z : ℂ) (hz : ‖z‖ = 1) (A : Finset ℕ) :
    countableFockIsometry (countablePhaseOrbital z hz) (countableKet A) =
      z ^ A.card • countableKet A := by
  rw [countableFockIsometry_ket]
  change countableOccupationImage (fun j => z • orbitalKet j) A = _
  rw [countableOccupationImage_smul, countableOccupationImage_orbitalKet]

theorem countableFock_phase_sector (z : ℂ) (hz : ‖z‖ = 1) {N : ℕ}
    {x : CountableSpace} (hx : x ∈ countableSector N) :
    countableFockIsometry (countablePhaseOrbital z hz) x = z ^ N • x := by
  have ht (A : Finset ℕ) :
      countableFockIsometry (countablePhaseOrbital z hz) (x A • countableKet A) =
        z ^ N • (x A • countableKet A) := by
    rw [map_smul, countableFock_phase_ket]
    by_cases hc : A.card = N
    · rw [hc]
      exact smul_comm (x A) (z ^ N) (countableKet A)
    · rw [hx A hc, zero_smul, zero_smul, smul_zero]
  have hs := (countableSpace_hasSum x).map
    (countableFockIsometry (countablePhaseOrbital z hz)).toContinuousLinearMap.toAddMonoidHom
    (countableFockIsometry (countablePhaseOrbital z hz)).continuous
  change HasSum (fun A => countableFockIsometry (countablePhaseOrbital z hz) (x A • countableKet A))
    (countableFockIsometry (countablePhaseOrbital z hz) x) at hs
  simp only [ht] at hs
  exact hs.unique ((countableSpace_hasSum x).const_smul (z ^ N))

/-- Actual fermion parity on the completed countable-mode Fock space. -/
def countableParity : CountableSpace →L[ℂ] CountableSpace :=
  (countableFockIsometry (countablePhaseOrbital (-1) (by norm_num))).toContinuousLinearMap

theorem countableParity_sector {N : ℕ} {x : CountableSpace}
    (hx : x ∈ countableSector N) : countableParity x = (-1 : ℂ)^N • x :=
  countableFock_phase_sector (-1) (by norm_num) hx

theorem countableParity_norm (x : CountableSpace) : ‖countableParity x‖ = ‖x‖ :=
  countableFockIsometry_norm _ x

theorem countableParity_vacuum : countableParity (countableKet ∅) = countableKet ∅ :=
  countableFockIsometry_vacuum _

theorem countableParity_square : countableParity.comp countableParity = 1 := by
  apply countableSpace_clm_ext
  intro A
  change countableParity (countableParity (countableKet A)) = countableKet A
  rw [countableParity_sector (countableKet_sector A), map_smul,
    countableParity_sector (countableKet_sector A), smul_smul, ← mul_pow]
  norm_num

theorem countableParity_adjoint : countableParity.adjoint = countableParity := by
  have hi : countableParity.adjoint.comp countableParity = 1 :=
    countableFockIsometry_adjoint_self _
  calc
    _ = countableParity.adjoint.comp (countableParity.comp countableParity) := by
      rw [countableParity_square]
      rfl
    _ = (countableParity.adjoint.comp countableParity).comp countableParity := rfl
    _ = _ := by rw [hi]; rfl

theorem countableParity_create (v : CountableOrbital) (x : CountableSpace) :
    countableParity (countableCreate v x) = -(countableCreate v (countableParity x)) := by
  change countableFockIsometry (countablePhaseOrbital (-1) _) (countableCreate v x) = _
  rw [countableFockIsometry_create, countablePhaseOrbital_apply, map_smul, smul_apply,
    neg_one_smul]
  rfl

theorem countableParity_annihilate (v : CountableOrbital) (x : CountableSpace) :
    countableParity (countableAnnihilate v x) = -(countableAnnihilate v (countableParity x)) := by
  change countableFockIsometry (countablePhaseOrbital (-1) _) (countableAnnihilate v x) = _
  rw [countableFockIsometry_annihilate, countablePhaseOrbital_apply,
    countableAnnihilate_smul, smul_apply]
  simp only [map_neg, map_one, neg_one_smul]
  rfl

end VortexGap.Fermion

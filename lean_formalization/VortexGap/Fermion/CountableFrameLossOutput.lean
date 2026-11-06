import VortexGap.Fermion.CountableRankOneLossOutput
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators ComplexOrder InnerProduct

/-- Weighted decomposable pair operator; weights are kept explicit. -/
def countableFramePair {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (u v : ι → CountableOrbital) : CountablePairSpace →L[ℂ] CountablePairSpace :=
  ∑ i ∈ s, a i • InnerProductSpace.rankOne ℂ (countableWedge (u i) (v i))
    (countableWedge (u i) (v i))

/-- One-environment amplitude, summed before taking its norm. -/
def countableFrameNoiseOne {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (M : CountableOrbital →L[ℂ] CountableOrbital) (u v : ι → CountableOrbital)
    (N : ℕ) : countableSector N →L[ℂ] CountableSpace :=
  ∑ i ∈ s, a i • (countableLossCreationOne M (u i) (v i)).comp
    (countablePairAnnihilate N (countableWedge (M (u i)) (M (v i))))

def countableFrameNoiseTwo {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (M : CountableOrbital →L[ℂ] CountableOrbital) (u v : ι → CountableOrbital)
    (N : ℕ) : countableSector N →L[ℂ] CountableSpace :=
  ∑ i ∈ s, a i • (countableLossCreationTwo M (u i) (v i)).comp
    (countablePairAnnihilate N (countableWedge (M (u i)) (M (v i))))

theorem countablePairConjugate_smul (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital)
    (c : ℂ) (Q : CountablePairSpace →L[ℂ] CountablePairSpace) :
    countablePairConjugate J (c • Q) = c • countablePairConjugate J Q := by
  ext p
  simp [countablePairConjugate]

/-- Actual finite-frame Hamiltonian output, including all cross-column amplitudes.
No normalization or positivity of weights is needed for this algebraic identity. -/
theorem countableLoss_frame_output {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    (u v : ι → CountableOrbital) {N : ℕ} (x : countableSector (N+2)) :
    (countablePairLift (N+2)
      (countablePairConjugate (countableLossEmbedding M hM hc) (countableFramePair s a u v))
      (countableFockSector countableSysOrbital (N+2) x) : CountableSpace) =
    countableFockIsometry countableSysOrbital
      (countablePairLift (N+2) (countableFramePair s a (fun i => M (u i)) (fun i => M (v i))) x) +
    countableFrameNoiseOne s a M u v (N+2) x +
    countableFrameNoiseTwo s a M u v (N+2) x := by
  simp only [countableFramePair, countableFrameNoiseOne, countableFrameNoiseTwo,
    countablePairConjugate_sum, countablePairConjugate_smul,
    countablePairLift_sum, countablePairLift_smul,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, Submodule.coe_sum, Submodule.coe_smul,
    map_sum, map_smul, countableLoss_rankOne_output, smul_add, Finset.sum_add_distrib]
theorem countableFrameNoiseOne_sector {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (M : CountableOrbital →L[ℂ] CountableOrbital) (u v : ι → CountableOrbital)
    (N : ℕ) (x : countableSector N) :
    countableFockSplit (countableFrameNoiseOne s a M u v N x) ∈ countableEnvironmentSector 1 := by
  simp only [countableFrameNoiseOne, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, map_sum, map_smul]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
    (countableLossCreationOne_sector M (u i) (v i) _)

theorem countableFrameNoiseTwo_sector {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (M : CountableOrbital →L[ℂ] CountableOrbital) (u v : ι → CountableOrbital)
    (N : ℕ) (x : countableSector N) :
    countableFockSplit (countableFrameNoiseTwo s a M u v N x) ∈ countableEnvironmentSector 2 := by
  simp only [countableFrameNoiseTwo, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, map_sum, map_smul]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
    (countableLossCreationTwo_sector M (u i) (v i) _)

theorem countableLoss_frame_output_norm_sq {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    (u v : ι → CountableOrbital) {N : ℕ} (x : countableSector (N+2)) :
    ‖(countablePairLift (N+2)
      (countablePairConjugate (countableLossEmbedding M hM hc) (countableFramePair s a u v))
      (countableFockSector countableSysOrbital (N+2) x) : CountableSpace)‖^2 =
    ‖(countablePairLift (N+2)
      (countableFramePair s a (fun i => M (u i)) (fun i => M (v i))) x : CountableSpace)‖^2 +
    ‖countableFrameNoiseOne s a M u v (N+2) x‖^2 +
    ‖countableFrameNoiseTwo s a M u v (N+2) x‖^2 := by
  let z : CountableSpace := countableFockIsometry countableSysOrbital
    (countablePairLift (N+2)
      (countableFramePair s a (fun i => M (u i)) (fun i => M (v i))) x)
  have h0 : countableFockSplit z ∈ countableEnvironmentSector 0 := by
    dsimp [z]
    rw [countableFockSplit_system]
    exact countableVacuumTensor_environment _
  have h1 := countableFrameNoiseOne_sector s a M u v (N+2) x
  have h2 := countableFrameNoiseTwo_sector s a M u v (N+2) x
  have h01 : inner ℂ z (countableFrameNoiseOne s a M u v (N+2) x) = 0 := by
    rw [← countableFockSplit.inner_map_map]
    exact countableEnvironmentSector_orthogonal h0 h1 (by decide)
  have h02 : inner ℂ z (countableFrameNoiseTwo s a M u v (N+2) x) = 0 := by
    rw [← countableFockSplit.inner_map_map]
    exact countableEnvironmentSector_orthogonal h0 h2 (by decide)
  have h12 : inner ℂ (countableFrameNoiseOne s a M u v (N+2) x)
      (countableFrameNoiseTwo s a M u v (N+2) x) = 0 := by
    rw [← countableFockSplit.inner_map_map]
    exact countableEnvironmentSector_orthogonal h1 h2 (by decide)
  rw [countableLoss_frame_output]
  change ‖z + _ + _‖^2 = _
  simp only [pow_two]
  rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) _ _ (by
      rw [inner_add_left, h02, h12, add_zero]),
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) _ _ h01]
  simp only [z, (countableFockIsometry countableSysOrbital).norm_map]
end VortexGap.Fermion

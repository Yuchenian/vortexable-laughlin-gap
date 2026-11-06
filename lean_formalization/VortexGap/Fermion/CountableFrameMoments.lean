import VortexGap.Frame.CountableTwoNoise
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators InnerProduct ComplexOrder

theorem countableFrameNoise_system_orthogonal {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (M : CountableOrbital →L[ℂ] CountableOrbital) (u v : ι → CountableOrbital)
    (N : ℕ) (x : CountableSpace) (y : countableSector N) :
    inner ℂ (countableFockIsometry countableSysOrbital x)
      (countableFrameNoiseOne s a M u v N y) = 0 ∧
    inner ℂ (countableFockIsometry countableSysOrbital x)
      (countableFrameNoiseTwo s a M u v N y) = 0 := by
  have h0 : countableFockSplit (countableFockIsometry countableSysOrbital x) ∈
      countableEnvironmentSector 0 := by
    rw [countableFockSplit_system]
    exact countableVacuumTensor_environment _
  constructor
  · rw [← countableFockSplit.inner_map_map]
    exact countableEnvironmentSector_orthogonal h0
      (countableFrameNoiseOne_sector s a M u v N y) (by decide)
  · rw [← countableFockSplit.inner_map_map]
    exact countableEnvironmentSector_orthogonal h0
      (countableFrameNoiseTwo_sector s a M u v N y) (by decide)

theorem countableFrameNoise_cross_orthogonal {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (M : CountableOrbital →L[ℂ] CountableOrbital) (u v : ι → CountableOrbital)
    (N : ℕ) (x y : countableSector N) :
    inner ℂ (countableFrameNoiseOne s a M u v N x)
      (countableFrameNoiseTwo s a M u v N y) = 0 := by
  rw [← countableFockSplit.inner_map_map]
  exact countableEnvironmentSector_orthogonal
    (countableFrameNoiseOne_sector s a M u v N x)
    (countableFrameNoiseTwo_sector s a M u v N y) (by decide)

/-- The actual first vacuum matrix element, for arbitrary bra and ket. -/
theorem countableLoss_frame_firstMoment {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    (u v : ι → CountableOrbital) {N : ℕ} (x y : countableSector (N+2)) :
    inner ℂ (countableFockIsometry countableSysOrbital (x : CountableSpace))
      (countablePairLift (N+2)
        (countablePairConjugate (countableLossEmbedding M hM hc) (countableFramePair s a u v))
        (countableFockSector countableSysOrbital (N+2) y) : CountableSpace) =
    inner ℂ x (countablePairLift (N+2)
      (countableFramePair s a (fun i => M (u i)) (fun i => M (v i))) y) := by
  obtain ⟨h1,h2⟩ := countableFrameNoise_system_orthogonal s a M u v (N+2) x y
  rw [countableLoss_frame_output, inner_add_right, inner_add_right, h1, h2, add_zero, add_zero,
    (countableFockIsometry countableSysOrbital).inner_map_map]
  rfl

/-- Bilinear second-moment identity, retaining interference among all frame columns. -/
theorem countableLoss_frame_secondMoment {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    (u v : ι → CountableOrbital) {N : ℕ} (x y : countableSector (N+2)) :
    inner ℂ
      (countablePairLift (N+2)
        (countablePairConjugate (countableLossEmbedding M hM hc) (countableFramePair s a u v))
        (countableFockSector countableSysOrbital (N+2) x) : CountableSpace)
      (countablePairLift (N+2)
        (countablePairConjugate (countableLossEmbedding M hM hc) (countableFramePair s a u v))
        (countableFockSector countableSysOrbital (N+2) y) : CountableSpace) =
    inner ℂ
      (countablePairLift (N+2) (countableFramePair s a (fun i => M (u i)) (fun i => M (v i))) x)
      (countablePairLift (N+2) (countableFramePair s a (fun i => M (u i)) (fun i => M (v i))) y) +
    inner ℂ (countableFrameNoiseOne s a M u v (N+2) x)
      (countableFrameNoiseOne s a M u v (N+2) y) +
    inner ℂ (countableFrameNoiseTwo s a M u v (N+2) x)
      (countableFrameNoiseTwo s a M u v (N+2) y) := by
  let H := countablePairLift (N+2) (countableFramePair s a (fun i => M (u i)) (fun i => M (v i)))
  obtain ⟨h01,h02⟩ := countableFrameNoise_system_orthogonal s a M u v (N+2) (H x) y
  obtain ⟨h10,h20⟩ := countableFrameNoise_system_orthogonal s a M u v (N+2) (H y) x
  have h10' := (inner_eq_zero_symm (𝕜 := ℂ)).mp h10
  have h20' := (inner_eq_zero_symm (𝕜 := ℂ)).mp h20
  have h12 := countableFrameNoise_cross_orthogonal s a M u v (N+2) x y
  have h21 := (inner_eq_zero_symm (𝕜 := ℂ)).mp
    (countableFrameNoise_cross_orthogonal s a M u v (N+2) y x)
  rw [countableLoss_frame_output, countableLoss_frame_output]
  change inner ℂ (countableFockIsometry countableSysOrbital (H x) + _ + _)
    (countableFockIsometry countableSysOrbital (H y) + _ + _) = _
  simp only [inner_add_left, inner_add_right, h01, h02, h10', h20', h12, h21,
    zero_add, add_zero, (countableFockIsometry countableSysOrbital).inner_map_map]
  rfl
end VortexGap.Fermion

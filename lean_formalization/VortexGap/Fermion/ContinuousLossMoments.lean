import VortexGap.Fermion.ContinuousLossReference

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory
open scoped InnerProduct ENNReal ComplexOrder

/-- Compression by the already constructed CAR environment-vacuum inclusion. -/
def continuousVacuumCompression (n : ℕ) (H : Space (n+n) →L[ℂ] Space (n+n)) :
    Space n →L[ℂ] Space n :=
  (lossVacuum n).toContinuousLinearMap.adjoint.comp (H.comp (lossVacuum n).toContinuousLinearMap)

theorem continuousVacuumCompression_inner {n : ℕ}
    (H : Space (n+n) →L[ℂ] Space (n+n)) (x y : Space n) :
    inner ℂ x (continuousVacuumCompression n H y) =
      inner ℂ (lossVacuum n x) (H (lossVacuum n y)) := by
  exact ContinuousLinearMap.adjoint_inner_right (lossVacuum n).toContinuousLinearMap x
    (H ((lossVacuum n).toContinuousLinearMap y))

variable {n : ℕ}
  (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
  (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
  {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
  (u v : α → EuclideanSpace ℂ (Fin n))
  (hu : AEStronglyMeasurable u μ) (hv : AEStronglyMeasurable v μ)
  (hun : ∀ a, ‖u a‖ ≤ 1) (hvn : ∀ a, ‖v a‖ ≤ 1)

include hu hv hun hvn in
/-- Exact continuous first moment of the concrete loss Hamiltonian. -/
theorem continuous_loss_first_moment :
    continuousVacuumCompression n
      (continuousLossHamiltonian M hM hc μ (fun a => wedgePair (u a) (v a))) =
      continuousFrameHamiltonian μ (fun a => exteriorSquare M.toLinearMap (wedgePair (u a) (v a))) := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  rw [continuousVacuumCompression_inner, ← (fockSplit n n).inner_map_map,
    continuous_loss_vacuum M μ u v hu hv hun hvn hM hc]
  simp only [lossVacuum_apply, (fockSplit n n).apply_symm_apply, inner_add_right, environmentVacuum_inner]
  rw [environmentSector_orthogonal (environmentVacuum_environmentSector x)
      (continuousOneLossNoise_sector M μ u v hu hv hun hvn y) (by decide),
    environmentSector_orthogonal (environmentVacuum_environmentSector x)
      (continuousTwoLossNoise_sector M μ _ (wedgePair_memLp μ u v hu hv hun hvn) y) (by decide)]
  simp

include hu hv hun hvn in
/-- Sesquilinear orthogonal-output identity for the literal continuous CAR operators. -/
theorem continuous_loss_output_inner (x y : Space n) :
    inner ℂ
      (fockSplit n n (continuousLossHamiltonian M hM hc μ (fun a => wedgePair (u a) (v a)) (lossVacuum n x)))
      (fockSplit n n (continuousLossHamiltonian M hM hc μ (fun a => wedgePair (u a) (v a)) (lossVacuum n y))) =
    inner ℂ (continuousFrameHamiltonian μ (fun a => exteriorSquare M.toLinearMap (wedgePair (u a) (v a))) x)
      (continuousFrameHamiltonian μ (fun a => exteriorSquare M.toLinearMap (wedgePair (u a) (v a))) y) +
      inner ℂ (continuousOneLossNoise M μ u v x) (continuousOneLossNoise M μ u v y) +
      inner ℂ (continuousTwoLossNoise M μ (fun a => wedgePair (u a) (v a)) x)
        (continuousTwoLossNoise M μ (fun a => wedgePair (u a) (v a)) y) := by
  have hp := wedgePair_memLp μ u v hu hv hun hvn
  have h01 (a b : Space n) : inner ℂ (environmentVacuum n n a) (continuousOneLossNoise M μ u v b) = 0 :=
    environmentSector_orthogonal (environmentVacuum_environmentSector a)
      (continuousOneLossNoise_sector M μ u v hu hv hun hvn b) (by decide)
  have h02 (a b : Space n) : inner ℂ (environmentVacuum n n a)
      (continuousTwoLossNoise M μ (fun i => wedgePair (u i) (v i)) b) = 0 :=
    environmentSector_orthogonal (environmentVacuum_environmentSector a)
      (continuousTwoLossNoise_sector M μ _ hp b) (by decide)
  have h10 (a b : Space n) : inner ℂ (continuousOneLossNoise M μ u v a) (environmentVacuum n n b) = 0 :=
    environmentSector_orthogonal (continuousOneLossNoise_sector M μ u v hu hv hun hvn a)
      (environmentVacuum_environmentSector b) (by decide)
  have h12 (a b : Space n) : inner ℂ (continuousOneLossNoise M μ u v a)
      (continuousTwoLossNoise M μ (fun i => wedgePair (u i) (v i)) b) = 0 :=
    environmentSector_orthogonal (continuousOneLossNoise_sector M μ u v hu hv hun hvn a)
      (continuousTwoLossNoise_sector M μ _ hp b) (by decide)
  have h20 (a b : Space n) : inner ℂ (continuousTwoLossNoise M μ (fun i => wedgePair (u i) (v i)) a)
      (environmentVacuum n n b) = 0 :=
    environmentSector_orthogonal (continuousTwoLossNoise_sector M μ _ hp a)
      (environmentVacuum_environmentSector b) (by decide)
  have h21 (a b : Space n) : inner ℂ (continuousTwoLossNoise M μ (fun i => wedgePair (u i) (v i)) a)
      (continuousOneLossNoise M μ u v b) = 0 :=
    environmentSector_orthogonal (continuousTwoLossNoise_sector M μ _ hp a)
      (continuousOneLossNoise_sector M μ u v hu hv hun hvn b) (by decide)
  simp only [continuous_loss_vacuum M μ u v hu hv hun hvn hM hc,
    inner_add_left, inner_add_right, h01, h02, h10, h12, h20, h21,
    environmentVacuum_inner, add_zero, zero_add]

include hu hv hun hvn in
/-- Exact second moment with X1 and X2 already defined as actual CAR integrals. -/
theorem continuous_loss_second_moment :
    continuousVacuumCompression n
      (continuousLossHamiltonian M hM hc μ (fun a => wedgePair (u a) (v a)) *
        continuousLossHamiltonian M hM hc μ (fun a => wedgePair (u a) (v a))) =
      continuousFrameHamiltonian μ (fun a => exteriorSquare M.toLinearMap (wedgePair (u a) (v a))) *
        continuousFrameHamiltonian μ (fun a => exteriorSquare M.toLinearMap (wedgePair (u a) (v a))) +
      (continuousOneLossNoise M μ u v).adjoint.comp (continuousOneLossNoise M μ u v) +
      (continuousTwoLossNoise M μ (fun a => wedgePair (u a) (v a))).adjoint.comp
        (continuousTwoLossNoise M μ (fun a => wedgePair (u a) (v a))) := by
  let p := fun a => wedgePair (u a) (v a)
  have hp : MemLp p 2 μ := wedgePair_memLp μ u v hu hv hun hvn
  let H := continuousLossHamiltonian M hM hc μ p
  let K := continuousFrameHamiltonian μ (fun a => exteriorSquare M.toLinearMap (p a))
  have hH : H.adjoint = H := continuousLossHamiltonian_adjoint M μ hM hc p hp
  have hK : K.adjoint = K := continuousFrameHamiltonian_adjoint μ _ (filteredPair_memLp M μ p hp)
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  rw [continuousVacuumCompression_inner]
  change inner ℂ (lossVacuum n x) (H (H (lossVacuum n y))) = _
  rw [← ContinuousLinearMap.adjoint_inner_left H (H (lossVacuum n y)) (lossVacuum n x), hH,
    ← (fockSplit n n).inner_map_map]
  rw [continuous_loss_output_inner M hM hc μ u v hu hv hun hvn]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, mul_apply_eq_comp,
    inner_add_right, ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (K x) (K y) + _ + _ = inner ℂ x (K (K y)) + _ + _
  rw [← ContinuousLinearMap.adjoint_inner_left K (K y) x, hK]

include hM hc hu hv hun hvn in
/-- The original reference-sector inequality controls the three derived output terms. -/
theorem continuous_loss_compressed_reference_inequality {N : ℕ} (γ : ℝ)
    (hgap : ∀ K ≤ N, ∀ y : Space n, InSector K y →
      γ * (inner ℂ y (continuousFrameHamiltonian μ (fun a => wedgePair (u a) (v a)) y)).re ≤
        (inner ℂ y ((continuousFrameHamiltonian μ (fun a => wedgePair (u a) (v a)) *
          continuousFrameHamiltonian μ (fun a => wedgePair (u a) (v a))) y)).re)
    {x : Space n} (hx : InSector N x) :
    γ * (inner ℂ x (continuousFrameHamiltonian μ
        (fun a => exteriorSquare M.toLinearMap (wedgePair (u a) (v a))) x)).re ≤
      (inner ℂ x ((continuousFrameHamiltonian μ
          (fun a => exteriorSquare M.toLinearMap (wedgePair (u a) (v a))) *
        continuousFrameHamiltonian μ (fun a => exteriorSquare M.toLinearMap (wedgePair (u a) (v a))) +
        (continuousOneLossNoise M μ u v).adjoint.comp (continuousOneLossNoise M μ u v) +
        (continuousTwoLossNoise M μ (fun a => wedgePair (u a) (v a))).adjoint.comp
          (continuousTwoLossNoise M μ (fun a => wedgePair (u a) (v a)))) x)).re := by
  have h := continuousLossHamiltonian_sector_inequality M hM hc μ _
    (wedgePair_memLp μ u v hu hv hun hvn) γ hgap (lossVacuum_sector hx)
  rw [← continuousVacuumCompression_inner, ← continuousVacuumCompression_inner,
    continuous_loss_first_moment M hM hc μ u v hu hv hun hvn,
    continuous_loss_second_moment M hM hc μ u v hu hv hun hvn] at h
  exact h

end VortexGap.Fermion


import VortexGap.Examples.ContinuousCells
import VortexGap.Examples.CrossMix
import VortexGap.Transfer.ContinuousFrame

noncomputable section
set_option autoImplicit false
namespace VortexGap.Examples
open VortexGap.Fermion VortexGap.Frame MeasureTheory
open scoped InnerProduct ComplexOrder

/-- The continuous transfer instantiated from raw cell data, not from finite transfer. -/
theorem continuous_cell_frame_transfer {k N : ℕ}
    (M : EuclideanSpace ℂ (Fin (2*k)) →L[ℂ] EuclideanSpace ℂ (Fin (2*k)))
    (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) {x : Space (2*k)} (hx : InSector N x) :
    (1 - 2*‖1-M^2‖ - ‖1-M^2‖^2) *
      (inner ℂ x (continuousFrameHamiltonian (continuousCellMeasure k)
        (fun a => exteriorSquare M.toLinearMap (cellPairs k a.1)) x)).re ≤
      (inner ℂ x ((continuousFrameHamiltonian (continuousCellMeasure k)
        (fun a => exteriorSquare M.toLinearMap (cellPairs k a.1)) *
        continuousFrameHamiltonian (continuousCellMeasure k)
        (fun a => exteriorSquare M.toLinearMap (cellPairs k a.1))) x)).re := by
  have hp (j : Fin k) : wedgePair (cellFrames k j (PiLp.single 2 0 1))
      (cellFrames k j (PiLp.single 2 1 1)) = cellPairs k j := modeFrame_wedge (cellPair k j)
  have h := continuous_frame_transfer M hM hc (continuousCellMeasure k)
    (fun a => cellFrames k a.1) (continuousCell_column_measurable k 0)
    (continuousCell_column_measurable k 1) (fun _ => 1) (by intro; norm_num)
    aestronglyMeasurable_const 2
    (Filter.Eventually.of_forall fun a => by simpa only [mul_one] using continuousCell_row_integrable k a)
    (Filter.Eventually.of_forall fun a => by simpa only [mul_one] using (continuousCell_row k a).le)
    1 (by norm_num)
    (by
      intro q
      simp_rw [hp, continuousCell_pairOperator (cellPairs k)]
      simpa only [LinearMap.coe_toContinuousLinearMap', one_mul] using cell_frame_bound k q)
    1 (by
      intro K hK y hy
      simp_rw [hp, continuousCell_hamiltonian (cellPairs k)]
      simpa only [LinearMap.coe_toContinuousLinearMap', mul_apply_eq_comp, Module.End.mul_apply, one_mul]
        using cell_reference_gap k y) hx
  simpa only [hp, one_mul] using h

/-- A genuinely mixing filter with a positive coefficient, through the continuous theorem. -/
theorem continuous_crossMix_gap {N : ℕ} {x : Space 4} (hx : InSector N x) :
    (9/10 : ℝ) * (inner ℂ x (continuousFrameHamiltonian (continuousCellMeasure 2)
      (fun a => exteriorSquare crossMixFilter.toLinearMap (cellPairs 2 a.1)) x)).re ≤
    (inner ℂ x ((continuousFrameHamiltonian (continuousCellMeasure 2)
      (fun a => exteriorSquare crossMixFilter.toLinearMap (cellPairs 2 a.1)) *
      continuousFrameHamiltonian (continuousCellMeasure 2)
      (fun a => exteriorSquare crossMixFilter.toLinearMap (cellPairs 2 a.1))) x)).re := by
  have h := continuous_cell_frame_transfer (k := 2) crossMixFilter crossMixFilter_nonneg
    crossMixFilter_contraction hx
  rw [crossMixFilter_delta] at h
  rw [continuousCell_hamiltonian (fun j => exteriorSquare crossMixFilter.toLinearMap (cellPairs 2 j))] at h ⊢
  have he : 0 ≤ (inner ℂ x (filteredHamiltonian crossMixFilter (fun _ => 1) (cellPairs 2) x)).re := by
    rw [← filtered_frameAnalysis_norm_sq crossMixFilter (fun _ => 1) (by intro; norm_num)]
    exact sq_nonneg _
  change (1 - 2*(199/10000 : ℝ) - (199/10000 : ℝ)^2) *
    (inner ℂ x (filteredHamiltonian crossMixFilter (fun _ => 1) (cellPairs 2) x)).re ≤
    (inner ℂ x ((filteredHamiltonian crossMixFilter (fun _ => 1) (cellPairs 2) *
      filteredHamiltonian crossMixFilter (fun _ => 1) (cellPairs 2)) x)).re at h
  change (9/10 : ℝ) * (inner ℂ x (filteredHamiltonian crossMixFilter (fun _ => 1) (cellPairs 2) x)).re ≤
    (inner ℂ x ((filteredHamiltonian crossMixFilter (fun _ => 1) (cellPairs 2) *
      filteredHamiltonian crossMixFilter (fun _ => 1) (cellPairs 2)) x)).re
  nlinarith only [h, he]

theorem continuous_crossMix_pair_energy :
    (inner ℂ (pairEmbed (cellPairs 2 0))
      (continuousFrameHamiltonian (continuousCellMeasure 2)
        (fun a => exteriorSquare crossMixFilter.toLinearMap (cellPairs 2 a.1))
        (pairEmbed (cellPairs 2 0)))).re = (2491/2500 : ℝ)^2 := by
  rw [continuousCell_hamiltonian (fun j => exteriorSquare crossMixFilter.toLinearMap (cellPairs 2 j))]
  exact crossMix_pair_energy

theorem continuous_crossMix_pair_energy_pos :
    0 < (inner ℂ (pairEmbed (cellPairs 2 0))
      (continuousFrameHamiltonian (continuousCellMeasure 2)
        (fun a => exteriorSquare crossMixFilter.toLinearMap (cellPairs 2 a.1))
        (pairEmbed (cellPairs 2 0)))).re := by
  rw [continuous_crossMix_pair_energy]
  norm_num

end VortexGap.Examples


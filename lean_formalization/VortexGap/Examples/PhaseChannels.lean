import VortexGap.Transfer.ContinuousSlater
import VortexGap.Examples.ContinuousPhase
import VortexGap.Examples.FourModeRankTwo
import VortexGap.Examples.CrossMix
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open VortexGap.Frame VortexGap.Examples MeasureTheory
open scoped InnerProduct ENNReal ComplexOrder

/-- Counting measure on finitely many channels, with the same base measure in each.
The row includes every target channel, including those different from the source. -/
theorem slater_channel_row {X I α : Type*} [MeasurableSpace X] [MeasurableSpace I]
    [Fintype I] [MeasurableSingletonClass I] [Fintype α] {n : ℕ} (μ : Measure X) [SFinite μ]
    (c : I × X → α → ℂ) (U : I × X → α → TwoFrame n) (ω : I × X → ℝ) (s : I × X)
    (hi : Integrable (fun t => slaterKernel (c s) (c t) (U s) (U t)*ω t) (Measure.count.prod μ)) :
    (∫ t, slaterKernel (c s) (c t) (U s) (U t)*ω t ∂Measure.count.prod μ) =
      ∑ j : I, ∫ y, slaterKernel (c s) (c (j,y)) (U s) (U (j,y))*ω (j,y) ∂μ := by
  rw [integral_prod _ hi, integral_count]

/-- The channels use opposite signs on the second basis pair and a continuous
common phase. The two coherent pairs at t=0 are orthogonal. -/
def phaseChannelCoeff (s : Fin 2 × ℝ) (a : Fin 2) : ℂ :=
  if s.1=1 ∧ a=1 then -phaseScalar s.2 else phaseScalar s.2

theorem phaseChannel_cross_kernel (s t : Fin 2 × ℝ) :
    slaterKernel (phaseChannelCoeff s) (phaseChannelCoeff t) fourModeFrames fourModeFrames = 4 := by
  have hn (z : Fin 2 × ℝ) (a : Fin 2) : ‖phaseChannelCoeff z a‖ = 1 := by
    unfold phaseChannelCoeff
    split_ifs <;> simp [phaseScalar_norm]
  simpa only [slaterKernel,hn,norm_one] using! fourModeKernel

theorem phaseChannel_row (s : Fin 2 × ℝ) :
    (∫ t, slaterKernel (phaseChannelCoeff s) (phaseChannelCoeff t) fourModeFrames fourModeFrames
      ∂(Measure.count : Measure (Fin 2)).prod phaseMeasure) = 8 := by
  simp_rw [phaseChannel_cross_kernel]
  rw [integral_prod _ (integrable_const _)]
  norm_num [phaseMeasure_mass]

theorem phaseChannel_pairs_orthogonal :
    inner ℂ (slaterPair (phaseChannelCoeff (0,0)) fourModeFrames)
      (slaterPair (phaseChannelCoeff (1,0)) fourModeFrames) = 0 := by
  simp [slaterPair, Fin.sum_univ_two, fourModeFrames, modeFrame_wedge,phaseChannelCoeff,phaseScalar,
    inner_add_left, pairBasis, EuclideanSpace.inner_single_left,pair01,pair23]

/-- Strictly positive coefficient for the checked nonidentity, nondiagonal filter. -/
theorem fourMode_crossMix_gap {N : ℕ} {x : Space 4} (hx : InSector N x) :
    let H := filteredHamiltonian crossMixFilter (fun _ : Unit => (1/2:ℝ)) (fun _ => fourModePair)
    (1/2-2*(199/10000:ℝ)-(199/10000:ℝ)^2)*(inner ℂ x (H x)).re ≤ ‖H x‖^2 := by
  simpa only [crossMixFilter_delta] using fourMode_rank_two_transfer crossMixFilter crossMixFilter_nonneg crossMixFilter_contraction hx

@[reducible]
def phaseChannelMeasure := (Measure.count : Measure (Fin 2)).prod phaseMeasure
@[reducible]
def phaseChannelPair (s : Fin 2 × ℝ) := slaterPair (phaseChannelCoeff s) fourModeFrames

private theorem chCoeff_L2 (a : Fin 2) : MemLp (fun t => phaseChannelCoeff t a) 2 phaseChannelMeasure := by
  have hm : Measurable fun t : Fin 2 × ℝ => phaseScalar t.2 := by unfold phaseScalar; fun_prop
  apply MemLp.of_bound (hm.neg.ite (by measurability) hm).aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro t
  change ‖phaseChannelCoeff t a‖ ≤ _
  unfold phaseChannelCoeff
  split_ifs <;> simp [phaseScalar_norm]

private theorem phaseChannelPair_L2 : MemLp phaseChannelPair 2 phaseChannelMeasure := continuousSlaterPair_memLp phaseChannelMeasure
  phaseChannelCoeff (fun _ => fourModeFrames) chCoeff_L2 (fun _ _ => aestronglyMeasurable_const)

private theorem phaseChannelPair_phase (i : Fin 2) (t : ℝ) : phaseChannelPair (i,t) = phaseScalar t • phaseChannelPair (i,0) := by
  fin_cases i <;> simp [phaseChannelPair,slaterPair,phaseChannelCoeff,Fin.sum_univ_two,smul_add,phaseScalar,smul_neg]

private theorem chRank (i : Fin 2) (t : ℝ) :
    InnerProductSpace.rankOne ℂ (phaseChannelPair (i,t)) (phaseChannelPair (i,t)) =
      InnerProductSpace.rankOne ℂ (phaseChannelPair (i,0)) (phaseChannelPair (i,0)) := by
  rw [phaseChannelPair_phase i t]
  apply ContinuousLinearMap.ext
  intro q
  simp only [InnerProductSpace.rankOne_apply,inner_smul_left,smul_smul]
  congr 1
  rw [mul_right_comm, Complex.conj_mul',phaseScalar_norm]
  norm_num

theorem phaseChannel_pairOperator :
    (continuousPairOperator phaseChannelMeasure phaseChannelPair).toLinearMap =
      (2:ℂ) • (∑ j : Fin 2, pairRankOne (cellPairs 2 j)) := by
  have : CompleteSpace (PairSpace 4) := PiLp.completeSpace 2 (fun _ => ℂ)
  have : CompleteSpace (PairSpace 4 →L[ℂ] PairSpace 4) := ContinuousLinearMap.instCompleteSpace
  have hi := continuousPairOperator_integrable phaseChannelMeasure phaseChannelPair phaseChannelPair_L2
  unfold continuousPairOperator
  rw [integral_prod _ hi]
  simp_rw [chRank]
  simp only [integral_const,phaseMeasure_mass,one_smul,integral_count,Fin.sum_univ_two]
  ext q A
  simp [phaseChannelPair,slaterPair,Fin.sum_univ_two,fourModeFrames,modeFrame_wedge,phaseChannelCoeff,phaseScalar,
    InnerProductSpace.rankOne_apply,smul_add,cellPairs,pairRankOne,
    LinearMap.smul_apply,show cellPair 2 0 = pair01 from rfl,show cellPair 2 1 = pair23 from rfl]
  ring

private theorem chHam : (continuousFrameHamiltonian phaseChannelMeasure phaseChannelPair).toLinearMap =
    (2:ℂ) • frameHamiltonian (fun _ => 1) (cellPairs 2) := by
  rw [continuousFrameHamiltonian_pairLift phaseChannelMeasure phaseChannelPair phaseChannelPair_L2]
  change pairLift (continuousPairOperator phaseChannelMeasure phaseChannelPair).toLinearMap = _
  rw [phaseChannel_pairOperator,pairLift_smul]
  simp [frameHamiltonian]

theorem phaseChannel_beta (q : PairSpace 4) : (inner ℂ q (continuousPairOperator phaseChannelMeasure phaseChannelPair q)).re ≤ 2*‖q‖^2 := by
  change (inner ℂ q ((continuousPairOperator phaseChannelMeasure phaseChannelPair).toLinearMap q)).re ≤ _
  rw [phaseChannel_pairOperator,LinearMap.smul_apply,inner_smul_right]
  simp only [Complex.mul_re,show (2:ℂ).re = 2 from rfl,show (2:ℂ).im = 0 from rfl,zero_mul,sub_zero]
  linarith [cell_frame_bound 2 q]

theorem phaseChannel_reference (x : Space 4) :
    let H := continuousFrameHamiltonian phaseChannelMeasure phaseChannelPair
    2*(inner ℂ x (H x)).re ≤ (inner ℂ x ((H*H) x)).re := by
  change 2*(inner ℂ x ((continuousFrameHamiltonian phaseChannelMeasure phaseChannelPair).toLinearMap x)).re ≤
    (inner ℂ x ((continuousFrameHamiltonian phaseChannelMeasure phaseChannelPair).toLinearMap
      ((continuousFrameHamiltonian phaseChannelMeasure phaseChannelPair).toLinearMap x))).re
  rw [chHam]
  simp only [LinearMap.smul_apply,map_smul,inner_smul_right,Complex.mul_re,show (2:ℂ).re = 2 from rfl,show (2:ℂ).im = 0 from rfl,zero_mul,sub_zero]
  have h := cell_reference_gap 2 x
  rw [Module.End.mul_apply] at h
  linarith

/-- Two overlapping channels on two copies of the unit interval; all reference and
row constants are supplied by the concrete model. -/
theorem phaseChannel_gap {N : ℕ} {x : Space 4} (hx : InSector N x) :
    let H := continuousFrameHamiltonian phaseChannelMeasure (fun t => exteriorSquare crossMixFilter.toLinearMap (phaseChannelPair t))
    (2-8*(199/10000:ℝ)-2*(199/10000:ℝ)^2)*(inner ℂ x (H x)).re ≤ ‖H x‖^2 := by
  have hr := continuousSlater_transfer phaseChannelMeasure phaseChannelCoeff (fun _ => fourModeFrames)
    crossMixFilter crossMixFilter_nonneg crossMixFilter_contraction chCoeff_L2 (fun _ _ => aestronglyMeasurable_const)
    (fun _ => 1) (fun _ => zero_lt_one) aestronglyMeasurable_const 8
    (Filter.Eventually.of_forall fun s => by simp_rw [phaseChannel_cross_kernel,mul_one]; exact integrable_const _)
    (Filter.Eventually.of_forall fun s => by simpa only [mul_one] using (phaseChannel_row s).le)
    2 (by norm_num) phaseChannel_beta 2 (fun _ _ y _ => phaseChannel_reference y) hx
  simpa only [crossMixFilter_delta] using hr

theorem phaseChannel_filtered_energy :
    let x := pairEmbed (cellPairs 2 0)
    let H := continuousFrameHamiltonian phaseChannelMeasure
      (fun t => exteriorSquare crossMixFilter.toLinearMap (phaseChannelPair t))
    (inner ℂ x (H x)).re = 2*(2491/2500:ℝ)^2 := by
  let T := exteriorSquare crossMixFilter.toLinearMap
  let q := cellPairs 2 0
  have first (i : Fin 2) : (T (phaseChannelPair (i,0))) (cellPair 2 0) = (2491/2500:ℂ) := by
    fin_cases i <;>
      simp [phaseChannelPair,slaterPair,Fin.sum_univ_two,fourModeFrames,modeFrame_wedge,phaseChannelCoeff,phaseScalar] <;>
      simp only [T,exteriorSquare_pairBasis] <;>
      norm_num [wedgePair,crossMixFilter_entry,cellPair,pair01,pair23,crossMixVector,map_div₀,map_ofNat]
  have energy (s : Fin 2 × ℝ) : ‖pairAnnihilate (T (phaseChannelPair s)) (pairEmbed q)‖^2 = (2491/2500:ℝ)^2 := by
    rcases s with ⟨i,t⟩
    rw [phaseChannelPair_phase i t,map_smul,pairAnnihilate_pairEmbed,norm_smul,ket_norm,mul_one,inner_smul_left,norm_mul,
      Complex.norm_conj,phaseScalar_norm,one_mul]
    change ‖inner ℂ _ (PiLp.single 2 (cellPair 2 0) 1)‖^2 = _
    simp [EuclideanSpace.inner_single_right,first]
  dsimp only
  rw [continuousFrameHamiltonian_energy phaseChannelMeasure _ (filteredPair_memLp crossMixFilter _ _ phaseChannelPair_L2)]
  change (∫ t, ‖pairAnnihilate (T (phaseChannelPair t)) (pairEmbed q)‖^2 ∂phaseChannelMeasure) = _
  simp_rw [energy]
  rw [integral_prod _ (integrable_const _)]
  norm_num [phaseMeasure_mass]

end VortexGap.Fermion

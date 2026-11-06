import VortexGap.Examples.PlaneBandDistinct
import VortexGap.Physical.PlaneGramBounds
import VortexGap.Examples.PeriodicEnvelope
import VortexGap.Physical.PlaneFourierBounds
import VortexGap.Physical.PlaneBandSpectrum

noncomputable section

namespace VortexGap.Fermion
open scoped ComplexOrder BoundedContinuousFunction
local notation "Orb" => CountableOrbital →L[ℂ] CountableOrbital

theorem periodicEnvelope_gram_deviation (ell : ℝ) (hell : 0 < ell) {ε : ℝ} (hε : 0 ≤ ε)
    (hε' : ε < 1) (q : ℝ) :
    let f := periodicEnvelope ε q hε
    ‖planeToeplitzMap ell hell (star f*f) - (1:ℂ) • (1:Orb)‖ ≤ ε * Real.exp (-q^2*ell^2/4) := by
  let f := periodicEnvelope ε q hε
  have he (z : ℂ) : (star f*f) z = (1:ℂ) + ∑ i : Fin 4,
      ((ε/4:ℝ):ℂ) * planeFourierPhase (periodicFrequencies q i) z := by
    change (starRingEnd ℂ) (f z) * f z = _
    rw [Complex.conj_mul', ← Complex.ofReal_pow]
    exact periodicEnvelope_symbol hε hε' q z
  apply (planeFourier_finite_bound ell hell (star f*f) 1 Finset.univ
    (fun _ : Fin 4 => ((ε/4:ℝ):ℂ)) (periodicFrequencies q) he).trans
  simp only [periodicFrequencies_norm_sq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ ε/4 by positivity), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  linarith

theorem periodicEnvelope_gram_strict (ell : ℝ) (hell : 0 < ell) {ε : ℝ} (hε : 0 ≤ ε)
    (hε' : ε < 1) (q : ℝ) : IsStrictlyPositive (planeScalarGram ell hell (periodicEnvelope ε q hε)) := by
  apply gramOperator_strict _ (1-ε) (by linarith)
  apply (planeScalarGram_pointwise_bounds ell hell _ (1-ε) (1+ε) (by linarith) (by linarith) ?_).1
  intro z
  rw [periodicEnvelope_norm_sq hε hε']
  exact periodicWeight_bounds hε q z

def periodicEnvelopeHamiltonian (ell : ℝ) (hell : 0 < ell) {ε : ℝ} (hε : 0 ≤ ε)
    (hε' : ε < 1) (q : ℝ) (N : ℕ) :=
  planeBandContactOperator ell hell (periodicEnvelope ε q hε)
    (periodicEnvelope_gram_strict ell hell hε hε' q) (periodicEnvelope_differentiable hε hε' q) N

theorem periodicEnvelope_physical_gap (ell : ℝ) (hell : 0 < ell) {ε : ℝ} (hε : 0 ≤ ε)
    (hε' : ε < 1) (q α γ : ℝ) (hα : α < 1) (hdev : ε*Real.exp (-q^2*ell^2/4) ≤ α)
    (N : ℕ) (href : ∀ j ≤ N, let H := countablePairLift j planePairOperator
      (H*H-(γ:ℂ) • H).IsPositive) :
    ∀ t ∈ spectrum ℝ (periodicEnvelopeHamiltonian ell hell hε hε' q N),
      t = 0 ∨ periodicGapBound ((1-ε)^2) α γ ≤ t := by
  have h := planeGram_bounds_of_deviation ell hell _ 1 α
    ((periodicEnvelope_gram_deviation ell hell hε hε' q).trans hdev)
  have hnonneg : 0 ≤ α := (mul_nonneg hε (Real.exp_pos _).le).trans hdev
  exact physical_scalar_criterion ell hell _ (periodicEnvelope_differentiable hε hε' q)
    (1-α) (1+α) ((1-ε)^2) γ (by linarith) (by linarith) (by positivity) h.1 h.2
    (planeWeightedPairOperator_lower ell _ _ (sq_nonneg _) (periodicEnvelope_pair_lower hε hε' q)) N href

theorem periodic_first_physical (ell : ℝ) (hell : 0 < ell) (N : ℕ)
    (href : ∀ j ≤ N, let H := countablePairLift j planePairOperator
      (H*H-(1/5:ℂ) • H).IsPositive) :
    ∀ t ∈ spectrum ℝ (periodicEnvelopeHamiltonian ell hell (ε := 1/100) (by norm_num) (by norm_num)
      (periodicMagneticWaveNumber ell 1) N), t = 0 ∨ 1390/10000 < t := by
  intro t ht
  have h := periodicEnvelope_physical_gap ell hell (by norm_num : (0:ℝ) ≤ 1/100)
    (by norm_num) _ (21/10000) (1/5) (by norm_num) (periodicMagnetic_first ell hell) N
    (by simpa using href) t ht
  exact h.imp_right (fun lower => periodic_first_row_arithmetic.trans_le lower)

theorem periodic_path_physical (ell : ℝ) (hell : 0 < ell) {ε : ℝ} (hε : 0 ≤ ε) (hm : ε ≤ 1/2)
    (N : ℕ) (href : ∀ j ≤ N, let H := countablePairLift j planePairOperator
      (H*H-(1/5:ℂ) • H).IsPositive) :
    ∀ t ∈ spectrum ℝ (periodicEnvelopeHamiltonian ell hell hε (by linarith)
      (periodicMagneticWaveNumber ell 2) N), t = 0 ∨ 430/10000 < t := by
  intro t ht
  have h := periodicEnvelope_physical_gap ell hell hε (by linarith) _ (1/1000) (1/5) (by norm_num)
    (periodicMagnetic_path ell hell ε hm) N (by simpa using href) t ht
  exact h.imp_right (fun lower => (periodic_path_arithmetic hm).trans_le lower)

theorem periodic_band_distinct (ell : ℝ) (hell : 0 < ell) {ε q : ℝ}
    (hε : 0 < ε) (hu : ε < 1) (hq : q ≠ 0) :
    (planeScalarEmbedding ell hell (periodicEnvelope ε q hε.le)).toLinearMap.range ≠
      (planeLLLEmbedding ell hell).toLinearMap.range := by
  intro he
  have hv : planeScalarEmbedding ell hell (periodicEnvelope ε q hε.le) (orbitalKet 0) ∈
      (planeLLLEmbedding ell hell).toLinearMap.range := he ▸ ⟨orbitalKet 0,rfl⟩
  exact periodicEnvelope_nonconstant hε hu hq
    (planeScalar_vacuum_mem_imp_constant ell hell _ hv 0 _)

end VortexGap.Fermion

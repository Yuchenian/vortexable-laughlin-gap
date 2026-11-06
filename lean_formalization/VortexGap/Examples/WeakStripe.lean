import VortexGap.Reference.CertifiedPlane
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
namespace VortexGap.Fermion
open scoped BoundedContinuousFunction ComplexOrder

private def stripeWeight (q : ℝ) (z : ℂ) : ℝ := 1 + Real.cos (q*z.re)/10000
private theorem stripe_bounds (q : ℝ) (z : ℂ) :
    (9999/10000:ℝ) ≤ stripeWeight q z ∧ stripeWeight q z ≤ (10001/10000:ℝ) := by
  unfold stripeWeight
  constructor <;> linarith [Real.neg_one_le_cos (q*z.re), Real.cos_le_one (q*z.re)]

def weakStripe (q : ℝ) : ℂ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun z => ((Real.sqrt (stripeWeight q z):ℝ):ℂ))
    (by unfold stripeWeight; fun_prop) (Real.sqrt (10001/10000)) (fun z => by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_sqrt (stripe_bounds q z).2)

private theorem stripe_sq (q : ℝ) (z : ℂ) : ‖weakStripe q z‖^2 = stripeWeight q z := by
  change ‖((Real.sqrt _:ℝ):ℂ)‖^2 = _
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt]
  linarith [(stripe_bounds q z).1]

private theorem stripe_diff (q : ℝ) : Differentiable ℝ (weakStripe q) := by
  intro z
  have hp : 0 < stripeWeight q z := by linarith [(stripe_bounds q z).1]
  have hd : DifferentiableAt ℝ (stripeWeight q) z := by unfold stripeWeight; fun_prop
  exact Complex.ofRealCLM.differentiableAt.comp z (hd.sqrt hp.ne')

private theorem stripe_gram (ell : ℝ) (hell : 0 < ell) (q : ℝ) :
    (9999/10000:ℝ) • (1 : CountableOrbital →L[ℂ] CountableOrbital) ≤ planeScalarGram ell hell (weakStripe q) ∧
    planeScalarGram ell hell (weakStripe q) ≤ (10001/10000:ℝ) • (1 : CountableOrbital →L[ℂ] CountableOrbital) :=
  planeScalarGram_pointwise_bounds ell hell (weakStripe q)
    (9999/10000) (10001/10000) (by norm_num) (by norm_num)
    (fun z => by rw [stripe_sq]; exact stripe_bounds q z)

def weakStripeHamiltonian (ell : ℝ) (hell : 0 < ell) (q : ℝ) (N : ℕ) :=
  planeBandContactOperator ell hell (weakStripe q)
    (gramOperator_strict _ _ (by norm_num : (0:ℝ)<9999/10000) (stripe_gram ell hell q).1)
    (stripe_diff q) N

theorem weakStripe_certified_gap (ell : ℝ) (hell : 0 < ell) (q : ℝ) (hq : q ≠ 0) (N : ℕ) :
    (planeScalarEmbedding ell hell (weakStripe q)).toLinearMap.range ≠
      (planeLLLEmbedding ell hell).toLinearMap.range ∧
    ∀ t ∈ spectrum ℝ (weakStripeHamiltonian ell hell q N), t=0 ∨ (37/1000:ℝ)<t := by
  constructor
  · intro he
    have hv : planeScalarEmbedding ell hell (weakStripe q) (orbitalKet 0) ∈
        (planeLLLEmbedding ell hell).toLinearMap.range := he ▸ ⟨orbitalKet 0,rfl⟩
    have hh := congrArg (fun c : ℂ => ‖c‖^2)
      (planeScalar_vacuum_mem_imp_constant ell hell _ hv 0 ((Real.pi/q:ℝ):ℂ))
    simp only [stripe_sq,stripeWeight,Complex.zero_re,Complex.ofReal_re,mul_zero,Real.cos_zero,
      show q*(Real.pi/q)=Real.pi by field_simp,Real.cos_pi] at hh
    norm_num at hh
  · have hw := planeWeightedPairOperator_lower ell (weakStripe q) ((9999/10000)^2) (by norm_num)
          (fun z => by rw [show (4:ℕ)=2*2 by decide,pow_mul,stripe_sq]
                       exact pow_le_pow_left₀ (by norm_num) (stripe_bounds q z).1 2)
    have hs := physical_scalar_criterion ell hell (weakStripe q) (stripe_diff q)
      (9999/10000) (10001/10000) ((9999/10000)^2) (1/25)
      (by norm_num) (by norm_num) (by norm_num) (stripe_gram ell hell q).1 (stripe_gram ell hell q).2
      hw N (fun k _ => by simpa using countablePlane_old_bound k)
    intro t ht
    exact (hs t ht).imp_right (fun h => lt_of_lt_of_le (by norm_num) h)

end VortexGap.Fermion

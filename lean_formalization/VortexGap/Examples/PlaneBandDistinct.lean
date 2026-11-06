import VortexGap.Examples.PlaneWeakCosine
import Mathlib.Analysis.Complex.Liouville
import Mathlib.MeasureTheory.Measure.OpenPos
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory
open scoped InnerProduct ComplexConjugate BoundedContinuousFunction

theorem planeBargmann_inner_conj (z : ℂ) (v : CountableOrbital) :
    inner ℂ (planeBargmann (conj z)) v = inner ℂ (star v) (planeBargmann z) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp [RCLike.inner_apply, planeBargmann_coefficient, planeBargmannCoeff, lp.star_apply, mul_comm]

theorem planeEvaluation_gaussian_factor (ell : ℝ) (z : ℂ) (v : CountableOrbital) :
    inner ℂ (planeEvaluation ell z) v = planeWavefunction ell z 0 *
      inner ℂ (star v) (planeBargmann (planeCoordinate ell z)) := by
  simp only [planeEvaluation, planeCoherent, inner_smul_left, Complex.conj_ofReal,
    Complex.norm_conj, planeBargmann_inner_conj]
  simp [planeWavefunction, planeBargmannCoeff, mul_assoc]

theorem planeScalar_vacuum_mem_imp_constant (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (h : planeScalarEmbedding ell hell f (orbitalKet 0) ∈ (planeLLLEmbedding ell hell).toLinearMap.range) :
    ∀ z w : ℂ, f z = f w := by
  obtain ⟨v, hv⟩ := h
  have hae : (fun z => f z * planeWavefunction ell z 0) =ᵐ[volume]
      (fun z => inner ℂ (planeEvaluation ell z) v) := by
    filter_upwards [planeScalarEmbedding_coe ell hell f (orbitalKet 0),
      planeLLLEmbedding_coe ell hell v] with z hz hzv
    have hk : inner ℂ (planeEvaluation ell z) (orbitalKet 0) = planeWavefunction ell z 0 := by
      rw [← inner_conj_symm, orbitalKet_inner_left, planeEvaluation_coefficient]
      simp
    rw [hk] at hz
    change planeLLLEmbedding ell hell v = planeScalarEmbedding ell hell f (orbitalKet 0) at hv
    rw [← hz, ← hzv, hv]
  have hw : Continuous (fun z => planeWavefunction ell z 0) := by
    unfold planeWavefunction planeCoordinate planeBargmannCoeff
    fun_prop
  have he := MeasureTheory.Measure.eq_of_ae_eq hae (f.continuous.mul hw)
    ((planeEvaluation_continuous ell).inner continuous_const)
  have hf : (fun z => f z) = fun z => inner ℂ (star v) (planeBargmann (planeCoordinate ell z)) := by
    funext z
    have hh := congrFun he z
    rw [planeEvaluation_gaussian_factor] at hh
    have hn : planeWavefunction ell z 0 ≠ 0 := by
      simp only [planeWavefunction, planeBargmannCoeff, pow_zero, Nat.factorial_zero,
        Nat.cast_one, Real.sqrt_one, Complex.ofReal_one, div_one, mul_one]
      apply mul_ne_zero
      · exact_mod_cast inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by positivity : 0 < 2*Real.pi*ell^2)))
      · exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
    exact (mul_right_cancel₀ hn (by simpa [mul_comm] using hh))
  have hd : Differentiable ℂ (fun z => f z) := by
    rw [hf]
    apply (innerSL ℂ (star v)).differentiable.comp
    apply (show Differentiable ℂ planeBargmann from fun z => (planeBargmann_hasDerivAt z).differentiableAt).comp
    unfold planeCoordinate
    fun_prop
  exact hd.apply_eq_apply_of_bounded f.isBounded_range

theorem planeWeakCos_range_ne (ell : ℝ) (hell : 0 < ell) :
    (planeScalarEmbedding ell hell planeWeakCos).toLinearMap.range ≠
      (planeLLLEmbedding ell hell).toLinearMap.range := by
  intro h
  have hm : planeScalarEmbedding ell hell planeWeakCos (orbitalKet 0) ∈
      (planeLLLEmbedding ell hell).toLinearMap.range := by
    rw [← h]
    exact ⟨orbitalKet 0, rfl⟩
  exact planeWeakCos_nonconstant (planeScalar_vacuum_mem_imp_constant ell hell planeWeakCos hm 0 (Real.pi : ℂ))
end VortexGap.Fermion


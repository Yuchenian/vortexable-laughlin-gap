import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
namespace VortexGap.Frame
open scoped BigOperators InnerProduct ComplexConjugate

abbrev TwoSpace := EuclideanSpace ℂ (Fin 2)

/-- The trace norm of a two-dimensional operator, using the actual ordered singular values. -/
def traceNormTwo (K : Module.End ℂ TwoSpace) : ℝ := K.singularValues 0 + K.singularValues 1

theorem traceNormTwo_nonneg (K : Module.End ℂ TwoSpace) : 0 ≤ traceNormTwo K :=
  add_nonneg (K.singularValues_nonneg 0) (K.singularValues_nonneg 1)

theorem singularValues_two_tail (K : Module.End ℂ TwoSpace) (i : ℕ) (hi : 2 ≤ i) :
    K.singularValues i = 0 := by
  apply K.singularValues_of_finrank_le
  simpa only [TwoSpace, finrank_euclideanSpace_fin] using hi

/-- Columns in an eigenbasis of K-adjoint K have the actual singular-value norms.
Zero singular values need no inverse or separate choice of left singular vectors. -/
theorem traceNormTwo_eq_sum_image_norm (K : Module.End ℂ TwoSpace) :
    ∃ b : OrthonormalBasis (Fin 2) ℂ TwoSpace, traceNormTwo K = ∑ i, ‖K (b i)‖ := by
  have hn : Module.finrank ℂ TwoSpace = 2 := by simp [TwoSpace]
  let b := K.isSymmetric_adjoint_comp_self.eigenvectorBasis hn
  have hb (i : Fin 2) : ‖K (b i)‖ = K.singularValues i := by
    apply (sq_eq_sq₀ (norm_nonneg _) (K.singularValues_nonneg i)).mp
    have he : K.adjoint (K (b i)) =
        (K.isSymmetric_adjoint_comp_self.eigenvalues hn i : ℂ) • b i :=
      K.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis hn i
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), ← LinearMap.adjoint_inner_right K, he,
      inner_smul_right, inner_self_eq_norm_sq_to_K, b.norm_eq_one]
    simp only [one_pow, RCLike.ofReal_one, mul_one]
    exact (K.sq_singularValues_fin hn i).symm
  refine ⟨b, ?_⟩
  simp [hb, Fin.sum_univ_two, traceNormTwo]

theorem two_matrix_expansion (K : Module.End ℂ TwoSpace)
    (b : OrthonormalBasis (Fin 2) ℂ TwoSpace) (i j : Fin 2) :
    K (PiLp.single 2 j 1) i = ∑ l, K (b l) i * conj (b l j) := by
  have h := congrArg (fun z : TwoSpace => K z i) (b.sum_repr' (PiLp.single 2 j 1))
  simpa only [map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply,
    PiLp.smul_apply, smul_eq_mul, EuclideanSpace.inner_single_right, mul_one, one_mul, mul_comm] using h.symm

theorem traceNormTwo_zero : traceNormTwo (0 : Module.End ℂ TwoSpace) = 0 := by
  simp [traceNormTwo, LinearMap.singularValues_zero]

theorem traceNormTwo_id : traceNormTwo (LinearMap.id : Module.End ℂ TwoSpace) = 2 := by
  obtain ⟨b,hb⟩ := traceNormTwo_eq_sum_image_norm (LinearMap.id : Module.End ℂ TwoSpace)
  simpa only [LinearMap.id_apply, b.norm_eq_one, Fin.sum_univ_two, one_add_one_eq_two] using hb

end VortexGap.Frame

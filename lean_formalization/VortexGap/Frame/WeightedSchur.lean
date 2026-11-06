import VortexGap.Frame.FiniteSchur

noncomputable section
set_option autoImplicit false
namespace VortexGap.Frame
open scoped BigOperators InnerProduct

/-- Weighted Young inequality, permitting zero measure weights. -/
theorem weighted_schur_pair (a b s t u v : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hs : 0 < s) (ht : 0 < t) :
    2 * Real.sqrt a * Real.sqrt b * u * v ≤ (b*t/s)*u^2 + (a*s/t)*v^2 := by
  apply (mul_le_mul_iff_of_pos_left (mul_pos hs ht)).mp
  calc
    _ ≤ (s*t)*(2 * Real.sqrt a * Real.sqrt b * u * v) +
        (Real.sqrt b*t*u - Real.sqrt a*s*v)^2 := le_add_of_nonneg_right (sq_nonneg _)
    _ = _ := by
      field_simp [ne_of_gt hs, ne_of_gt ht]
      ring_nf
      rw [Real.sq_sqrt ha, Real.sq_sqrt hb]
      ring

/-- Finite Schur with arbitrary nonnegative measure weights and positive Schur weights.
The l2 coordinates absorb sqrt(a_i), but zero a_i are still permitted. -/
theorem finite_weighted_schur_quadratic {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (ω : ι → ℝ) (hω : ∀ i, 0 < ω i)
    (k : ι → ι → ℝ) (hk : ∀ i j, 0 ≤ k i j) (hs : ∀ i j, k i j = k j i)
    (C : ℝ) (hr : ∀ i, ∑ j, a j * k i j * ω j ≤ C * ω i) (u : ι → ℝ) :
    ∑ i, ∑ j, Real.sqrt (a i) * Real.sqrt (a j) * k i j * u i * u j ≤ C * ∑ i, (u i)^2 := by
  have hcol : (∑ i, ∑ j, k i j * (a i * ω i / ω j) * (u j)^2) =
      ∑ i, ∑ j, k i j * (a j * ω j / ω i) * (u i)^2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hs j i]
  have hrowi (i : ι) :
      ∑ j, k i j * (a j * ω j / ω i) * (u i)^2 ≤ C * (u i)^2 := by
    calc
      _ = (∑ j, a j * k i j * ω j) * ((u i)^2 / ω i) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ (C * ω i) * ((u i)^2 / ω i) :=
        mul_le_mul_of_nonneg_right (hr i) (div_nonneg (sq_nonneg _) (le_of_lt (hω i)))
      _ = _ := by field_simp [ne_of_gt (hω i)]
  have hrow : (∑ i, ∑ j, k i j * (a j * ω j / ω i) * (u i)^2) ≤ C * ∑ i, (u i)^2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hrowi i
  have hp (i j : ι) :
      2 * (Real.sqrt (a i) * Real.sqrt (a j) * k i j * u i * u j) ≤
        k i j * (a j * ω j / ω i) * (u i)^2 + k i j * (a i * ω i / ω j) * (u j)^2 := by
    have h := mul_le_mul_of_nonneg_left
      (weighted_schur_pair (a i) (a j) (ω i) (ω j) (u i) (u j) (ha i) (ha j) (hω i) (hω j)) (hk i j)
    convert h using 1 <;> ring
  have h := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset ι)) => hp i j
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  rw [hcol] at h
  linarith only [h, hrow]

/-- Operator-valued weighted Schur. The concrete two-frame Gram majorant is a
separate obligation, not a hidden assumption of a transfer theorem. -/
theorem finite_weighted_synthesis_norm_sq {ι E F : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (R : ι → E →L[ℂ] F) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (ω : ι → ℝ) (hω : ∀ i, 0 < ω i) (k : ι → ι → ℝ) (C : ℝ)
    (hk : ∀ i j, 0 ≤ k i j) (hs : ∀ i j, k i j = k j i)
    (hr : ∀ i, ∑ j, a j * k i j * ω j ≤ C * ω i)
    (hGram : ∀ i j, ‖(R i).adjoint ∘L R j‖ ≤ k i j) (f : ι → E) :
    ‖∑ i, (Real.sqrt (a i) : ℂ) • R i (f i)‖ ^ 2 ≤ C * ∑ i, ‖f i‖ ^ 2 := by
  have hb (i j : ι) :
      (inner ℂ (R i (f i)) (R j (f j))).re ≤ k i j * ‖f i‖ * ‖f j‖ := by
    rw [← ContinuousLinearMap.adjoint_inner_right (R i)]
    calc
      _ ≤ ‖inner ℂ (f i) ((R i).adjoint (R j (f j)))‖ := RCLike.re_le_norm _
      _ ≤ ‖f i‖ * ‖((R i).adjoint ∘L R j) (f j)‖ := norm_inner_le_norm _ _
      _ ≤ ‖f i‖ * (‖(R i).adjoint ∘L R j‖ * ‖f j‖) :=
        mul_le_mul_of_nonneg_left (((R i).adjoint ∘L R j).le_opNorm (f j)) (norm_nonneg _)
      _ ≤ ‖f i‖ * (k i j * ‖f j‖) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hGram i j) (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  have hterm (i j : ι) :
      (inner ℂ ((Real.sqrt (a i) : ℂ) • R i (f i))
        ((Real.sqrt (a j) : ℂ) • R j (f j))).re ≤
        Real.sqrt (a i) * Real.sqrt (a j) * k i j * ‖f i‖ * ‖f j‖ := by
    have h := mul_le_mul_of_nonneg_left (hb i j)
      (mul_nonneg (Real.sqrt_nonneg (a i)) (Real.sqrt_nonneg (a j)))
    convert h using 1
    · simp only [inner_smul_left, inner_smul_right, Complex.conj_ofReal,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      ring
    · ring
  have he : ‖∑ i, (Real.sqrt (a i) : ℂ) • R i (f i)‖ ^ 2 =
      ∑ i, ∑ j, (inner ℂ ((Real.sqrt (a i) : ℂ) • R i (f i))
        ((Real.sqrt (a j) : ℂ) • R j (f j))).re := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
    simp only [sum_inner, inner_sum, map_sum]
    rw [Finset.sum_comm]
    rfl
  calc
    _ = _ := he
    _ ≤ ∑ i, ∑ j, Real.sqrt (a i) * Real.sqrt (a j) * k i j * ‖f i‖ * ‖f j‖ :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ ≤ _ := finite_weighted_schur_quadratic a ha ω hω k hk hs C hr (fun i => ‖f i‖)

end VortexGap.Frame

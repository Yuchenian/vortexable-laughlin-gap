import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open Finset

theorem plane_binomial_mass (n : ℕ) :
    (∑ i ∈ range (n+1), (n.choose i : ℝ)) = (2 : ℝ)^n := by
  exact_mod_cast Nat.sum_range_choose n

/-- The centered second binomial moment for every angular momentum, including
zero. Pascal's recurrence proves it without a finite-K check. -/
theorem plane_binomial_second_moment (n : ℕ) :
    (∑ i ∈ range (n+1), (n.choose i : ℝ)*((n : ℝ)-2*(i : ℝ))^2) =
      (n : ℝ)*(2 : ℝ)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hsplit := sum_choose_succ_mul (fun i j => ((j : ℝ)-(i : ℝ))^2) n
    have hl : (∑ i ∈ range (n+2), ((n+1).choose i : ℝ)*
        (((n+1-i : ℕ) : ℝ)-(i : ℝ))^2) =
        ∑ i ∈ range (n+2), ((n+1).choose i : ℝ)*((n+1 : ℕ)-2*(i : ℝ))^2 := by
      apply sum_congr rfl
      intro i hi
      rw [Nat.cast_sub (by have := mem_range.mp hi; omega)]
      push_cast
      ring
    rw [hl] at hsplit
    calc
      _ = (∑ i ∈ range (n+1), (n.choose i : ℝ)*(((n+1-i : ℕ) : ℝ)-(i : ℝ))^2) +
          ∑ i ∈ range (n+1), (n.choose i : ℝ)*(((n-i : ℕ) : ℝ)-(i+1 : ℕ))^2 := hsplit
      _ = ∑ i ∈ range (n+1),
          (2*((n.choose i : ℝ)*((n : ℝ)-2*(i : ℝ))^2)+2*(n.choose i : ℝ)) := by
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro i hi
        have hn : i ≤ n := by have := mem_range.mp hi; omega
        rw [Nat.cast_sub (by omega : i ≤ n+1), Nat.cast_sub hn]
        push_cast
        ring
      _ = 2*((n : ℝ)*2^n)+2*2^n := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum, ih, plane_binomial_mass]
      _ = _ := by push_cast; rw [pow_succ]; ring

/-- Pairing i with n-i gives the ordered-pair half of the moment. The central
term, when present, vanishes rather than being counted with half weight. -/
theorem plane_binomial_half_moment (n : ℕ) :
    2*(∑ i ∈ (range (n+1)).filter (fun i => 2*i<n),
      (n.choose i : ℝ)*((n : ℝ)-2*(i : ℝ))^2) = (n : ℝ)*(2 : ℝ)^n := by
  let W : ℕ → ℝ := fun i => (n.choose i : ℝ)*((n : ℝ)-2*(i : ℝ))^2
  let f : ℕ → ℝ := fun i => if 2*i<n then W i else 0
  have hsym (i : ℕ) (hi : i ≤ n) : W (n-i) = W i := by
    dsimp [W]
    rw [Nat.choose_symm hi, Nat.cast_sub hi]
    ring
  have hp (i : ℕ) (hi : i ∈ range (n+1)) : W i = f i+f (n-i) := by
    have hin : i ≤ n := by have := mem_range.mp hi; omega
    by_cases hl : 2*i<n
    · have hr : ¬2*(n-i)<n := by omega
      simp [f, hl, hr]
    · by_cases hr : 2*(n-i)<n
      · simp [f, hl, hr, hsym i hin]
      · have he : n = 2*i := by omega
        have hw : W i = 0 := by simp [W, he, Nat.cast_mul]
        simp [f, hl, hr, hw]
  have hfull : (∑ i ∈ range (n+1), W i) = 2*(∑ i ∈ range (n+1), f i) := by
    calc
      _ = ∑ i ∈ range (n+1), (f i+f (n-i)) := sum_congr rfl hp
      _ = (∑ i ∈ range (n+1), f i)+(∑ i ∈ range (n+1), f i) := by
        rw [sum_add_distrib, sum_flip]
      _ = _ := by ring
  calc
    _ = 2*(∑ i ∈ range (n+1), f i) := by rw [sum_filter]
    _ = ∑ i ∈ range (n+1), W i := hfull.symm
    _ = _ := plane_binomial_second_moment n

theorem plane_binomial_half_moment_value (n : ℕ) (hn : 0 < n) :
    (∑ i ∈ (range (n+1)).filter (fun i => 2*i<n),
      (n.choose i : ℝ)*((n : ℝ)-2*(i : ℝ))^2) = (n : ℝ)*(2 : ℝ)^(n-1) := by
  have h := plane_binomial_half_moment n
  have he : (2 : ℝ)^n = 2*2^(n-1) := by
    have hnat : n = (n-1)+1 := by omega
    conv_lhs => rw [hnat]
    rw [pow_succ]
    ring
  rw [he] at h
  linarith

/-- Equivalent binomial form of the angular-momentum block coefficient.
Its identification with the factorial formula is a separate lemma. -/
def planeBlockCoefficient (n i : ℕ) : ℝ :=
  ((n : ℝ)-2*(i : ℝ))*Real.sqrt ((n.choose i : ℝ)/((n : ℝ)*2^(n-1)))

theorem planeBlockCoefficient_sq (n i : ℕ) :
    planeBlockCoefficient n i ^ 2 =
      ((n.choose i : ℝ)*((n : ℝ)-2*(i : ℝ))^2)/((n : ℝ)*2^(n-1)) := by
  rw [planeBlockCoefficient, mul_pow, Real.sq_sqrt (by positivity)]
  ring

/-- Every positive angular-momentum block has total squared coefficient one. -/
theorem planeBlockCoefficient_sum_sq (n : ℕ) (hn : 0 < n) :
    (∑ i ∈ (range (n+1)).filter (fun i => 2*i<n), planeBlockCoefficient n i ^ 2) = 1 := by
  simp_rw [planeBlockCoefficient_sq]
  rw [← sum_div, plane_binomial_half_moment_value n hn]
  exact div_self (by positivity)

theorem planeBlockCoefficient_factorial (n : ℕ) (hn : 0 < n) (i : ℕ) (hi : i ≤ n) :
    planeBlockCoefficient n i = ((n : ℝ)-2*(i : ℝ))*
      Real.sqrt (((n-1).factorial : ℝ)/
        ((2 : ℝ)^(n-1)*(i.factorial : ℝ)*((n-i).factorial : ℝ))) := by
  have hc : (n.choose i : ℝ)*(i.factorial : ℝ)*((n-i).factorial : ℝ) = (n.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
  have hf : (n : ℝ)*((n-1).factorial : ℝ) = (n.factorial : ℝ) := by
    exact_mod_cast Nat.mul_factorial_pred (ne_of_gt hn)
  unfold planeBlockCoefficient
  congr 1
  congr 1
  apply (div_eq_div_iff (by positivity) (by positivity)).2
  calc
    _ = (2 : ℝ)^(n-1)*((n.choose i : ℝ)*(i.factorial : ℝ)*((n-i).factorial : ℝ)) := by ring
    _ = (2 : ℝ)^(n-1)*(n.factorial : ℝ) := by rw [hc]
    _ = _ := by rw [← hf]; ring

/-- The exact factorial expression in the current supplement is normalized
for every positive K, with precisely the ordered indices 2*i<K. -/
theorem plane_block_factorial_normalization (n : ℕ) (hn : 0 < n) :
    (∑ i ∈ (range (n+1)).filter (fun i => 2*i<n),
      (((n : ℝ)-2*(i : ℝ))*Real.sqrt (((n-1).factorial : ℝ)/
        ((2 : ℝ)^(n-1)*(i.factorial : ℝ)*((n-i).factorial : ℝ))))^2) = 1 := by
  calc
    _ = ∑ i ∈ (range (n+1)).filter (fun i => 2*i<n), planeBlockCoefficient n i ^ 2 := by
      apply sum_congr rfl
      intro i hi
      have hin : i ≤ n := by have := mem_range.mp (mem_filter.mp hi).1; omega
      rw [planeBlockCoefficient_factorial n hn i hin]
    _ = 1 := planeBlockCoefficient_sum_sq n hn

end VortexGap.Fermion

import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.RealDeriv

noncomputable section
namespace VortexGap.SpherePolynomial
open MvPolynomial Finset
abbrev Poly (N : ℕ) := MvPolynomial (Fin N) ℂ

def laughlin (N : ℕ) : Poly N := (∏ i, ∏ j ∈ Ioi i, (X i - X j : Poly N)) ^ 3

private theorem diff_ne_zero {N : ℕ} {i j : Fin N} (h : i ≠ j) :
    (X i - X j : Poly N) ≠ 0 := sub_ne_zero.mpr (X_injective.ne h)

theorem laughlin_ne_zero (N : ℕ) : laughlin N ≠ 0 := by
  apply pow_ne_zero
  exact Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj =>
    diff_ne_zero (Finset.mem_Ioi.mp hj).ne

private theorem degree_diff {N : ℕ} (k i j : Fin N) (h : i ≠ j) :
    (X i - X j : Poly N).degreeOf k = (if k=i then 1 else 0) + (if k=j then 1 else 0) := by
  by_cases hi : k=i
  · subst i
    rw [sub_eq_add_neg, degreeOf_add_eq_of_degreeOf_lt]
    · simp [h]
    · simp [degreeOf_neg,degreeOf_X_of_ne h]
  by_cases hj : k=j
  · subst j
    rw [← neg_sub (X k) (X i),degreeOf_neg,sub_eq_add_neg,degreeOf_add_eq_of_degreeOf_lt]
    · simp [hi]
    · simp [degreeOf_neg,degreeOf_X_of_ne hi]
  have := degreeOf_sub_le k (X i : Poly N) (X j)
  simpa [hi,hj,degreeOf_X_of_ne hi,degreeOf_X_of_ne hj] using this

theorem laughlin_degree (N : ℕ) (k : Fin N) : (laughlin N).degreeOf k = 3*(N-1) := by
  classical
  have hn (i : Fin N) : (∏ j ∈ Ioi i, (X i-X j : Poly N)) ≠ 0 :=
    prod_ne_zero_iff.mpr fun j hj => diff_ne_zero (mem_Ioi.mp hj).ne
  rw [laughlin,degreeOf_pow_eq _ _ _ (prod_ne_zero_iff.mpr fun i _ => hn i),
      degreeOf_prod_eq _ _ (fun i _ => hn i)]
  simp_rw [degreeOf_prod_eq _ _ (fun j hj => diff_ne_zero (mem_Ioi.mp hj).ne)]
  have hs (i : Fin N) : (∑ j ∈ Ioi i, (X i-X j : Poly N).degreeOf k) =
      (if k=i then (Ioi i).card else 0) + (if i<k then 1 else 0) := by
    rw [sum_congr rfl (fun j hj => degree_diff k i j (mem_Ioi.mp hj).ne),sum_add_distrib]
    by_cases hi : k=i <;> simp [hi]
  simp_rw [hs]
  rw [sum_add_distrib]
  have hl : (∑ i : Fin N, if i<k then 1 else 0) = (Iio k).card := by
    have he : univ.filter (fun i : Fin N => i < k) = Iio k := by ext i; simp
    simp [he]
  rw [hl]
  simp [Fin.card_Ioi, Fin.card_Iio]
  omega

/-- At Laughlin flux a polynomial divisible by the full cubic Vandermonde
has no degree left for a nonconstant factor in any particle coordinate. -/
theorem multiple_at_minimal_flux {N : ℕ} {p : Poly N} (hd : laughlin N ∣ p)
    (hb : ∀ i, p.degreeOf i ≤ 3*(N-1)) : ∃ c : ℂ, p = C c * laughlin N := by
  classical
  obtain ⟨q,rfl⟩ := hd
  by_cases hz : q=0
  · exact ⟨0,by simp [hz]⟩
  have hq (i : Fin N) : q.degreeOf i = 0 := by
    have h := hb i
    rw [degreeOf_mul_eq (laughlin_ne_zero N) hz,laughlin_degree] at h
    omega
  have hconst : q = C (q.coeff 0) := by
    ext m
    by_cases hm : m=0
    · simp [hm]
    · rw [coeff_C]
      simp [Ne.symm hm]
      by_contra h
      apply hm
      ext i
      have hi := monomial_le_degreeOf i (mem_support_iff.mpr h)
      rw [hq] at hi
      exact Nat.eq_zero_of_le_zero hi
  exact ⟨q.coeff 0,(congrArg (laughlin N * ·) hconst).trans (mul_comm _ _)⟩

private theorem diff_irreducible {N : ℕ} {i j : Fin N} (h : i ≠ j) :
    Irreducible (X i - X j : Poly N) := by
  apply irreducible_of_totalDegree_eq_one
  · have hl := degreeOf_le_totalDegree (X i - X j : Poly N) i
    rw [degree_diff i i j h] at hl
    have hu := totalDegree_sub (X i : Poly N) (X j)
    simp [h] at hl hu
    omega
  · intro c hc
    obtain ⟨d,hd⟩ := exists_coeff_ne_zero (diff_ne_zero h)
    exact isUnit_iff_ne_zero.mpr fun hz => hd (by simpa [hz] using hc d)

private theorem diff_relprime {N : ℕ} {i j k l : Fin N} (hij : i<j) (hkl : k<l)
    (hne : (i,j) ≠ (k,l)) : IsRelPrime (X i-X j : Poly N) (X k-X l) := by
  apply (diff_irreducible hij.ne).isRelPrime_iff_not_dvd.mpr
  rintro ⟨q,hq⟩
  have hn : q ≠ 0 := by
    intro hz
    exact diff_ne_zero hkl.ne (by simpa [hz] using hq)
  have hd (t : Fin N) := congrArg (fun p : Poly N => p.degreeOf t) hq
  have inc (t : Fin N) (ht : t=i ∨ t=j) : t=k ∨ t=l := by
    have hh := hd t
    change (X k-X l : Poly N).degreeOf t = ((X i-X j)*q).degreeOf t at hh
    rw [degreeOf_mul_eq (diff_ne_zero hij.ne) hn,degree_diff _ _ _ hkl.ne,degree_diff _ _ _ hij.ne] at hh
    by_contra! h
    rcases ht with rfl|rfl <;> simp_all <;> omega
  rcases inc i (Or.inl rfl) with hik|hil <;> rcases inc j (Or.inr rfl) with hjk|hjl
  · exact hij.ne (hik.trans hjk.symm)
  · exact hne (Prod.ext hik hjl)
  · omega
  · exact hij.ne (hil.trans hjl.symm)

/-- Independent cubic coincidence factors combine into the full Laughlin
factor; no assumption on simultaneous intersections of diagonals is needed. -/
theorem laughlin_dvd_of_pair_cubes {N : ℕ} {p : Poly N}
    (hc : ∀ i j : Fin N, i<j → (X i-X j : Poly N)^3 ∣ p) : laughlin N ∣ p := by
  classical
  let edges := (univ : Finset (Fin N × Fin N)).filter (fun e => e.1 < e.2)
  let factor := fun e : Fin N × Fin N => (X e.1-X e.2 : Poly N)^3
  have he (e : Fin N × Fin N) : e ∈ edges ↔ e.1 < e.2 := by simp [edges]
  have hf : laughlin N = ∏ e ∈ edges, factor e := by
    rw [prod_finset_product edges univ Ioi (fun e => by simp [edges])]
    simp [laughlin,factor,Finset.prod_pow]
  rw [hf]
  apply Finset.prod_dvd_of_isRelPrime
  · intro e he₁ d hd₁ hne
    exact ((diff_relprime ((he e).mp he₁) ((he d).mp hd₁) hne).pow_left).pow_right
  · intro e h
    exact hc _ _ ((he e).mp h)

theorem pair_cubic_at_minimal_flux {N : ℕ} {p : Poly N}
    (hc : ∀ i j : Fin N, i<j → (X i-X j : Poly N)^3 ∣ p)
    (hb : ∀ i, p.degreeOf i ≤ 3*(N-1)) : ∃ c : ℂ, p = C c * laughlin N :=
  multiple_at_minimal_flux (laughlin_dvd_of_pair_cubes hc) hb

theorem pair_cubes_dvd_laughlin {N : ℕ} (i j : Fin N) (h : i<j) :
    (X i-X j : Poly N)^3 ∣ laughlin N := by
  apply pow_dvd_pow_of_dvd
  exact (Finset.dvd_prod_of_mem (fun j => (X i-X j : Poly N)) (mem_Ioi.mpr h)).trans
    (Finset.dvd_prod_of_mem (fun i => ∏ j ∈ Ioi i, (X i-X j : Poly N)) (mem_univ i))

/-- Exact polynomial zero-mode criterion at the minimal flux, in an affine chart. -/
theorem diagonal_conditions_iff {N : ℕ} (p : Poly N) :
    ((∀ i j : Fin N, i<j → (X i-X j : Poly N)^3 ∣ p) ∧
      (∀ i, p.degreeOf i ≤ 3*(N-1))) ↔ ∃ c : ℂ, p = C c * laughlin N := by
  constructor
  · rintro ⟨hd,hb⟩
    exact pair_cubic_at_minimal_flux hd hb
  · rintro ⟨c,rfl⟩
    constructor
    · intro i j hij
      exact dvd_mul_of_dvd_right (pair_cubes_dvd_laughlin i j hij) _
    · intro i
      simpa [laughlin_degree] using degreeOf_mul_le i (C c : Poly N) (laughlin N)

theorem flux_six_three_polynomial_test :
    laughlin 3 ≠ 0 ∧ (∀ i, (laughlin 3).degreeOf i = 6) ∧
      (∀ i j : Fin 3, i<j → (X i-X j : Poly 3)^3 ∣ laughlin 3) :=
  ⟨laughlin_ne_zero 3,laughlin_degree 3,pair_cubes_dvd_laughlin⟩

end VortexGap.SpherePolynomial
end

noncomputable section
namespace VortexGap.SpherePolynomial
open MvPolynomial
variable {N : ℕ}
private abbrev Line (N : ℕ) := Polynomial (Poly N)
private def half : Poly N := C (1/2 : ℂ)
private theorem half_add : (half : Poly N) + half = 1 := by
  rw [half,← map_add]; norm_num

/-- Substitute the two arguments by their common midpoint plus/minus t,
leaving every spectator unchanged. -/
def relativeLine (i j : Fin N) : Poly N →ₐ[ℂ] Line N :=
  aeval fun k => if k=i then Polynomial.C ((X i+X j)*half) + Polynomial.X
    else if k=j then Polynomial.C ((X i+X j)*half) - Polynomial.X
    else Polynomial.C (X k)

private def restore (i j : Fin N) : Line N →ₐ[ℂ] Poly N :=
  (Polynomial.aeval ((X i-X j)*half : Poly N)).restrictScalars ℂ

private theorem restore_line (i j : Fin N) (h : i ≠ j) (p : Poly N) :
    restore i j (relativeLine i j p) = p := by
  have hh : (restore i j).comp (relativeLine i j) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro k
    by_cases hi : k=i
    · subst k
      simp [restore,relativeLine]
      linear_combination X i * half_add
    by_cases hj : k=j
    · subst k
      simp [restore,relativeLine,h.symm]
      linear_combination X j * half_add
    simp [restore,relativeLine,hi,hj]
  exact AlgHom.congr_fun hh p

theorem line_cube_iff (i j : Fin N) (h : i ≠ j) (p : Poly N) :
    Polynomial.X^3 ∣ relativeLine i j p ↔ (X i-X j : Poly N)^3 ∣ p := by
  constructor
  · rintro ⟨q,hq⟩
    use half^3 * restore i j q
    have hh := congrArg (restore i j) hq
    rw [restore_line _ _ h,map_mul,map_pow] at hh
    simpa [restore,mul_pow,mul_assoc] using hh
  · rintro ⟨q,rfl⟩
    have hh : relativeLine i j (X i-X j) = (2:Line N)*Polynomial.X := by
      simp [relativeLine,h.symm]; ring
    use (2:Line N)^3 * relativeLine i j q
    rw [map_mul,map_pow,hh]; ring

private def reflect : Line N →ₐ[ℂ] Line N :=
  (Polynomial.aeval (-Polynomial.X : Line N)).restrictScalars ℂ

private theorem reflect_coeff (q : Line N) (d : ℕ) :
    (reflect q).coeff d = (-1)^d * q.coeff d := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add,hp,hq,mul_add]
  | monomial n a =>
    change (Polynomial.aeval (-Polynomial.X : Line N) _).coeff d = _
    rw [Polynomial.aeval_monomial]
    change (Polynomial.C a * (-Polynomial.X)^n : Line N).coeff d = _
    rw [show (-Polynomial.X : Line N) = Polynomial.C (-1) * Polynomial.X by simp; ring,
      mul_pow,← Polynomial.C_pow,← mul_assoc,← Polynomial.C_mul,Polynomial.coeff_C_mul_X_pow]
    by_cases h : n=d
    · subst n; simp [mul_comm]
    · simp [Polynomial.coeff_monomial,h,Ne.symm h]

private theorem reflect_line (i j : Fin N) (h : i≠j) (p : Poly N) :
    reflect (relativeLine i j p) = relativeLine i j (rename (Equiv.swap i j) p) := by
  have he : reflect.comp (relativeLine i j) = (relativeLine i j).comp (rename (Equiv.swap i j)) := by
    apply MvPolynomial.algHom_ext
    intro k
    by_cases hi : k=i
    · subst k
      simp [reflect,relativeLine,h.symm,sub_eq_add_neg]
    by_cases hj : k=j
    · subst k
      simp [reflect,relativeLine,h.symm,sub_eq_add_neg]
    simp [reflect,relativeLine,hi,hj,Equiv.swap_apply_of_ne_of_ne hi hj]
  exact AlgHom.congr_fun he p

/-- The symbolic first relative derivative on the pair diagonal. -/
def diagonalJet (i j : Fin N) (p : Poly N) : Poly N :=
  (relativeLine i j p).derivative.eval 0

theorem jet_zero_iff_cube (i j : Fin N) (h : i ≠ j) (p : Poly N)
    (hs : rename (Equiv.swap i j) p = -p) :
    diagonalJet i j p = 0 ↔ (X i-X j : Poly N)^3 ∣ p := by
  let q := relativeLine i j p
  have ho : reflect q = -q := by rw [reflect_line i j h,hs,map_neg]
  have even_vanish (d : ℕ) (hd : Even d) : q.coeff d = 0 := by
    have he := reflect_coeff q d
    rw [ho,Polynomial.coeff_neg,hd.neg_one_pow,one_mul] at he
    exact CharZero.eq_neg_self_iff.mp he.symm
  have jet : diagonalJet i j p = q.coeff 1 := by
    simp [diagonalJet,q,← Polynomial.coeff_zero_eq_eval_zero,Polynomial.coeff_derivative]
  rw [jet,← line_cube_iff i j h,Polynomial.X_pow_dvd_iff]
  constructor
  · intro hj d hd
    interval_cases d
    · exact even_vanish 0 (by decide)
    · exact hj
    · exact even_vanish 2 (by decide)
  · exact fun hc => hc 1 (by decide)

theorem alternating_zero_jets_at_flux {p : Poly N}
    (hs : ∀ i j : Fin N, i<j → rename (Equiv.swap i j) p = -p)
    (hb : ∀ i, p.degreeOf i ≤ 3*(N-1)) :
    (∀ i j : Fin N, i<j → diagonalJet i j p = 0) ↔ ∃ c : ℂ, p = C c * laughlin N := by
  rw [← diagonal_conditions_iff]
  exact ⟨fun hj => ⟨fun i j h => (jet_zero_iff_cube i j h.ne p (hs i j h)).mp (hj i j h),hb⟩,
    fun hh i j h => (jet_zero_iff_cube i j h.ne p (hs i j h)).mpr (hh.1 i j h)⟩

/-- The raw relative coordinate has contact jet two, fixing the
plus/minus convention. Its cube has zero jet, also with spectators. -/
theorem relative_jet_linear_cubic_test {N : ℕ} (i j : Fin N) (h : i≠j) :
    diagonalJet i j (X i-X j) = 2 ∧ diagonalJet i j ((X i-X j)^3) = 0 := by
  have he : relativeLine i j (X i-X j) = (2:Line N)*Polynomial.X := by
    simp [relativeLine,h.symm]; ring
  constructor
  · simp [diagonalJet,he,Polynomial.derivative_mul]
  · simp [diagonalJet,map_pow,he,Polynomial.derivative_pow,Polynomial.derivative_mul]

end VortexGap.SpherePolynomial
end

noncomputable section
namespace VortexGap.SpherePolynomial
open MvPolynomial
variable {N : ℕ}

def relativePoint (i j : Fin N) (z : Fin N → ℂ) (t : ℂ) (k : Fin N) : ℂ :=
  if k = i then (z i + z j) * (1/2) + t
  else if k = j then (z i + z j) * (1/2) - t else z k

theorem relativeLine_specialize (i j : Fin N) (z : Fin N → ℂ) (t : ℂ) (p : Poly N) :
    ((relativeLine i j p).map (eval z)).eval t = eval (relativePoint i j z t) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [relativeLine]
  | add p q hp hq => simp [map_add,hp,hq]
  | mul_X p k hp =>
    simp only [map_mul, Polynomial.map_mul, Polynomial.eval_mul, hp, eval_X]
    congr 1
    by_cases hi : k = i
    · subst k
      simp [relativeLine,relativePoint]
      left
      change eval z (C (1/2 : ℂ)) = _
      simp
    by_cases hj : k = j
    · subst k
      simp [relativeLine,relativePoint,hi]
      left
      change eval z (C (1/2 : ℂ)) = _
      simp
    simp [relativeLine,relativePoint,hi,hj]

theorem diagonalJet_hasDerivAt (i j : Fin N) (z : Fin N → ℂ) (p : Poly N) :
    HasDerivAt (fun t => eval (relativePoint i j z t) p) (eval z (diagonalJet i j p)) 0 := by
  have h := ((relativeLine i j p).map (eval z)).hasDerivAt 0
  simpa only [relativeLine_specialize, diagonalJet, Polynomial.derivative_map, Polynomial.eval_zero_map] using h

/-- Vanishing of actual coincidence derivatives at all affine configurations. -/
theorem pointwise_contact_at_flux {p : Poly N}
    (hs : ∀ i j : Fin N, i < j → rename (Equiv.swap i j) p = -p)
    (hb : ∀ i, p.degreeOf i ≤ 3*(N-1)) :
    (∀ i j : Fin N, i < j → ∀ z : Fin N → ℂ,
      deriv (fun t => eval (relativePoint i j z t) p) 0 = 0) ↔
      ∃ c : ℂ, p = C c * laughlin N := by
  rw [← alternating_zero_jets_at_flux hs hb]
  constructor
  · intro h i j hij
    apply MvPolynomial.funext
    intro z
    simpa only [map_zero, (diagonalJet_hasDerivAt i j z p).deriv] using h i j hij z
  · intro h i j hij z
    rw [(diagonalJet_hasDerivAt i j z p).deriv, h i j hij, map_zero]

end VortexGap.SpherePolynomial
end

noncomputable section
namespace VortexGap.SpherePolynomial
open MvPolynomial
variable {N : ℕ}

private theorem swap_cube {p : Poly N}
    (hs : ∀ a b : Fin N, a ≠ b → rename (Equiv.swap a b) p = -p)
    (i j a b : Fin N) (h : (X i-X j : Poly N)^3 ∣ p) :
    (X (Equiv.swap a b i)-X (Equiv.swap a b j) : Poly N)^3 ∣ p := by
  by_cases he : a=b
  · subst b
    simpa using h
  have hm := map_dvd (rename (R := ℂ) (Equiv.swap a b)).toRingHom h
  simpa [hs a b he] using hm

theorem head_cube_all_pairs {p : Poly (N+2)}
    (hs : ∀ a b : Fin (N+2), a ≠ b → rename (Equiv.swap a b) p = -p)
    (h : (X 0-X 1 : Poly (N+2))^3 ∣ p) (i j : Fin (N+2)) (hij : i ≠ j) :
    (X i-X j : Poly (N+2))^3 ∣ p := by
  let k := Equiv.swap 0 i (1 : Fin (N+2))
  have hk : k ≠ i := by
    have hdist := (Equiv.swap (0 : Fin (N+2)) i).injective.ne Fin.zero_ne_one.symm
    simpa [k] using hdist
  have h1 : (X i-X k : Poly (N+2))^3 ∣ p := by
    simpa [k] using swap_cube hs 0 1 0 i h
  simpa [Equiv.swap_apply_of_ne_of_ne hk.symm hij] using swap_cube hs i k k j h1

theorem head_jet_laughlin_iff {p : Poly (N+2)}
    (hs : ∀ a b : Fin (N+2), a ≠ b → rename (Equiv.swap a b) p = -p)
    (hb : ∀ i, p.degreeOf i ≤ 3*((N+2)-1)) :
    diagonalJet 0 1 p = 0 ↔ ∃ c : ℂ, p = C c * laughlin (N+2) := by
  rw [← alternating_zero_jets_at_flux (fun i j hij => hs i j hij.ne) hb]
  constructor
  · intro h i j hij
    apply (jet_zero_iff_cube i j hij.ne p (hs i j hij.ne)).mpr
    exact head_cube_all_pairs hs
      ((jet_zero_iff_cube 0 1 Fin.zero_ne_one p (hs 0 1 Fin.zero_ne_one)).mp h) i j hij.ne
  · intro h
    exact h 0 1 Fin.zero_lt_one

/-- All spectator positions and one relative real direction at every complex
center suffice to determine the Laughlin line. -/
theorem head_pointwise_laughlin_iff {p : Poly (N+2)}
    (hs : ∀ a b : Fin (N+2), a ≠ b → rename (Equiv.swap a b) p = -p)
    (hb : ∀ i, p.degreeOf i ≤ 3*((N+2)-1)) :
    (∀ s : ℂ, ∀ z : Fin N → ℂ, deriv (fun t : ℝ =>
      eval (Fin.cons (s+t) (Fin.cons (s-t) z)) p) 0 = 0) ↔
      ∃ c : ℂ, p = C c * laughlin (N+2) := by
  rw [← head_jet_laughlin_iff hs hb]
  have he (y : Fin (N+2) → ℂ) (t : ℂ) :
      relativePoint 0 1 y t = Fin.cons ((y 0+y 1)*(1/2)+t)
        (Fin.cons ((y 0+y 1)*(1/2)-t) (Fin.tail (Fin.tail y))) := by
    funext k
    refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => ?_) k) k <;>
      simp [relativePoint,Fin.tail]
    intro hk
    have hh := congrArg Fin.val hk
    simp at hh
  have hj (y : Fin (N+2) → ℂ) := (diagonalJet_hasDerivAt 0 1 y p).comp_ofReal.deriv
  simp only [he] at hj
  constructor
  · intro h
    apply MvPolynomial.funext
    intro y
    rw [map_zero,← hj]
    apply h
  · intro h s z
    have hh := hj (Fin.cons s (Fin.cons s z))
    simpa [h, Fin.tail,show (s+s)*(2:ℂ)⁻¹=s by ring] using hh

end VortexGap.SpherePolynomial
end

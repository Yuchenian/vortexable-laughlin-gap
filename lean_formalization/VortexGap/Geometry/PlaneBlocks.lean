import VortexGap.Geometry.PlaneBinomial
import VortexGap.Geometry.PlanePairCoefficients
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open Finset
open scoped InnerProduct ComplexConjugate

def planeBlockModes (n : ℕ) : Finset ℕ := (range (n+1)).filter (fun i => 2*i<n)

def planeBlockIndex (n : ℕ) (i : planeBlockModes n) : CountablePairIndex :=
  ⟨(i.val,n-i.val), by
    have h := (mem_filter.mp i.property).2
    omega⟩

theorem planeBlockIndex_injective (n : ℕ) : Function.Injective (planeBlockIndex n) := by
  intro i j h
  apply Subtype.ext
  exact congrArg (fun a : CountablePairIndex => a.val.1) h

theorem planeBlockIndex_total (n : ℕ) (i : planeBlockModes n) :
    (planeBlockIndex n i).val.1+(planeBlockIndex n i).val.2 = n := by
  have h := (mem_filter.mp i.property).2
  dsimp [planeBlockIndex]
  omega

/-- The actual completed pair-space vector supported on the ordered angular
momentum block. Finite support is exact here, not an orbital cutoff approximation. -/
def planeBlockVector (n : ℕ) : CountablePairSpace :=
  ∑ i : planeBlockModes n, (planeBlockCoefficient n i.val : ℂ) •
    lp.single 2 (planeBlockIndex n i) 1

theorem planeBlock_basis_inner (n : ℕ) (i j : planeBlockModes n) :
    inner ℂ (lp.single 2 (planeBlockIndex n i) 1 : CountablePairSpace)
      (lp.single 2 (planeBlockIndex n j) 1 : CountablePairSpace) = if i=j then 1 else 0 := by
  simp [lp.inner_single_left, lp.single_apply, Pi.single_apply, (planeBlockIndex_injective n).eq_iff]

theorem planeBlockVector_inner_self (n : ℕ) :
    inner ℂ (planeBlockVector n) (planeBlockVector n) =
      ∑ i : planeBlockModes n, ((planeBlockCoefficient n i.val)^2 : ℂ) := by
  simp only [planeBlockVector, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    planeBlock_basis_inner, Complex.conj_ofReal]
  simp [pow_two]

theorem planeBlockVector_norm_sq (n : ℕ) (hn : 0 < n) : ‖planeBlockVector n‖^2 = 1 := by
  calc
    _ = (inner ℂ (planeBlockVector n) (planeBlockVector n)).re := by
      simpa only [RCLike.re_eq_complex_re] using norm_sq_eq_re_inner (𝕜 := ℂ) (planeBlockVector n)
    _ = ∑ i : planeBlockModes n, (planeBlockCoefficient n i.val)^2 := by
      rw [planeBlockVector_inner_self]
      simp [← Complex.ofReal_pow]
    _ = 1 := by
      rw [Finset.sum_coe_sort (s := planeBlockModes n) (f := fun i : ℕ => planeBlockCoefficient n i ^ 2)]
      exact planeBlockCoefficient_sum_sq n hn

theorem planeBlock_basis_inner_ne (n m : ℕ) (h : n ≠ m)
    (i : planeBlockModes n) (j : planeBlockModes m) :
    inner ℂ (lp.single 2 (planeBlockIndex n i) 1 : CountablePairSpace)
      (lp.single 2 (planeBlockIndex m j) 1 : CountablePairSpace) = 0 := by
  have he : planeBlockIndex n i ≠ planeBlockIndex m j := by
    intro he
    have hn := planeBlockIndex_total n i
    have hm := planeBlockIndex_total m j
    rw [he] at hn
    exact h (hn.symm.trans hm)
  simp [lp.inner_single_left, lp.single_apply, he]

theorem planeBlockVector_orthogonal (n m : ℕ) (h : n ≠ m) :
    inner ℂ (planeBlockVector n) (planeBlockVector m) = 0 := by
  simp only [planeBlockVector, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    planeBlock_basis_inner_ne n m h, mul_zero, sum_const_zero]

/-- Every positive angular-momentum block participates in the actual countably
infinite orthonormal family in the completed pair space. -/
theorem planeBlockVector_orthonormal : Orthonormal ℂ (fun n : ℕ => planeBlockVector (n+1)) := by
  apply orthonormal_iff_ite.mpr
  intro i j
  by_cases h : i=j
  · subst j
    rw [ite_eq_left rfl, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow,
      planeBlockVector_norm_sq (i+1) (by omega)]
    rfl
  · rw [ite_eq_right h]
    exact planeBlockVector_orthogonal _ _ (by omega)

theorem planeBlockVector_zero : planeBlockVector 0 = 0 := by
  unfold planeBlockVector
  apply sum_eq_zero
  intro i _
  have h : 2*i.val < 0 := (mem_filter.mp i.property).2
  omega

end VortexGap.Fermion

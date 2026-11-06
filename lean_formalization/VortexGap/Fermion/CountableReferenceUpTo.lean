import VortexGap.Fermion.CountableSectorExtension
import VortexGap.Fermion.CountablePairLift
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators ComplexOrder

/-- Bounded reference operator on sectors 0,...,N, zero on higher sectors.
This is an exact particle-number decomposition, not an orbital approximation. -/
def countableReferenceUpTo (N : ℕ) (Q : CountablePairSpace →L[ℂ] CountablePairSpace) :
    CountableSpace →L[ℂ] CountableSpace :=
  ∑ k ∈ Finset.range (N+1), countableSectorExtend k (countablePairLift k Q)

theorem countableReferenceUpTo_apply_sector (N K : ℕ) (hK : K ≤ N)
    (Q : CountablePairSpace →L[ℂ] CountablePairSpace) (x : countableSector K) :
    countableReferenceUpTo N Q (x : CountableSpace) = (countablePairLift K Q x : CountableSpace) := by
  rw [countableReferenceUpTo]
  simp only [sum_apply]
  rw [Finset.sum_eq_single K]
  · exact countableSectorExtend_apply_self K _ x
  · intro j hj hjK
    exact countableSectorExtend_apply_other j K hjK _ x
  · intro h
    exact False.elim (h (Finset.mem_range.mpr (by omega)))

theorem countableReferenceUpTo_apply_above (N K : ℕ) (hK : N < K)
    (Q : CountablePairSpace →L[ℂ] CountablePairSpace) (x : countableSector K) :
    countableReferenceUpTo N Q (x : CountableSpace) = 0 := by
  rw [countableReferenceUpTo]
  simp only [sum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  have hj' := Finset.mem_range.mp hj
  exact countableSectorExtend_apply_other j K (by omega) _ x

theorem countableReferenceUpTo_square (N : ℕ)
    (Q : CountablePairSpace →L[ℂ] CountablePairSpace) :
    countableReferenceUpTo N Q * countableReferenceUpTo N Q =
      ∑ k ∈ Finset.range (N+1),
        countableSectorExtend k (countablePairLift k Q * countablePairLift k Q) := by
  rw [countableReferenceUpTo, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_eq_single k]
  · exact countableSectorExtend_mul k _ _
  · intro j hj hjk
    exact countableSectorExtend_mul_other k j (Ne.symm hjk) _ _
  · intro h
    exact False.elim (h hk)

theorem countableReferenceUpTo_positive (N : ℕ)
    (Q : CountablePairSpace →L[ℂ] CountablePairSpace) (hQ : Q.IsPositive) :
    (countableReferenceUpTo N Q).IsPositive :=
  ContinuousLinearMap.isPositive_sum _ (fun k _ =>
    countableSectorExtend_positive k _ (countablePairLift_positive k Q hQ))

/-- The only spectral input is the original reference inequality in each
reachable particle-number sector. No enlarged-space inequality is assumed. -/
theorem countableReferenceUpTo_gap (N : ℕ)
    (Q : CountablePairSpace →L[ℂ] CountablePairSpace) (γ : ℝ)
    (h : ∀ k ≤ N, (countablePairLift k Q * countablePairLift k Q -
      (γ : ℂ) • countablePairLift k Q).IsPositive) :
    (countableReferenceUpTo N Q * countableReferenceUpTo N Q -
      (γ : ℂ) • countableReferenceUpTo N Q).IsPositive := by
  rw [countableReferenceUpTo_square, countableReferenceUpTo, Finset.smul_sum,
    ← Finset.sum_sub_distrib]
  simp_rw [← countableSectorExtend_smul, ← countableSectorExtend_sub]
  apply ContinuousLinearMap.isPositive_sum
  intro k hk
  exact countableSectorExtend_positive k _ (h k (by
    have := Finset.mem_range.mp hk
    omega))
end VortexGap.Fermion

import VortexGap.Fermion.CountableEnvironmentAmplification
import VortexGap.Fermion.CountableSplitSectors
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct

theorem countableSector_orthogonal {K L : ℕ} {x y : CountableSpace}
    (hx : x ∈ countableSector K) (hy : y ∈ countableSector L) (hKL : K ≠ L) :
    inner ℂ x y = 0 := by
  rw [lp.inner_eq_tsum]
  calc
    _ = ∑' A : Finset ℕ, (0 : ℂ) := by
      apply tsum_congr
      intro A
      by_cases hA : A.card = K
      · rw [hy A (by omega), inner_zero_right]
      · rw [hx A hA, inner_zero_left]
    _ = 0 := tsum_zero

theorem countableSector_adjoint_subtype_self (N : ℕ) :
    (countableSector N).subtypeL.adjoint.comp (countableSector N).subtypeL = 1 := by
  apply (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp
  intro x
  rfl

theorem countableSector_adjoint_subtype_other (K L : ℕ) (hKL : K ≠ L) :
    (countableSector K).subtypeL.adjoint.comp (countableSector L).subtypeL = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (y : CountableSpace) (x : CountableSpace) = inner ℂ y 0
  rw [inner_zero_right]
  exact countableSector_orthogonal y.property x.property hKL

/-- Each spectator occupation leaves precisely N-card(B) reference particles.
The statement also covers card(B)>N, where the whole fiber vanishes. -/
theorem countableEnvironmentFiber_sector {N : ℕ} {x : CountableSplitSpace}
    (hx : x ∈ countableSplitSector N) (B : Finset ℕ) :
    countableEnvironmentFiber x B ∈ countableSector (N - B.card) := by
  intro A hA
  exact hx (A,B) (by change A.card + B.card ≠ N; omega)

theorem countableEnvironmentFiber_above_total {N : ℕ} {x : CountableSplitSpace}
    (hx : x ∈ countableSplitSector N) (B : Finset ℕ) (hB : N < B.card) :
    countableEnvironmentFiber x B = 0 := by
  ext A
  change x (A,B) = 0
  exact hx (A,B) (by change A.card + B.card ≠ N; omega)

theorem countableEnvironmentFiber_reference_range (N : ℕ) (B : Finset ℕ) :
    N - B.card ≤ N := Nat.sub_le _ _
end VortexGap.Fermion

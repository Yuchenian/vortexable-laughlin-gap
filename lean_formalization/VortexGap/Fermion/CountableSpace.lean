import VortexGap.Fermion.Finite
import Mathlib.Analysis.InnerProductSpace.l2Space

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct BigOperators ComplexConjugate ENNReal

/-- Full occupation Hilbert space over countably many modes; no particle-number cutoff. -/
abbrev CountableSpace := lp (fun _ : Finset ℕ => ℂ) 2

def countableKet (A : Finset ℕ) : CountableSpace := lp.single 2 A 1

def occupationIndex {n : ℕ} (A : Finset (Fin n)) : Finset ℕ :=
  A.map ⟨Fin.val, Fin.val_injective⟩

theorem occupationIndex_injective (n : ℕ) : Function.Injective (@occupationIndex n) :=
  Finset.map_injective _

theorem occupationIndex_card {n : ℕ} (A : Finset (Fin n)) :
    (occupationIndex A).card = A.card := Finset.card_map _

theorem countableKet_inner_left (A : Finset ℕ) (x : CountableSpace) :
    inner ℂ (countableKet A) x = x A := by
  simp [countableKet, lp.inner_single_left, RCLike.inner_apply]

theorem countableKet_inner (A B : Finset ℕ) :
    inner ℂ (countableKet A) (countableKet B) = if A=B then 1 else 0 := by
  rw [countableKet_inner_left]
  change lp.single (E := fun _ : Finset ℕ => ℂ) 2 B 1 A = _
  by_cases h : A = B
  · subst B; simp
  · rw [if_neg h]; exact lp.single_apply_ne 2 B 1 h

theorem countableKet_norm (A : Finset ℕ) : ‖countableKet A‖ = 1 := by
  simp [countableKet, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]

/-- Zero-extension of the actual finite-mode occupation amplitudes. -/
def countableEmbedLinear (n : ℕ) : Space n →ₗ[ℂ] CountableSpace where
  toFun x := ∑ A, x A • countableKet (occupationIndex A)
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' z x := by simp [Finset.smul_sum, smul_smul]

theorem countableEmbedLinear_coefficient {n : ℕ} (x : Space n) (A : Finset (Fin n)) :
    countableEmbedLinear n x (occupationIndex A) = x A := by
  rw [← countableKet_inner_left]
  change inner ℂ (countableKet (occupationIndex A))
    (∑ B, x B • countableKet (occupationIndex B)) = x A
  simp [inner_sum, inner_smul_right, countableKet_inner, (occupationIndex_injective n).eq_iff]

theorem countableEmbedLinear_inner {n : ℕ} (x y : Space n) :
    inner ℂ (countableEmbedLinear n x) (countableEmbedLinear n y) = inner ℂ x y := by
  change inner ℂ (∑ A, x A • countableKet (occupationIndex A)) (countableEmbedLinear n y) = _
  simp only [sum_inner, inner_smul_left, countableKet_inner_left, countableEmbedLinear_coefficient]
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

def countableEmbed (n : ℕ) : Space n →ₗᵢ[ℂ] CountableSpace where
  toLinearMap := countableEmbedLinear n
  norm_map' := (LinearMap.norm_map_iff_inner_map_map (countableEmbedLinear n)).mpr countableEmbedLinear_inner

theorem countableEmbed_ket {n : ℕ} (A : Finset (Fin n)) :
    countableEmbed n (ket A) = countableKet (occupationIndex A) := by
  simp [countableEmbed, countableEmbedLinear, ket, PiLp.single_apply]

theorem countableSpace_hasSum (x : CountableSpace) :
    HasSum (fun A => x A • countableKet A) x := by
  simpa only [countableKet, ← lp.single_smul, smul_eq_mul, mul_one]
    using lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x

end VortexGap.Fermion


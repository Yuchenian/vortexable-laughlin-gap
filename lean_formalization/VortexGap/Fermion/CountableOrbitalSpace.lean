import VortexGap.Fermion.CountableBasis

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open Filter
open scoped BigOperators InnerProduct ComplexConjugate ENNReal Topology

/-- Actual one-particle Hilbert space, with the l2 norm rather than a Finsupp norm. -/
abbrev CountableOrbital := lp (fun _ : ℕ => ℂ) 2

def orbitalKet (j : ℕ) : CountableOrbital := lp.single 2 j 1

/-- Finite orbital combinations embedded in the complete one-particle Hilbert space. -/
def orbitalEmbed : (ℕ →₀ ℂ) →ₗ[ℂ] CountableOrbital :=
  Finsupp.linearCombination ℂ orbitalKet

theorem orbitalKet_inner_left (j : ℕ) (v : CountableOrbital) :
    inner ℂ (orbitalKet j) v = v j := by
  simp [orbitalKet, lp.inner_single_left, RCLike.inner_apply]

theorem orbitalKet_norm (j : ℕ) : ‖orbitalKet j‖ = 1 := by
  simp [orbitalKet, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]

theorem orbitalEmbed_single (j : ℕ) (z : ℂ) :
    orbitalEmbed (Finsupp.single j z) = lp.single 2 j z := by
  simp [orbitalEmbed, orbitalKet, ← lp.single_smul]

theorem orbitalEmbed_coefficient (v : ℕ →₀ ℂ) (j : ℕ) : orbitalEmbed v j = v j := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw =>
      change (orbitalEmbed (v + w)) j = v j + w j
      rw [map_add]
      change orbitalEmbed v j + orbitalEmbed w j = _
      rw [hv, hw]
  | single i z =>
      by_cases h : i = j
      · subst j; simp [orbitalEmbed_single]
      · simp [orbitalEmbed_single, lp.single_apply, Finsupp.single_apply, h, Ne.symm h]

theorem orbitalEmbed_injective : Function.Injective orbitalEmbed := by
  intro v w h
  ext j
  simpa only [orbitalEmbed_coefficient] using congrArg (fun x : CountableOrbital => x j) h

theorem orbitalEmbed_inner (v w : ℕ →₀ ℂ) :
    inner ℂ (orbitalEmbed v) (orbitalEmbed w) =
      ∑ j ∈ v.support, conj (v j) * w j := by
  change inner ℂ (∑ j ∈ v.support, v j • orbitalKet j) (orbitalEmbed w) = _
  simp only [sum_inner, inner_smul_left, orbitalKet_inner_left, orbitalEmbed_coefficient]

theorem orbital_hasSum (v : CountableOrbital) :
    HasSum (fun j => v j • orbitalKet j) v := by
  simpa only [orbitalKet, ← lp.single_smul, smul_eq_mul, mul_one]
    using lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) v

theorem orbitalEmbed_dense : DenseRange orbitalEmbed := by
  intro v
  have h : Tendsto (fun s : Finset ℕ => ∑ j ∈ s, v j • orbitalKet j) atTop (𝓝 v) := by
    simpa only [HasSum, SummationFilter.unconditional_filter] using orbital_hasSum v
  apply mem_closure_of_tendsto h
  exact Filter.Eventually.of_forall fun s =>
    ⟨∑ j ∈ s, Finsupp.single j (v j), by simp [map_sum, orbitalEmbed, Finsupp.linearCombination_single]⟩

end VortexGap.Fermion

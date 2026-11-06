import VortexGap.Fermion.PairBounds
import OAI.Analysis.LaughlinGap.Creation

/-! Exact occupation-to-antisymmetric-tensor identification for every n and N.
The normalized coefficient is 1/sqrt(N!), including the zero-mode vacuum.
This module does not construct a second-quantized operator. -/
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators InnerProduct
open OAI.LaughlinGap.Occupation

abbrev TensorSpace (n N : ℕ) := EuclideanSpace ℂ (Fin N → Fin n)

def antisymmetricTensors (n N : ℕ) : Submodule ℂ (TensorSpace n N) where
  carrier := {ψ | ∀ (i j : Fin N), i ≠ j → ∀ a, ψ (a ∘ Equiv.swap i j) = -ψ a}
  zero_mem' := by intros i j hij a; simp
  add_mem' := by
    intro ψ φ hψ hφ i j hij a
    change ψ (a ∘ Equiv.swap i j) + φ (a ∘ Equiv.swap i j) = -(ψ a + φ a)
    rw [hψ i j hij a, hφ i j hij a, neg_add]
  smul_mem' := by
    intro c ψ hψ i j hij a
    change c * ψ (a ∘ Equiv.swap i j) = -(c * ψ a)
    rw [hψ i j hij a, mul_neg]

theorem inSector_iff_homogeneous {n N : ℕ} (x : Space n) :
    InSector N x ↔ Homogeneous N x := Iff.rfl

/-- All one-particle dimensions, including zero. -/
theorem tensorReadout_antisymmetric {n N : ℕ} (x : Space n) :
    normalizedReadout n N x ∈ antisymmetricTensors n N := by
  intro i j hij a
  simp only [normalizedReadout_apply, word_ofFn_swap a i j hij,
    LinearMap.neg_apply, PiLp.neg_apply, mul_neg]

def tensorCoordinates (n N : ℕ) : TensorSpace n N →ₗ[ℂ] ExteriorCoordinates n N where
  toFun ψ := WithLp.toLp 2 (fun A => (Real.sqrt (N.factorial : ℝ) : ℂ) *
    ψ (increasingConfiguration A))
  map_add' ψ φ := by ext A; exact mul_add _ _ _
  map_smul' c ψ := by ext A; exact mul_left_comm _ _ _

theorem tensorCoordinates_readout {n N : ℕ} (x : Space n) :
    tensorCoordinates n N (normalizedReadout n N x) = sectorReadout n N x := by
  have hs : (Real.sqrt (N.factorial : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast Nat.factorial_pos N))
  ext A
  change (Real.sqrt (N.factorial : ℝ) : ℂ) *
    normalizedReadout n N x (increasingConfiguration A) = x A.val
  rw [normalizedReadout_increasing]
  push_cast
  field_simp

theorem tensorReadout_coordinates {n N : ℕ} (ψ : antisymmetricTensors n N) :
    normalizedReadout n N (sectorInclusion n N (tensorCoordinates n N ψ)) =
      (ψ : TensorSpace n N) := by
  cases n with
  | zero =>
    cases N with
    | zero =>
      ext a
      have he (A : BasisLabel 0 0) : increasingConfiguration A = a := Subsingleton.elim _ _
      simp [normalizedReadout_apply, List.ofFn_zero, word_nil,
        sectorInclusion_apply, tensorCoordinates, he]
    | succ N =>
      ext a
      exact Fin.elim0 (a 0)
  | succ d =>
    change normalizedReadout (d + 1) N
      (sectorInclusion (d + 1) N (coordinatesFromTensor d N ψ)) = _
    exact readout_coordinatesFromTensor ψ.property

theorem tensorReadout_norm_sq {n N : ℕ} {x : Space n} (hx : InSector N x) :
    ‖normalizedReadout n N x‖ ^ 2 = ‖x‖ ^ 2 := normalizedReadout_norm_sq hx

/-- The complete actual N-sector, not only decomposable states, is unitarily
identified with all antisymmetric tensors. The factorial normalization is explicit. -/
def sectorTensorIsometry (n N : ℕ) : particleSector n N ≃ₗᵢ[ℂ] antisymmetricTensors n N where
  toFun x := ⟨normalizedReadout n N (x : Space n), tensorReadout_antisymmetric _⟩
  invFun ψ := ⟨sectorInclusion n N (tensorCoordinates n N ψ), sectorInclusion_homogeneous _⟩
  left_inv x := Subtype.ext (by
    change sectorInclusion n N (tensorCoordinates n N (normalizedReadout n N (x : Space n))) =
      (x : Space n)
    rw [tensorCoordinates_readout, sectorInclusion_readout x.property])
  right_inv ψ := Subtype.ext (tensorReadout_coordinates ψ)
  map_add' x y := Subtype.ext (map_add (normalizedReadout n N) (x : Space n) (y : Space n))
  map_smul' z x := Subtype.ext (map_smul (normalizedReadout n N) z (x : Space n))
  norm_map' x := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (tensorReadout_norm_sq x.property)

theorem sectorTensorIsometry_apply {n N : ℕ} (x : particleSector n N) (a : Fin N → Fin n) :
    (sectorTensorIsometry n N x : TensorSpace n N) a =
      ((Real.sqrt (N.factorial : ℝ))⁻¹ : ℂ) * word (List.ofFn a) (x : Space n) ∅ := rfl

end VortexGap.Fermion

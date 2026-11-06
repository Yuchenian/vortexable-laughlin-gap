import VortexGap.Fermion.ExteriorPower

/-! Exact compatibility of the all-N tensor construction with the existing
normalized CAR pair embedding and exterior square. No dilation is assumed. -/
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators InnerProduct ComplexConjugate
open OAI.LaughlinGap.Occupation

theorem annihilate_basis {n : ℕ} (i : Fin n) :
    annihilate (PiLp.single 2 i (1 : ℂ)) = annihilateMode i := by
  simp [annihilate, PiLp.single_apply]

theorem rawReadout_pair_wedge {n : ℕ} (u v : EuclideanSpace ℂ (Fin n)) (a : Fin 2 → Fin n) :
    rawReadout n 2 (pairEmbed (wedgePair u v)) a =
      u (a 0) * v (a 1) - v (a 0) * u (a 1) := by
  rw [rawReadout_apply, pairEmbed_wedge]
  simp only [List.ofFn_succ, List.ofFn_zero, word_cons, word_nil,
    one_mul, Module.End.mul_apply, Fin.succ_zero_eq_one]
  change (annihilateMode (a 1) (annihilateMode (a 0) (create u (create v (ket ∅))))) ∅ = _
  rw [← annihilate_basis (a 0), ← annihilate_basis (a 1), vector_annihilate_two_create]
  simp only [map_sub, map_smul, vector_create_vacuum]
  simp [EuclideanSpace.inner_single_left, ket]

def tensorPure {n N : ℕ} (v : Fin N → EuclideanSpace ℂ (Fin n)) : TensorSpace n N :=
  WithLp.toLp 2 (fun a => ∏ i, v i (a i))

theorem tensorPower_pure {n m N : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m))
    (v : Fin N → EuclideanSpace ℂ (Fin n)) :
    tensorPower A N (tensorPure v) = tensorPure (fun i => A (v i)) := by
  ext a
  rw [tensorPower_apply]
  change (∑ b : Fin N → Fin n, (∏ i, A (PiLp.single 2 (b i) 1) (a i)) * (∏ i, v i (b i))) =
    ∏ i, A (v i) (a i)
  calc
    _ = ∑ b : Fin N → Fin n, ∏ i, A (PiLp.single 2 (b i) 1) (a i) * v i (b i) := by
      simp only [Finset.prod_mul_distrib]
    _ = ∏ i, ∑ j, A (PiLp.single 2 j 1) (a i) * v i j :=
      (Fintype.prod_sum (fun (i : Fin N) (j : Fin n) => A (PiLp.single 2 j 1) (a i) * v i j)).symm
    _ = _ := Finset.prod_congr rfl fun i _ => (orbital_map_apply A _ _).symm

theorem normalizedReadout_pair_wedge {n : ℕ} (u v : EuclideanSpace ℂ (Fin n)) :
    normalizedReadout n 2 (pairEmbed (wedgePair u v)) =
      (Real.sqrt 2 : ℂ)⁻¹ • (tensorPure ![u, v] - tensorPure ![v, u]) := by
  ext a
  change ((Real.sqrt ((Nat.factorial 2) : ℝ))⁻¹ : ℂ) * rawReadout n 2 (pairEmbed (wedgePair u v)) a = _
  rw [rawReadout_pair_wedge]
  norm_num [tensorPure, Fin.prod_univ_succ, PiLp.smul_apply, PiLp.sub_apply]
  rfl

theorem tensorPower_pair_wedge {n m : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m))
    (u v : EuclideanSpace ℂ (Fin n)) :
    tensorPower A 2 (normalizedReadout n 2 (pairEmbed (wedgePair u v))) =
      normalizedReadout m 2 (pairEmbed (wedgePair (A u) (A v))) := by
  rw [normalizedReadout_pair_wedge, normalizedReadout_pair_wedge,
    map_smul, map_sub, tensorPower_pure, tensorPower_pure]
  rfl

def pairSectorEmbed {n : ℕ} : PairSpace n →ₗ[ℂ] particleSector n 2 where
  toFun p := ⟨pairEmbed p, pairEmbed_sector p⟩
  map_add' p q := Subtype.ext (map_add pairEmbed p q)
  map_smul' z p := Subtype.ext (map_smul pairEmbed z p)

theorem pairSectorEmbed_apply {n : ℕ} (p : PairSpace n) :
    (pairSectorEmbed p : Space n) = pairEmbed p := rfl

theorem exteriorPower_wedge {n m : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m))
    (u v : EuclideanSpace ℂ (Fin n)) :
    exteriorPower A 2 (pairSectorEmbed (wedgePair u v)) =
      pairSectorEmbed (wedgePair (A u) (A v)) := by
  apply (sectorTensorIsometry m 2).injective
  rw [exteriorPower_tensor]
  apply Subtype.ext
  exact tensorPower_pair_wedge A u v

/-- Equality of the independently constructed all-N and CAR-based degree-two actions. -/
theorem exteriorPower_pairEmbed {n m : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)) (p : PairSpace n) :
    exteriorPower A 2 (pairSectorEmbed p) = pairSectorEmbed (exteriorSquare A p) := by
  have hb (b : PairIndex n) : exteriorPower A 2 (pairSectorEmbed (pairBasis b)) =
      pairSectorEmbed (exteriorSquare A (pairBasis b)) := by
    rw [← wedgePair_basis b, exteriorSquare_wedge]
    exact exteriorPower_wedge A _ _
  conv_lhs => rw [← pairBasis_expansion p]
  conv_rhs => rw [← pairBasis_expansion p]
  simp only [map_sum, map_smul, hb]

end VortexGap.Fermion

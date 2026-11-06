import VortexGap.Fermion.Pair

/-! Concrete normalized complex wedges and their exterior-square functor.
No arbitrary-N exterior functor or Fock dilation is asserted here. -/
open scoped BigOperators InnerProduct ComplexConjugate
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion

private theorem sum_orderedPairs {n : ℕ} {E : Type*} [AddCommMonoid E]
    (f : Fin n → Fin n → E) :
    (∑ a : PairIndex n, f a.val.1 a.val.2) =
      ∑ i, ∑ j, if i < j then f i j else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun a : Fin n × Fin n => a.1 < a.2))
    (by simp) (fun a => f a.1 a.2), Finset.sum_filter, Fintype.sum_prod_type]

/-- Split a zero-diagonal double sum into the two orders of each unordered pair. -/
theorem sum_split_orderedPairs {n : ℕ} {E : Type*} [AddCommMonoid E]
    (f : Fin n → Fin n → E) (hf : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) = ∑ a : PairIndex n, (f a.val.1 a.val.2 + f a.val.2 a.val.1) := by
  have h (i j : Fin n) : f i j =
      (if i < j then f i j else 0) + (if j < i then f i j else 0) := by
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [hij, not_lt_of_gt hij]
    · subst j; simp [hf]
    · simp [hij, not_lt_of_gt hij]
  calc
    _ = ∑ i, ∑ j, ((if i < j then f i j else 0) +
        (if j < i then f i j else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_congr rfl fun j _ => h i j
    _ = (∑ i, ∑ j, if i < j then f i j else 0) +
        (∑ i, ∑ j, if j < i then f i j else 0) := by
      simp only [Finset.sum_add_distrib]
    _ = _ := by
      rw [Finset.sum_comm (f := fun i j => if j < i then f i j else 0)]
      rw [← sum_orderedPairs f, ← sum_orderedPairs (fun i j => f j i)]
      rw [← Finset.sum_add_distrib]

def wedgePair {n : ℕ} (u v : EuclideanSpace ℂ (Fin n)) : PairSpace n :=
  WithLp.toLp 2 (fun a => u a.val.1 * v a.val.2 - u a.val.2 * v a.val.1)

theorem pairAnnihilate_wedge {n : ℕ} (u v : EuclideanSpace ℂ (Fin n)) :
    pairAnnihilate (wedgePair u v) = annihilate v * annihilate u := by
  simp only [annihilate, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, Finset.smul_sum, smul_smul]
  rw [sum_split_orderedPairs (fun i j =>
    (conj (u i) * conj (v j)) • (annihilateMode j * annihilateMode i))
    (by intro i; simp [mode_square])]
  apply Finset.sum_congr rfl
  intro a _
  change conj (u a.val.1 * v a.val.2 - u a.val.2 * v a.val.1) •
    (annihilateMode a.val.2 * annihilateMode a.val.1) = _
  rw [mode_anticommute a.val.1 a.val.2]
  simp only [map_sub, map_mul, smul_neg, ← neg_smul, ← add_smul]
  congr 1

theorem pairCreate_wedge {n : ℕ} (u v : EuclideanSpace ℂ (Fin n)) :
    pairCreate (wedgePair u v) = create u * create v := by
  rw [← pairAnnihilate_adjoint, pairAnnihilate_wedge]
  simp only [OAI.LaughlinGap.Occupation.adjoint_mul, annihilate_adjoint]

theorem pairEmbed_wedge {n : ℕ} (u v : EuclideanSpace ℂ (Fin n)) :
    pairEmbed (wedgePair u v) = create u (create v (ket ∅)) := by
  rw [← pairCreate_vacuum, pairCreate_wedge, Module.End.mul_apply]

theorem vector_annihilate_vacuum {n : ℕ} (u : EuclideanSpace ℂ (Fin n)) :
    annihilate u (ket ∅) = 0 := by
  simp [annihilate, LinearMap.sum_apply, annihilate_vacuum]

theorem vector_create_vacuum {n : ℕ} (u v : EuclideanSpace ℂ (Fin n)) :
    annihilate u (create v (ket ∅)) = (inner ℂ u v) • ket ∅ := by
  have h := congrArg (fun A : Module.End ℂ (Space n) => A (ket ∅)) (vector_car u v)
  simpa [Module.End.mul_apply, vector_annihilate_vacuum] using h

theorem vector_annihilate_two_create {n : ℕ} (u s t : EuclideanSpace ℂ (Fin n)) :
    annihilate u (create s (create t (ket ∅))) =
      (inner ℂ u s) • create t (ket ∅) - (inner ℂ u t) • create s (ket ∅) := by
  apply eq_sub_iff_add_eq.mpr
  have h := congrArg (fun A : Module.End ℂ (Space n) => A (create t (ket ∅)))
    (vector_car u s)
  simpa [Module.End.mul_apply, vector_create_vacuum] using h

/-- The complex Gram determinant, with the first inner-product argument antilinear. -/
theorem wedgePair_inner {n : ℕ} (u v s t : EuclideanSpace ℂ (Fin n)) :
    inner ℂ (wedgePair u v) (wedgePair s t) =
      inner ℂ u s * inner ℂ v t - inner ℂ u t * inner ℂ v s := by
  rw [← pairEmbed_inner, pairEmbed_wedge, pairEmbed_wedge]
  rw [← annihilate_adjoint u, LinearMap.adjoint_inner_left,
    ← annihilate_adjoint v, LinearMap.adjoint_inner_left]
  rw [vector_annihilate_two_create]
  simp [vector_create_vacuum, inner_sub_right, inner_smul_right,
    inner_self_eq_norm_sq_to_K, ket_norm]

theorem wedgePair_unit_norm {n : ℕ} (u v : EuclideanSpace ℂ (Fin n))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℂ u v = 0) :
    ‖wedgePair u v‖ = 1 := by
  have h : inner ℂ (wedgePair u v) (wedgePair u v) = 1 := by
    rw [wedgePair_inner, huv]
    simp [inner_self_eq_norm_sq_to_K, hu, hv]
  have hr : ‖wedgePair u v‖ ^ 2 = (1 : ℝ) := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), h]
    simp
  nlinarith [norm_nonneg (wedgePair u v)]

theorem wedgePair_self {n : ℕ} (u : EuclideanSpace ℂ (Fin n)) :
    wedgePair u u = 0 := by
  ext a
  simp [wedgePair, mul_comm]

theorem wedgePair_swap {n : ℕ} (u v : EuclideanSpace ℂ (Fin n)) :
    wedgePair v u = -wedgePair u v := by
  ext a
  simp only [wedgePair, PiLp.neg_apply]
  change v a.val.1 * u a.val.2 - v a.val.2 * u a.val.1 =
    -(u a.val.1 * v a.val.2 - u a.val.2 * v a.val.1)
  ring

def wedgePairBilinear (n : ℕ) : EuclideanSpace ℂ (Fin n) →ₗ[ℂ]
    EuclideanSpace ℂ (Fin n) →ₗ[ℂ] PairSpace n where
  toFun u :=
    { toFun := wedgePair u
      map_add' v w := by ext a; simp [wedgePair]; ring
      map_smul' z v := by ext a; simp [wedgePair]; ring }
  map_add' u v := by ext w a; simp [wedgePair]; ring
  map_smul' z u := by ext v a; simp [wedgePair]; ring

private theorem orbital_expansion {n : ℕ} (u : EuclideanSpace ℂ (Fin n)) :
    (∑ i, u i • PiLp.single 2 i (1 : ℂ)) = u := by
  ext i
  simp [Pi.single_apply]

/-- The matrix of exterior square: columns are wedges of the actual images
of the canonical orbitals. It is defined independently of its covariance law. -/
def exteriorSquare {n m : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)) :
    PairSpace n →ₗ[ℂ] PairSpace m where
  toFun p := ∑ a, p a • wedgePair (A (PiLp.single 2 a.val.1 1))
    (A (PiLp.single 2 a.val.2 1))
  map_add' p q := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' z p := by simp [Finset.smul_sum, smul_smul]

theorem exteriorSquare_wedge {n m : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m))
    (u v : EuclideanSpace ℂ (Fin n)) :
    exteriorSquare A (wedgePair u v) = wedgePair (A u) (A v) := by
  have expand (x : EuclideanSpace ℂ (Fin n)) :
      A x = ∑ i, x i • A (PiLp.single 2 i 1) := by
    simp_rw [← map_smul]
    rw [← map_sum, orbital_expansion]
  change _ = wedgePairBilinear m (A u) (A v)
  rw [expand u, expand v]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.smul_sum, smul_smul]
  change _ = ∑ i, ∑ j, (v i * u j) •
    wedgePair (A (PiLp.single 2 j 1)) (A (PiLp.single 2 i 1))
  rw [sum_split_orderedPairs (fun i j => (v i * u j) •
    wedgePair (A (PiLp.single 2 j 1)) (A (PiLp.single 2 i 1)))
    (by intro i; simp [wedgePair_self])]
  apply Finset.sum_congr rfl
  intro a _
  change (u a.val.1 * v a.val.2 - u a.val.2 * v a.val.1) • _ = _
  rw [wedgePair_swap (A (PiLp.single 2 a.val.2 1)) (A (PiLp.single 2 a.val.1 1))]
  simp only [smul_neg, ← neg_smul, ← add_smul]
  congr 1
  ring

theorem wedgePair_basis {n : ℕ} (a : PairIndex n) :
    wedgePair (PiLp.single 2 a.val.1 1) (PiLp.single 2 a.val.2 1) = pairBasis a := by
  apply (pairEmbedding n).injective
  change pairEmbed (wedgePair _ _) = pairEmbed (pairBasis a)
  rw [pairEmbed_wedge]
  have hc (i : Fin n) : create (PiLp.single 2 i 1) = createMode i := by
    simp [create]
  rw [hc, hc]
  simp [pairEmbed, pairBasis, pairKet, pairMode_adjoint, Module.End.mul_apply]

theorem exteriorSquare_pairBasis {n m : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m))
    (a : PairIndex n) :
    exteriorSquare A (pairBasis a) =
      wedgePair (A (PiLp.single 2 a.val.1 1)) (A (PiLp.single 2 a.val.2 1)) := by
  simp [exteriorSquare, pairBasis]

private theorem pairLinear_ext {n m : ℕ} (F G : PairSpace n →ₗ[ℂ] PairSpace m)
    (h : ∀ a, F (pairBasis a) = G (pairBasis a)) : F = G := by
  ext p
  rw [← pairBasis_expansion p]
  simp only [map_sum, map_smul, h]

theorem exteriorSquare_id {n : ℕ} :
    exteriorSquare (LinearMap.id : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] _) =
      (LinearMap.id : PairSpace n →ₗ[ℂ] _) := by
  apply pairLinear_ext
  intro a
  simp only [exteriorSquare_pairBasis, LinearMap.id_apply, wedgePair_basis]

theorem exteriorSquare_comp {n m k : ℕ}
    (B : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin k))
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)) :
    exteriorSquare (B.comp A) = (exteriorSquare B).comp (exteriorSquare A) := by
  apply pairLinear_ext
  intro a
  simp only [exteriorSquare_pairBasis, LinearMap.comp_apply, exteriorSquare_wedge]

theorem exteriorSquare_isometry_inner {n m : ℕ}
    (U : EuclideanSpace ℂ (Fin n) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m))
    (p q : PairSpace n) :
    inner ℂ (exteriorSquare U.toLinearMap p) (exteriorSquare U.toLinearMap q) =
      inner ℂ p q := by
  have hb (a b : PairIndex n) :
      inner ℂ (exteriorSquare U.toLinearMap (pairBasis a))
        (exteriorSquare U.toLinearMap (pairBasis b)) =
      inner ℂ (pairBasis a) (pairBasis b) := by
    rw [exteriorSquare_pairBasis, exteriorSquare_pairBasis,
      ← wedgePair_basis a, ← wedgePair_basis b, wedgePair_inner, wedgePair_inner]
    simp only [LinearIsometry.coe_toLinearMap, U.inner_map_map]
  conv_lhs => rw [← pairBasis_expansion p, ← pairBasis_expansion q]
  simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hb]
  conv_rhs => rw [← pairBasis_expansion p, ← pairBasis_expansion q]
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right]

def exteriorSquareIsometry {n m : ℕ}
    (U : EuclideanSpace ℂ (Fin n) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) :
    PairSpace n →ₗᵢ[ℂ] PairSpace m where
  toLinearMap := exteriorSquare U.toLinearMap
  norm_map' := (LinearMap.norm_map_iff_inner_map_map _).mpr
    (exteriorSquare_isometry_inner U)

theorem exteriorSquare_adjoint {n m : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)) :
    exteriorSquare A.adjoint = (exteriorSquare A).adjoint := by
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro p q
  have hb (a : PairIndex m) (b : PairIndex n) :
      inner ℂ (exteriorSquare A.adjoint (pairBasis a)) (pairBasis b) =
      inner ℂ (pairBasis a) (exteriorSquare A (pairBasis b)) := by
    rw [exteriorSquare_pairBasis, exteriorSquare_pairBasis,
      ← wedgePair_basis a, ← wedgePair_basis b, wedgePair_inner, wedgePair_inner]
    simp only [LinearMap.adjoint_inner_left]
  rw [← pairBasis_expansion p, ← pairBasis_expansion q]
  simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hb]

/-- The bound is on full Fock space and has no particle-number factor. -/
theorem pairAnnihilate_wedge_norm_le {n : ℕ}
    (u v : EuclideanSpace ℂ (Fin n)) (x : Space n) :
    ‖pairAnnihilate (wedgePair u v) x‖ ≤ ‖v‖ * ‖u‖ * ‖x‖ := by
  rw [pairAnnihilate_wedge, Module.End.mul_apply]
  calc
    _ ≤ ‖v‖ * ‖annihilate u x‖ := annihilate_norm_le v _
    _ ≤ ‖v‖ * (‖u‖ * ‖x‖) := mul_le_mul_of_nonneg_left
      (annihilate_norm_le u x) (norm_nonneg v)
    _ = _ := (mul_assoc _ _ _).symm

end VortexGap.Fermion


import OAI.Analysis.LaughlinGap.Occupation

/-! Concrete full finite-mode Fock space, not a particle-number-truncated CAR representation. -/
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators InnerProduct ComplexConjugate
open OAI.LaughlinGap.Occupation

abbrev Space (n : ℕ) := EuclideanSpace ℂ (Finset (Fin n))
abbrev annihilateMode {n : ℕ} (i : Fin n) : Module.End ℂ (Space n) := annihilation i
abbrev createMode {n : ℕ} (i : Fin n) : Module.End ℂ (Space n) := creation i

theorem mode_car {n : ℕ} (i j : Fin n) :
    annihilateMode i * createMode j + createMode j * annihilateMode i =
      if i = j then 1 else 0 := annihilation_creation_CAR i j

theorem mode_adjoint {n : ℕ} (i : Fin n) :
    (annihilateMode i).adjoint = createMode i := annihilation_adjoint i

theorem mode_square {n : ℕ} (i : Fin n) :
    annihilateMode i * annihilateMode i = 0 := transition_square i false

theorem mode_anticommute {n : ℕ} (i j : Fin n) :
    annihilateMode i * annihilateMode j = -(annihilateMode j * annihilateMode i) := by
  by_cases hij : i = j
  · subst j; simp [mode_square]
  · exact transition_anticommute_of_ne hij false false

theorem mode_norm_le {n : ℕ} (i : Fin n) (x : Space n) :
    ‖annihilateMode i x‖ ≤ ‖x‖ := transition_norm_le i false x

def ket {n : ℕ} (A : Finset (Fin n)) : Space n := PiLp.single 2 A 1

theorem ket_norm {n : ℕ} (A : Finset (Fin n)) : ‖ket A‖ = 1 := by simp [ket]

def annihilate {n : ℕ} (v : EuclideanSpace ℂ (Fin n)) : Module.End ℂ (Space n) :=
  ∑ i, conj (v i) • annihilateMode i

def create {n : ℕ} (v : EuclideanSpace ℂ (Fin n)) : Module.End ℂ (Space n) :=
  ∑ i, v i • createMode i

theorem annihilate_smul {n : ℕ} (z : ℂ) (v : EuclideanSpace ℂ (Fin n)) :
    annihilate (z • v) = conj z • annihilate v := by
  simp [annihilate, map_mul, Finset.smul_sum, smul_smul]

theorem create_smul {n : ℕ} (z : ℂ) (v : EuclideanSpace ℂ (Fin n)) :
    create (z • v) = z • create v := by
  simp [create, Finset.smul_sum, smul_smul]

theorem annihilate_adjoint {n : ℕ} (v : EuclideanSpace ℂ (Fin n)) :
    (annihilate v).adjoint = create v := by
  simp [annihilate, create, map_sum, map_smulₛₗ]

/-- CAR for arbitrary complex orbitals in the full finite-mode Fock Hilbert space. -/
theorem vector_car {n : ℕ} (v w : EuclideanSpace ℂ (Fin n)) :
    annihilate v * create w + create w * annihilate v = (inner ℂ v w) • 1 := by
  have hi (i : Fin n) : annihilateMode i * create w + create w * annihilateMode i =
      w i • (1 : Module.End ℂ (Space n)) := by
    simp only [create, Finset.mul_sum, Finset.sum_mul, mul_smul_comm,
      smul_mul_assoc, ← Finset.sum_add_distrib, ← smul_add, mode_car]
    simp
  simp only [annihilate, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, ← Finset.sum_add_distrib, ← smul_add, hi, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

theorem annihilate_vacuum {n : ℕ} (i : Fin n) : annihilateMode i (ket ∅) = 0 := by
  ext A
  by_cases h : i ∈ A <;> simp [ket, annihilateMode, annihilation, transition_apply, h]

theorem create_full {n : ℕ} (i : Fin n) : createMode i (ket Finset.univ) = 0 := by
  ext A
  by_cases h : i ∈ A
  · have hf : flip i A ≠ Finset.univ := by
      intro he
      have hn : i ∉ flip i A := by simp [h]
      simp [he] at hn
    have he : A.erase i ≠ Finset.univ := by simpa only [flip_of_mem h] using hf
    simp [ket, createMode, creation, transition_apply, h, he]
  · simp [ket, createMode, creation, transition_apply, h]

theorem vector_norm_identity {n : ℕ} (v : EuclideanSpace ℂ (Fin n)) (x : Space n) :
    ‖create v x‖ ^ 2 + ‖annihilate v x‖ ^ 2 = ‖v‖ ^ 2 * ‖x‖ ^ 2 := by
  have hc : (create v).adjoint = annihilate v := by
    rw [← annihilate_adjoint, LinearMap.adjoint_adjoint]
  have he : inner ℂ (create v x) (create v x) + inner ℂ (annihilate v x) (annihilate v x) =
      inner ℂ v v * inner ℂ x x := by
    calc
      _ = inner ℂ x ((annihilate v * create v + create v * annihilate v) x) := by
        rw [← LinearMap.adjoint_inner_right (create v) x (create v x), hc,
          ← LinearMap.adjoint_inner_right (annihilate v) x (annihilate v x), annihilate_adjoint,
          ← inner_add_right]
        rfl
      _ = _ := by rw [vector_car]; simp
  simp only [inner_self_eq_norm_sq_to_K] at he
  exact_mod_cast he

theorem annihilate_norm_le {n : ℕ} (v : EuclideanSpace ℂ (Fin n)) (x : Space n) :
    ‖annihilate v x‖ ≤ ‖v‖ * ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  have h := vector_norm_identity v x
  nlinarith [sq_nonneg ‖create v x‖]

def annihilateCLM {n : ℕ} (v : EuclideanSpace ℂ (Fin n)) : Space n →L[ℂ] Space n :=
  LinearMap.toContinuousLinearMap (annihilate v)

/-- Here the norm is the induced Hilbert-space operator norm, not a matrix entry norm. -/
theorem annihilate_opNorm_le {n : ℕ} (v : EuclideanSpace ℂ (Fin n)) :
    ‖annihilateCLM v‖ ≤ ‖v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  exact annihilate_norm_le v

end VortexGap.Fermion

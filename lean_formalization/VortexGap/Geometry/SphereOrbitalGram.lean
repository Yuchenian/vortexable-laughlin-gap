import VortexGap.Transfer.SphereFiltered
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory OAI.Laughlin.Rotation
open scoped Matrix ComplexConjugate
attribute [local fun_prop] sourceSpinRepresentation_continuous

theorem sphereOrbital_orthogonality (q : ℕ) (i j : Fin (q+1)) :
    (∫ g : SourceSU2, sourceSpinRepresentation q g i 0 * conj (sourceSpinRepresentation q g j 0) ∂sourceHaar) =
      ((1:ℂ)/((q:ℂ)+1)) * (1 : Matrix (Fin (q+1)) _ ℂ) i j := by
  let P : Matrix (Fin (q+1)) (Fin (q+1)) ℂ := Matrix.single 0 0 1
  have hp : P.trace = 1 := by simp [P,Matrix.trace,Matrix.diag,Matrix.single]
  have hs := congrFun (congrFun (source_spin_haar_schur q P) i) j
  have he (g : SourceSU2) : conjugateOrbit (sourceSpinRepresentation q) P g i j =
      sourceSpinRepresentation q g i 0 * conj (sourceSpinRepresentation q g j 0) := by
    rw [conjugateOrbit,sourceSpinRepresentation_inv,Matrix.mul_apply,Finset.sum_eq_single 0]
    · simp [P,Matrix.mul_single_apply_same,Matrix.conjTranspose_apply]
    · intro b _ hb
      simp [P,hb]
    · simp
  change (∫ g : SourceSU2, conjugateOrbit (sourceSpinRepresentation q) P g i j ∂sourceHaar) = _ at hs
  simpa only [he,hp,Matrix.smul_apply,smul_eq_mul,Nat.cast_add,Nat.cast_one] using hs

/-- The scalar orbital evaluated in the moving north-pole gauge, before area normalization. -/
def sphereOrbitalValue (q : ℕ) (x : Fin (q+1) → ℂ) (g : SourceSU2) : ℂ :=
  ∑ i, conj (sourceSpinRepresentation q g i 0) * x i

theorem sphereOrbitalValue_continuous (q : ℕ) (x : Fin (q+1) → ℂ) :
    Continuous (sphereOrbitalValue q x) := by
  unfold sphereOrbitalValue
  fun_prop

theorem sphereOrbitalValue_gram (q : ℕ) (x y : Fin (q+1) → ℂ) :
    (∫ g, conj (sphereOrbitalValue q x g) * sphereOrbitalValue q y g ∂sourceHaar) =
      (1/((q:ℂ)+1)) * ∑ i, conj (x i) * y i := by
  let A (i j : Fin (q+1)) (g : SourceSU2) := (conj (x i) * y j) *
    (sourceSpinRepresentation q g i 0 * conj (sourceSpinRepresentation q g j 0))
  have hi (i j) : Integrable (A i j) sourceHaar := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    dsimp [A]
    fun_prop
  have he (g) : conj (sphereOrbitalValue q x g) * sphereOrbitalValue q y g = ∑ i, ∑ j, A i j g := by
    simp only [sphereOrbitalValue,map_sum,map_mul,RingHomCompTriple.comp_apply,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp [A,mul_comm,mul_left_comm,mul_assoc]
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hi _ j)]
  simp_rw [A,integral_const_mul,sphereOrbital_orthogonality,Matrix.one_apply]
  simp [mul_ite,Finset.mul_sum,mul_comm,mul_left_comm]
theorem sphereOrbitalValue_physical (n : ℕ) (x : Fin (n+2) → ℂ) (R : ℝ) (g : SourceSU2) :
    (∑ i, sphereRotatedOrbital n g i R 0 * x i) =
      sphereChartOrbital (n+1) 0 R 0 * sphereOrbitalValue (n+1) x g := by
  rw [sphereOrbitalValue,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : sphereRotatedOrbital n g i R 0 =
      conj (sourceSpinRepresentation (n+1) g i 0) * sphereChartOrbital (n+1) 0 R 0 := by
    simp [sphereRotatedOrbital,sphereChartOrbital_origin,sourceSpinRepresentation_inv,
      Matrix.conjTranspose_apply,mul_ite]
  rw [he]
  ring

theorem sphereOrbitalValue_parseval (q : ℕ) (x : Fin (q+1) → ℂ) :
    ((q:ℝ)+1) * (∫ g, ‖sphereOrbitalValue q x g‖^2 ∂sourceHaar) = ∑ i, ‖x i‖^2 := by
  have h := sphereOrbitalValue_gram q x x
  have hx (z : ℂ) : conj z * z = ((‖z‖^2:ℝ):ℂ) := by
    rw [mul_comm,Complex.mul_conj,Complex.sq_norm]
  simp_rw [hx] at h
  rw [integral_complex_ofReal] at h
  have h' : (∫ g, ‖sphereOrbitalValue q x g‖^2 ∂sourceHaar) =
      (1/((q:ℝ)+1)) * ∑ i, ‖x i‖^2 := by
    apply Complex.ofReal_injective
    push_cast
    simpa only [Complex.ofReal_pow] using h
  rw [h']
  field_simp

/-- Bounds on the Gram form of a continuous scalar multiplier pulled back to SU(2). -/
theorem sphereOrbitalValue_weight_bounds (q : ℕ) (x : Fin (q+1) → ℂ)
    (f : SourceSU2 → ℂ) (hf : Continuous f) (a b : ℝ)
    (ha : ∀ g, a ≤ ‖f g‖^2) (hb : ∀ g, ‖f g‖^2 ≤ b) :
    let G := ((q:ℝ)+1) * ∫ g, ‖f g * sphereOrbitalValue q x g‖^2 ∂sourceHaar
    a * ∑ i, ‖x i‖^2 ≤ G ∧ G ≤ b * ∑ i, ‖x i‖^2 := by
  dsimp only
  let v := sphereOrbitalValue q x
  have hv : Continuous v := sphereOrbitalValue_continuous q x
  have hi (c : ℝ) : Integrable (fun g => c * ‖v g‖^2) sourceHaar :=
    (continuous_const.mul (hv.norm.pow 2)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hw : Integrable (fun g => ‖f g * v g‖^2) sourceHaar :=
    ((hf.mul hv).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hlo := integral_mono (hi a) hw (fun g => by
    rw [norm_mul,mul_pow]; exact mul_le_mul_of_nonneg_right (ha g) (sq_nonneg _))
  have hup := integral_mono hw (hi b) (fun g => by
    rw [norm_mul,mul_pow]; exact mul_le_mul_of_nonneg_right (hb g) (sq_nonneg _))
  rw [integral_const_mul] at hlo hup
  rw [← sphereOrbitalValue_parseval q x]
  change a * (_ * ∫ g, ‖v g‖^2 ∂sourceHaar) ≤ _ ∧ _ ≤ b * (_ * ∫ g, ‖v g‖^2 ∂sourceHaar)
  rw [mul_left_comm a,mul_left_comm b]
  exact ⟨mul_le_mul_of_nonneg_left hlo (by positivity),mul_le_mul_of_nonneg_left hup (by positivity)⟩

end VortexGap.Fermion

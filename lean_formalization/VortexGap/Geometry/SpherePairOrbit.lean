import VortexGap.Geometry.SphereHaarRadial
import VortexGap.Frame.ContinuousPairLift
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open OAI.Laughlin.Rotation MeasureTheory VortexGap.Frame
open scoped Matrix ComplexConjugate

def sphereOrbitPair (n : ℕ) (g : SourceSU2) : PairSpace (n+2) :=
  wedgePair (sphereSpinFrame n g (PiLp.single 2 0 1)) (sphereSpinFrame n g (PiLp.single 2 1 1))

theorem sphereOrbitPair_inner (n : ℕ) (g h : SourceSU2) :
    inner ℂ (sphereOrbitPair n g) (sphereOrbitPair n h) =
      sourceSpinRepresentation (2*n) (g⁻¹*h) 0 0 := by
  have he := sphereSpinFrame_matrix n g h
  have hh : inner ℂ (sphereOrbitPair n g) (sphereOrbitPair n h) =
      ((sphereSpinColumns n g)ᴴ * sphereSpinColumns n h).det := by
    rw [← he, Matrix.det_fin_two]
    simp only [sphereOrbitPair, wedgePair_inner, twoOperatorMatrix_entry, twoFrameOverlap_entry]
  rw [hh, sphereSpinBlock_first_row]
  cases n with
  | zero => rw [sphereSpinColumns_flux_one, show (g⁻¹*h).val.det = 1 from (g⁻¹*h).property.2]; simp
  | succ n => rw [sphereSpinColumns_pair_det]; simp

private theorem spin_kernel_convolution (q : ℕ) (g k : SourceSU2) :
    (∫ h, sourceSpinRepresentation q (g⁻¹*h) 0 0 * sourceSpinRepresentation q (h⁻¹*k) 0 0 ∂sourceHaar) =
      sourceSpinRepresentation q (g⁻¹*k) 0 0 / ((q:ℂ)+1) := by
  let ρ := sourceSpinRepresentation q
  let P : Matrix (Fin (q+1)) (Fin (q+1)) ℂ := Matrix.single 0 0 1
  let A := conjugateOrbit ρ P
  have hA (i j : Fin (q+1)) : Continuous (fun h => A h i j) := by
    dsimp [A,conjugateOrbit]
    simp only [Matrix.mul_apply]
    have hc := sourceSpinRepresentation_continuous q
    dsimp [ρ]
    fun_prop
  have hL (i j : Fin (q+1)) : Continuous (fun h => (ρ g⁻¹ * A h) i j) := by
    simp only [Matrix.mul_apply]
    fun_prop
  have he (h : SourceSU2) :
      (ρ g⁻¹ * A h * ρ k) 0 0 = ρ (g⁻¹*h) 0 0 * ρ (h⁻¹*k) 0 0 := by
    have hm : ρ g⁻¹ * A h * ρ k = ρ (g⁻¹*h) * P * ρ (h⁻¹*k) := by
      simp [A,conjugateOrbit, map_mul, Matrix.mul_assoc]
    rw [hm, Matrix.mul_apply, Finset.sum_eq_single 0]
    · simp [P]
    · intro b _ hb; simp [P,hb]
    · simp
  change (∫ h, ρ (g⁻¹*h) 0 0 * ρ (h⁻¹*k) 0 0 ∂sourceHaar) = _
  simp_rw [← he]
  change matrixIntegral sourceHaar (fun h => ρ g⁻¹ * A h * ρ k) 0 0 = _
  rw [matrixIntegral_mul_right _ _ (fun i j => (hL i j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
    matrixIntegral_mul_left _ _ (fun i j => (hA i j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  have hs := source_spin_haar_schur q P
  change matrixIntegral sourceHaar A = _ at hs
  rw [hs, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← map_mul]
  simp [P,Matrix.trace,Matrix.diag,Matrix.single,div_eq_mul_inv,mul_comm,ρ]

theorem sphereOrbitPair_reproducing (n : ℕ) (g k : SourceSU2) :
    (∫ h, inner ℂ (sphereOrbitPair n g) (sphereOrbitPair n h) *
      inner ℂ (sphereOrbitPair n h) (sphereOrbitPair n k) ∂sourceHaar) =
      inner ℂ (sphereOrbitPair n g) (sphereOrbitPair n k) / ((2*n:ℕ)+1:ℂ) := by
  simp only [sphereOrbitPair_inner]
  exact spin_kernel_convolution (2*n) g k

theorem sphereOrbitPair_continuous (n : ℕ) : Continuous (sphereOrbitPair n) := by
  have col (j : Fin 2) (i : Fin (n+2)) : Continuous (fun g =>
      sphereSpinFrame n g (PiLp.single 2 j 1) i) := by
    change Continuous (fun g => ((sphereSpinColumns n g) *ᵥ (Pi.single j (1:ℂ))) i)
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, sphereSpinColumns] using
      sourceSpinRepresentation_continuous (n+1) i (Fin.castLE (by omega) j)
  apply (PiLp.continuous_toLp 2 (fun _ : PairIndex (n+2) => ℂ)).comp
  apply continuous_pi
  intro a
  exact ((col 0 a.val.1).mul (col 1 a.val.2)).sub ((col 0 a.val.2).mul (col 1 a.val.1))

/-- The highest-pair-spin sector, realized inside the actual exterior square. -/
def spherePairSector (n : ℕ) := Submodule.span ℂ (Set.range (sphereOrbitPair n))

theorem spherePair_projector (n : ℕ) :
    ((2*n:ℕ)+1:ℂ) • continuousPairOperator sourceHaar (sphereOrbitPair n) =
      (spherePairSector n).starProjection := by
  let p := sphereOrbitPair n
  let S := spherePairSector n
  let D : ℂ := ((2*n:ℕ)+1:ℂ)
  let T := D • continuousPairOperator sourceHaar p
  have hn : D ≠ 0 := by dsimp [D]; exact_mod_cast (Nat.succ_ne_zero (2*n))
  have pc : Continuous p := sphereOrbitPair_continuous n
  have hp : MemLp p 2 sourceHaar := pc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hm (g) : p g ∈ S := Submodule.subset_span (Set.mem_range_self g)
  have fixp (g) : S.starProjection (p g) = p g := Submodule.starProjection_eq_self_iff.mpr (hm g)
  have hi (x : PairSpace (n+2)) :
      Integrable (fun h => inner ℂ (p h) x • p h) sourceHaar :=
    (show Continuous (fun h => inner ℂ (p h) x • p h) by fun_prop).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have ht (x : PairSpace (n+2)) : T x = D • ∫ h, inner ℂ (p h) x • p h ∂sourceHaar := by
    change D • (∫ h, InnerProductSpace.rankOne ℂ (p h) (p h) ∂sourceHaar) x = _
    rw [ContinuousLinearMap.integral_apply (continuousPairOperator_integrable _ _ hp)]
    rfl
  have rangeT (x : PairSpace (n+2)) : T x ∈ S := by
    apply Submodule.starProjection_eq_self_iff.mp
    rw [ht, map_smul, ← S.starProjection.integral_comp_comm (hi x)]
    simp only [map_smul, fixp]
  have onOrbit (k : SourceSU2) : T (p k) = p k := by
    let e := T (p k) - p k
    have hz (g : SourceSU2) : inner ℂ (p g) e = 0 := by
      dsimp only [e]
      rw [inner_sub_right, ht, inner_smul_right, ← integral_inner (hi _) (p g)]
      simp_rw [inner_smul_right]
      simp_rw [mul_comm (inner ℂ (p _) (p k))]
      rw [sphereOrbitPair_reproducing]
      change D * (_ / D) - _ = 0
      field_simp [hn]
      exact sub_self _
    have he : e ∈ S := S.sub_mem (rangeT _) (hm _)
    have hall (y : PairSpace (n+2)) (hy : y ∈ S) : inner ℂ y e = 0 := by
      induction hy using Submodule.span_induction with
      | mem x hx => obtain ⟨g,rfl⟩ := hx; exact hz g
      | zero => simp
      | add x y _ _ hx hy => simp [hx,hy]
      | smul c x _ hx => simp [hx]
    exact sub_eq_zero.mp (inner_self_eq_zero.mp (hall e he))
  have onS (x : PairSpace (n+2)) (hx : x ∈ S) : T x = x := by
    apply LinearMap.eqOn_span (f := T.toLinearMap) (g := LinearMap.id) _ hx
    rintro _ ⟨k,rfl⟩
    exact onOrbit k
  ext x : 1
  change T x = S.starProjection x
  rw [← onS (S.starProjection x) (S.starProjection_apply_mem x), ht, ht]
  congr 1
  apply integral_congr_ae
  filter_upwards with h
  rw [← S.inner_starProjection_left_eq_right, fixp]

theorem spherePairSector_finrank (n : ℕ) :
    Module.finrank ℂ (spherePairSector n) = 2*n+1 := by
  let E := PairSpace (n+2)
  haveI : CompleteSpace E := PiLp.completeSpace 2 (fun _ => ℂ)
  haveI : CompleteSpace (E →L[ℂ] E) := ContinuousLinearMap.instCompleteSpace
  let p := sphereOrbitPair n
  let S := spherePairSector n
  let tr : (E →L[ℂ] E) →L[ℂ] ℂ :=
    ((LinearMap.trace ℂ E).comp (ContinuousLinearMap.coeLM ℂ)).toContinuousLinearMap
  have hp : MemLp p 2 sourceHaar := (sphereOrbitPair_continuous n).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have ht (g : SourceSU2) : tr (InnerProductSpace.rankOne ℂ (p g) (p g)) = 1 := by
    change LinearMap.trace ℂ (PairSpace (n+2)) (InnerProductSpace.rankOne ℂ (p g) (p g)).toLinearMap = 1
    rw [InnerProductSpace.trace_rankOne, sphereOrbitPair_inner]
    simp
  have htrace : tr (continuousPairOperator sourceHaar p) = 1 := by
    rw [continuousPairOperator, ← tr.integral_comp_comm (continuousPairOperator_integrable _ _ hp)]
    simp_rw [ht]
    simp
  have hproj : LinearMap.IsProj S S.starProjection.toLinearMap :=
    ⟨S.starProjection_apply_mem, fun _ hx => Submodule.starProjection_eq_self_iff.mpr hx⟩
  have hh := congrArg tr (spherePair_projector n)
  change tr (_ • continuousPairOperator sourceHaar p) = tr S.starProjection at hh
  rw [map_smul, htrace, smul_eq_mul, mul_one] at hh
  change _ = LinearMap.trace ℂ E S.starProjection.toLinearMap at hh
  rw [hproj.trace] at hh
  exact_mod_cast hh.symm

theorem spherePair_beta_one (n : ℕ) (x : PairSpace (n+2)) :
    ((2*n:ℕ)+1:ℝ) * (inner ℂ x (continuousPairOperator sourceHaar (sphereOrbitPair n) x)).re ≤ ‖x‖^2 := by
  have hh := DFunLike.congr_fun (spherePair_projector n) x
  have he := congrArg (fun v => (inner ℂ x v).re) hh
  change (inner ℂ x (((2*n:ℕ)+1:ℂ) • _)).re = _ at he
  rw [inner_smul_right] at he
  have hr : ((2*n:ℕ)+1:ℂ) = (((2*n:ℕ)+1:ℝ):ℂ) := by push_cast; rfl
  rw [hr, Complex.re_ofReal_mul] at he
  apply le_trans he.le
  rw [pow_two]
  exact (re_inner_le_norm (𝕜 := ℂ) x ((spherePairSector n).starProjection x)).trans (mul_le_mul_of_nonneg_left ((spherePairSector n).norm_starProjection_apply_le x) (norm_nonneg _))

/-- At flux three the V1 pair orbit occupies five of the six exterior coordinates. -/
theorem spherePair_flux_three_test :
    Module.finrank ℂ (spherePairSector 2) = 5 ∧ Module.finrank ℂ (PairSpace 4) = 6 := by
  constructor
  · exact spherePairSector_finrank 2
  · rw [finrank_euclideanSpace]
    decide

end VortexGap.Fermion

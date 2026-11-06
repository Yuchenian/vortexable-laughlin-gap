import VortexGap.Geometry.SphereSpinBlock
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open VortexGap.Frame OAI.Laughlin.Rotation
open scoped Matrix ComplexConjugate

def sphereSpinFrame (n : ℕ) (g : SourceSU2) : TwoFrame (n+2) where
  toLinearMap := (sphereSpinColumns n g).toEuclideanLin
  norm_map' := by
    apply (LinearMap.norm_map_iff_inner_map_map _).mpr
    intro x y
    rw [← LinearMap.adjoint_inner_right]
    have hh := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A.toEuclideanLin)
      (sphereSpinColumns_orthonormal n g)
    change ((sphereSpinColumns n g)ᴴ * sphereSpinColumns n g).toLpLin 2 2 = _ at hh
    rw [Matrix.toLpLin_mul 2 2 2, Matrix.toLpLin_one] at hh
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    exact congrArg (inner ℂ x) (LinearMap.congr_fun hh y)

theorem sphereSpinFrame_matrix (n : ℕ) (g h : SourceSU2) :
    twoOperatorMatrix (twoFrameOverlap (sphereSpinFrame n g) (sphereSpinFrame n h)) =
      (sphereSpinColumns n g)ᴴ * sphereSpinColumns n h := by
  let A := (sphereSpinColumns n g)ᴴ * sphereSpinColumns n h
  have he : twoFrameOverlap (sphereSpinFrame n g) (sphereSpinFrame n h) = A.toEuclideanLin := by
    change ((sphereSpinColumns n g).toEuclideanLin.adjoint).comp _ = _
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    exact (Matrix.toLpLin_mul 2 2 2 _ _).symm
  rw [he, twoOperatorMatrix, Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact LinearMap.toMatrix_toLin _ _ _

private theorem spinor_coordinates (k : SourceSU2) :
    k.val 1 1 = conj (k.val 0 0) ∧ k.val 1 0 = -conj (k.val 0 1) ∧
      ‖k.val 0 0‖^2 + ‖k.val 0 1‖^2 = 1 := by
  have hd : k.val.det = 1 := k.property.2
  have hu : k.valᴴ * k.val = 1 := Matrix.mem_unitaryGroup_iff'.mp k.property.1
  have ha : k.valᴴ = k.val.adjugate := by
    calc
      _ = k.valᴴ * (k.val * k.val.adjugate) := by rw [Matrix.mul_adjugate, hd, one_smul, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hu, Matrix.one_mul]
  rw [Matrix.adjugate_fin_two] at ha
  have h₀ := congrFun (congrFun ha 0) 0
  have h₁ := congrFun (congrFun ha 1) 0
  change conj (k.val 0 0) = k.val 1 1 at h₀
  change conj (k.val 0 1) = - k.val 1 0 at h₁
  have hc : k.val 1 0 = -conj (k.val 0 1) := by rw [h₁, neg_neg]
  refine ⟨h₀.symm, hc, ?_⟩
  rw [Matrix.det_fin_two, ← h₀, hc, mul_neg, sub_neg_eq_add, Complex.mul_conj, Complex.mul_conj] at hd
  simpa only [Complex.sq_norm, ← Complex.ofReal_add, ← Complex.ofReal_one, Complex.ofReal_inj] using hd

theorem sphereSpinFrame_traceNorm_sq (n : ℕ) (g h : SourceSU2) :
    let t := ‖(g⁻¹*h).val 0 0‖
    traceNormTwo (twoFrameOverlap (sphereSpinFrame (n+1) g) (sphereSpinFrame (n+1) h))^2 =
      (t^n)^2 * (4*t^2 + ((n:ℝ)+1)^2*(1-t^2)^2) := by
  let k := g⁻¹*h
  obtain ⟨hd,hc,hu⟩ := spinor_coordinates k
  obtain ⟨h00,h01,h10,h11⟩ := sphereSpinBlock_entries n k
  have hb : ‖k.val 0 1‖^2 = 1-‖k.val 0 0‖^2 := by linarith
  have hm : k.val 0 0*k.val 1 1 + ((n:ℂ)+1)*k.val 0 1*k.val 1 0 =
      ((‖k.val 0 0‖^2 - ((n:ℝ)+1)*‖k.val 0 1‖^2 : ℝ):ℂ) := by
    rw [hd,hc, mul_neg, mul_assoc, Complex.mul_conj, Complex.mul_conj]
    simp only [Complex.sq_norm, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_add,
      Complex.ofReal_one, Complex.ofReal_natCast, sub_eq_add_neg]
  dsimp only
  rw [traceNormTwo_sq_matrix, sphereSpinFrame_matrix, sphereSpinColumns_pair_det]
  simp only [Fin.sum_univ_two, sphereSpinColumns_overlap]
  change ‖sourceSpinRepresentation (n+2) k 0 0‖^2 + ‖sourceSpinRepresentation (n+2) k 0 1‖^2 +
    (‖sourceSpinRepresentation (n+2) k 1 0‖^2 + ‖sourceSpinRepresentation (n+2) k 1 1‖^2) +
    2*‖k.val 0 0 ^ (2*(n+1))‖ = _
  rw [h00,h01,h10,h11,hm,hc]
  simp only [norm_pow, norm_mul, norm_neg, RCLike.norm_conj, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, sq_abs, Real.sq_sqrt (by positivity : 0 ≤ ((n+2:ℕ):ℝ))]
  change _ = (‖k.val 0 0‖^n)^2 * (4*‖k.val 0 0‖^2 + ((n:ℝ)+1)^2*(1-‖k.val 0 0‖^2)^2)
  rw [show 2*(n+1)=(n+1)*2 by omega, pow_mul]
  simp only [pow_succ ‖k.val 0 0‖, Nat.cast_add, Nat.cast_ofNat]
  rw [hb]
  ring

theorem sphereSpinFrame_traceNorm (n : ℕ) (g h : SourceSU2) :
    let t := ‖(g⁻¹*h).val 0 0‖
    traceNormTwo (twoFrameOverlap (sphereSpinFrame (n+1) g) (sphereSpinFrame (n+1) h)) =
      t^n * Real.sqrt (4*t^2 + ((n:ℝ)+1)^2*(1-t^2)^2) := by
  dsimp only
  apply (sq_eq_sq₀ (traceNormTwo_nonneg _) (by positivity)).mp
  rw [sphereSpinFrame_traceNorm_sq, mul_pow, Real.sq_sqrt (by positivity)]

theorem sphereSpinFrame_flux_one_traceNorm (g h : SourceSU2) :
    traceNormTwo (twoFrameOverlap (sphereSpinFrame 0 g) (sphereSpinFrame 0 h)) = 2 := by
  let k := g⁻¹*h
  obtain ⟨hd,hc,hu⟩ := spinor_coordinates k
  apply (sq_eq_sq₀ (traceNormTwo_nonneg _) (by norm_num)).mp
  rw [traceNormTwo_sq_matrix, sphereSpinFrame_matrix, sphereSpinColumns_flux_one]
  change (∑ i : Fin 2, ∑ j : Fin 2, ‖k.val i j‖^2) + 2*‖k.val.det‖ = _
  rw [show k.val.det = 1 from k.property.2]
  simp only [Fin.sum_univ_two, hd, hc, norm_one, norm_neg, RCLike.norm_conj]
  linarith

end VortexGap.Fermion

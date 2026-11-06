import VortexGap.Fermion.LossOutput

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators InnerProduct ComplexConjugate ComplexOrder

/-- Actual environment-vacuum isometry in the enlarged occupation space. -/
def lossVacuum (n : ℕ) : Space n →ₗᵢ[ℂ] Space (n+n) :=
  (fockSplit n n).symm.toLinearIsometry.comp (environmentVacuumIsometry n n)

theorem lossVacuum_apply {n : ℕ} (x : Space n) :
    lossVacuum n x = (fockSplit n n).symm (environmentVacuum n n x) := rfl

theorem lossVacuum_sector {n N : ℕ} {x : Space n} (hx : InSector N x) :
    InSector N (lossVacuum n x) := environmentVacuum_sector hx

/-- Compression by the actual vacuum inclusion, not an abstract channel datum. -/
def vacuumCompression (n : ℕ) (H : Module.End ℂ (Space (n+n))) : Module.End ℂ (Space n) :=
  (lossVacuum n).toLinearMap.adjoint.comp (H.comp (lossVacuum n).toLinearMap)

theorem vacuumCompression_inner {n : ℕ} (H : Module.End ℂ (Space (n+n))) (x y : Space n) :
    inner ℂ x (vacuumCompression n H y) = inner ℂ (lossVacuum n x) (H (lossVacuum n y)) :=
by
  change inner ℂ x ((lossVacuum n).toLinearMap.adjoint (H ((lossVacuum n).toLinearMap y))) = _
  exact LinearMap.adjoint_inner_right (lossVacuum n).toLinearMap x (H (lossVacuum n y))

theorem frameHamiltonian_adjoint {n : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (p : ι → PairSpace n) :
    (frameHamiltonian w p).adjoint = frameHamiltonian w p := by
  unfold frameHamiltonian
  rw [pairLift_frame]
  simp only [map_sum, map_smulₛₗ, Complex.conj_ofReal,
    OAI.LaughlinGap.Occupation.adjoint_mul, LinearMap.adjoint_adjoint]

variable {n : ℕ}
variable (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
variable (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
variable {ι : Type*} [Fintype ι] (w : ι → ℝ) (u v : ι → EuclideanSpace ℂ (Fin n))

/-- Exact first moment for the concrete finite CAR loss construction. -/
theorem loss_first_moment :
    vacuumCompression n (lossHamiltonian M hM hc w (fun i => wedgePair (u i) (v i))) =
      filteredHamiltonian M w (fun i => wedgePair (u i) (v i)) := by
  apply LinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  rw [vacuumCompression_inner, ← (fockSplit n n).inner_map_map]
  simp only [lossVacuum_apply, (fockSplit n n).apply_symm_apply, loss_frame_vacuum,
    inner_add_right, environmentVacuum_inner]
  rw [environmentSector_orthogonal (environmentVacuum_environmentSector x)
      (oneLossNoise_sector M w u v y) (by decide),
    environmentSector_orthogonal (environmentVacuum_environmentSector x)
      (twoLossNoise_sector M w (fun i => wedgePair (u i) (v i)) y) (by decide)]
  simp

/-- Orthogonality gives a sesquilinear identity, not just a numerical norm check. -/
theorem loss_output_inner (x y : Space n) :
    inner ℂ
      (fockSplit n n (lossHamiltonian M hM hc w (fun i => wedgePair (u i) (v i)) (lossVacuum n x)))
      (fockSplit n n (lossHamiltonian M hM hc w (fun i => wedgePair (u i) (v i)) (lossVacuum n y))) =
    inner ℂ (filteredHamiltonian M w (fun i => wedgePair (u i) (v i)) x)
      (filteredHamiltonian M w (fun i => wedgePair (u i) (v i)) y) +
      inner ℂ (oneLossNoise M w u v x) (oneLossNoise M w u v y) +
      inner ℂ (twoLossNoise M w (fun i => wedgePair (u i) (v i)) x)
        (twoLossNoise M w (fun i => wedgePair (u i) (v i)) y) := by
  have h01 (a b : Space n) : inner ℂ (environmentVacuum n n a) (oneLossNoise M w u v b) = 0 :=
    environmentSector_orthogonal (environmentVacuum_environmentSector a)
      (oneLossNoise_sector M w u v b) (by decide)
  have h02 (a b : Space n) : inner ℂ (environmentVacuum n n a)
      (twoLossNoise M w (fun i => wedgePair (u i) (v i)) b) = 0 :=
    environmentSector_orthogonal (environmentVacuum_environmentSector a)
      (twoLossNoise_sector M w (fun i => wedgePair (u i) (v i)) b) (by decide)
  have h10 (a b : Space n) : inner ℂ (oneLossNoise M w u v a) (environmentVacuum n n b) = 0 :=
    environmentSector_orthogonal (oneLossNoise_sector M w u v a)
      (environmentVacuum_environmentSector b) (by decide)
  have h12 (a b : Space n) : inner ℂ (oneLossNoise M w u v a)
      (twoLossNoise M w (fun i => wedgePair (u i) (v i)) b) = 0 :=
    environmentSector_orthogonal (oneLossNoise_sector M w u v a)
      (twoLossNoise_sector M w (fun i => wedgePair (u i) (v i)) b) (by decide)
  have h20 (a b : Space n) : inner ℂ (twoLossNoise M w (fun i => wedgePair (u i) (v i)) a)
      (environmentVacuum n n b) = 0 :=
    environmentSector_orthogonal (twoLossNoise_sector M w (fun i => wedgePair (u i) (v i)) a)
      (environmentVacuum_environmentSector b) (by decide)
  have h21 (a b : Space n) : inner ℂ (twoLossNoise M w (fun i => wedgePair (u i) (v i)) a)
      (oneLossNoise M w u v b) = 0 :=
    environmentSector_orthogonal (twoLossNoise_sector M w (fun i => wedgePair (u i) (v i)) a)
      (oneLossNoise_sector M w u v b) (by decide)
  simp only [lossVacuum_apply, loss_frame_vacuum, inner_add_left, inner_add_right,
    h01, h02, h10, h12, h20, h21, environmentVacuum_inner, add_zero, zero_add]

/-- Concrete exact second moment, with the explicitly constructed X1 and X2. -/
theorem loss_second_moment :
    vacuumCompression n
      (lossHamiltonian M hM hc w (fun i => wedgePair (u i) (v i)) *
        lossHamiltonian M hM hc w (fun i => wedgePair (u i) (v i))) =
    filteredHamiltonian M w (fun i => wedgePair (u i) (v i)) *
        filteredHamiltonian M w (fun i => wedgePair (u i) (v i)) +
      (oneLossNoise M w u v).adjoint.comp (oneLossNoise M w u v) +
      (twoLossNoise M w (fun i => wedgePair (u i) (v i))).adjoint.comp
        (twoLossNoise M w (fun i => wedgePair (u i) (v i))) := by
  let H := lossHamiltonian M hM hc w (fun i => wedgePair (u i) (v i))
  let K := filteredHamiltonian M w (fun i => wedgePair (u i) (v i))
  have hH : H.adjoint = H := frameHamiltonian_adjoint _ _
  have hK : K.adjoint = K := frameHamiltonian_adjoint _ _
  apply LinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  rw [vacuumCompression_inner]
  change inner ℂ (lossVacuum n x) (H (H (lossVacuum n y))) = _
  rw [← LinearMap.adjoint_inner_left H (H (lossVacuum n y)) (lossVacuum n x), hH,
    ← (fockSplit n n).inner_map_map]
  rw [loss_output_inner]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, Module.End.mul_apply,
    inner_add_right, LinearMap.adjoint_inner_right]
  change inner ℂ (K x) (K y) + _ + _ = inner ℂ x (K (K y)) + _ + _
  rw [← LinearMap.adjoint_inner_left K (K y) x, hK]

include hM hc in
/-- Reference information reaches the exact three output terms, using only sectors 0..N. -/
theorem loss_compressed_reference_inequality {N : ℕ} (γ : ℝ)
    (hgap : ∀ K ≤ N, ∀ y : Space n, InSector K y →
      γ * (inner ℂ y (frameHamiltonian w (fun i => wedgePair (u i) (v i)) y)).re ≤
        (inner ℂ y ((frameHamiltonian w (fun i => wedgePair (u i) (v i)) *
          frameHamiltonian w (fun i => wedgePair (u i) (v i))) y)).re)
    {x : Space n} (hx : InSector N x) :
    γ * (inner ℂ x (filteredHamiltonian M w (fun i => wedgePair (u i) (v i)) x)).re ≤
      (inner ℂ x ((filteredHamiltonian M w (fun i => wedgePair (u i) (v i)) *
          filteredHamiltonian M w (fun i => wedgePair (u i) (v i)) +
        (oneLossNoise M w u v).adjoint.comp (oneLossNoise M w u v) +
        (twoLossNoise M w (fun i => wedgePair (u i) (v i))).adjoint.comp
          (twoLossNoise M w (fun i => wedgePair (u i) (v i)))) x)).re := by
  have h := lossHamiltonian_sector_inequality M hM hc w (fun i => wedgePair (u i) (v i)) γ hgap
    (lossVacuum_sector hx)
  rw [← vacuumCompression_inner, ← vacuumCompression_inner, loss_first_moment, loss_second_moment] at h
  exact h

end VortexGap.Fermion

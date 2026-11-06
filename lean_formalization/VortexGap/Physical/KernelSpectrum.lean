import VortexGap.Physical.KernelGap
import VortexGap.Operator.SpectralGap
noncomputable section
set_option autoImplicit false
namespace VortexGap
open scoped ComplexOrder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A lower bound on the whole kernel complement implies a quadratic operator
gap; no discreteness or existence of eigenvectors is used. -/
theorem kernel_complement_gap_quadratic (A : H →L[ℂ] H) (hA : 0 ≤ A) (γ : ℝ)
    (hg : ∀ x ∈ (LinearMap.ker A.toLinearMap)ᗮ, γ*‖x‖^2 ≤ (inner ℂ x (A x)).re) :
    (A*A-(γ : ℂ) • A).IsPositive := by
  apply (quadratic_positive_norm_iff A (ContinuousLinearMap.nonneg_iff_isPositive.mp hA) γ).mpr
  intro y
  have hs : (CFC.sqrt A).adjoint = CFC.sqrt A :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)).star_eq
  have hx : CFC.sqrt A y ∈ (LinearMap.ker A.toLinearMap)ᗮ := by
    rw [← positive_sqrt_kernel A hA, ContinuousLinearMap.orthogonal_ker, hs]
    change CFC.sqrt A y ∈ closure (Set.range (fun z : H => CFC.sqrt A z))
    exact subset_closure ⟨y, rfl⟩
  have h := hg (CFC.sqrt A y) hx
  rw [positive_energy_sqrt A hA] at h
  have he : CFC.sqrt A (CFC.sqrt A y) = A y :=
    congrArg (fun T : H →L[ℂ] H => T y) (CFC.sqrt_mul_sqrt_self A hA)
  rw [he] at h
  rwa [positive_energy_sqrt A hA]

theorem kernel_complement_gap_spectrum (A : H →L[ℂ] H) (hA : 0 ≤ A) (γ : ℝ)
    (hg : ∀ x ∈ (LinearMap.ker A.toLinearMap)ᗮ, γ*‖x‖^2 ≤ (inner ℂ x (A x)).re) :
    ∀ t ∈ spectrum ℝ A, t = 0 ∨ γ ≤ t :=
  (quadratic_positive_iff_spectrum_gap A (ContinuousLinearMap.nonneg_iff_isPositive.mp hA) γ).mp
    (kernel_complement_gap_quadratic A hA γ hg)

end VortexGap

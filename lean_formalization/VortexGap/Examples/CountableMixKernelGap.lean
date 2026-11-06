import VortexGap.Physical.KernelGap
import VortexGap.Examples.CountableContinuousMix
noncomputable section
set_option autoImplicit false
namespace VortexGap.Examples
open VortexGap.Fermion
open scoped InnerProduct ComplexOrder

/-- Kernel-complement regression on the actual infinite-mode cross-orbital filter.
The reference gap is discharged by the continuous-frame example. -/
theorem countableMix_kernel_gap (N : ℕ) :
    ∀ x ∈ (LinearMap.ker (countableMixHamiltonian N).toLinearMap)ᗮ,
      (9/10 : ℝ) * ‖x‖^2 ≤ (inner ℂ x (countableMixHamiltonian N x)).re := by
  apply quadratic_gap_on_kernel_complement _
    (ContinuousLinearMap.nonneg_iff_isPositive.mpr (countableMixHamiltonian_positive N))
  simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using countableContinuousMix_gap N

end VortexGap.Examples

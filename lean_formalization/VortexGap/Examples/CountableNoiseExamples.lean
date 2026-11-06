import VortexGap.Fermion.CountableOneEnvironment
import VortexGap.Examples.CountableFockExamples
noncomputable section
set_option autoImplicit false
namespace VortexGap.Examples
open Fermion
open scoped InnerProduct

/-- Both tensor factors have infinite support, with non-real coefficients. -/
theorem geometricEnvironmentProduct_coefficient (i j : ℕ) :
    countableFockSplit (countableEnvironmentProduct geometricOrbital geometricOneParticle)
      ({i},{j}) = (Complex.I/2 : ℂ)^(i+j) := by
  change countableEnvironmentFiber
    (countableFockSplit (countableEnvironmentProduct geometricOrbital geometricOneParticle))
    {j} {i} = _
  rw [countableEnvironmentProduct_fiber]
  change geometricOneParticle {j} *
    (countableCreate geometricOrbital (countableKet ∅) {i}) = _
  rw [geometricOneParticle, createVacuum_singleton_coefficient,
    createVacuum_singleton_coefficient, geometricOrbital_coefficient, geometricOrbital_coefficient,
    pow_add, mul_comm]

theorem geometricEnvironmentProduct_norm_sq :
    ‖countableEnvironmentProduct geometricOrbital geometricOneParticle‖^2 = (16/9 : ℝ) := by
  have hu : inner ℂ geometricOrbital geometricOrbital = (4/3 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, geometricOrbital_norm_sq]
    norm_num
  have hx : inner ℂ geometricOneParticle geometricOneParticle = (4/3 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, geometricOneParticle_norm_sq]
    norm_num
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), countableEnvironmentProduct_inner, hu, hx]
  norm_num

/-- A genuine contraction with a complex phase acts only on the environment factor. -/
theorem geometricOneEnvironment_phase :
    countableOneEnvironmentAction ((Complex.I/2 : ℂ) •
      (1 : CountableOrbital →L[ℂ] CountableOrbital))
      (countableEnvironmentProduct geometricOrbital geometricOneParticle) =
    (Complex.I/2 : ℂ) • countableEnvironmentProduct geometricOrbital geometricOneParticle := by
  rw [countableOneEnvironmentAction_product]
  simp [countableEnvironmentProduct, map_smul]

theorem geometricOneEnvironment_phase_norm_sq :
    ‖countableOneEnvironmentAction ((Complex.I/2 : ℂ) •
      (1 : CountableOrbital →L[ℂ] CountableOrbital))
      (countableEnvironmentProduct geometricOrbital geometricOneParticle)‖^2 = (4/9 : ℝ) := by
  rw [geometricOneEnvironment_phase, norm_smul, mul_pow, geometricEnvironmentProduct_norm_sq]
  norm_num [norm_div]
end VortexGap.Examples

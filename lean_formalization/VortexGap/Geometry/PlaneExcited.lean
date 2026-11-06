import VortexGap.Geometry.PlaneDifferentiation
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct ComplexConjugate

theorem planeBargmann_inner_jet (z w : ℂ) :
    inner ℂ (planeBargmann z) (planeJet w) = conj z * Complex.exp (conj z*w) := by
  have h : HasDerivAt (fun u => inner ℂ (planeBargmann z) (planeBargmann u))
      (conj z * Complex.exp (conj z*w)) w := by
    convert (((hasDerivAt_id w).const_mul (conj z)).cexp) using 1
    · funext u; exact planeBargmann_inner z u
    · simp only [id_eq, mul_one]; ring
  exact ((innerSL ℂ (planeBargmann z)).hasFDerivAt.comp_hasDerivAt w
    (planeBargmann_hasDerivAt w)).unique h

theorem planeJet_inner_bargmann (z w : ℂ) :
    inner ℂ (planeJet z) (planeBargmann w) = w * Complex.exp (conj z*w) := by
  rw [← inner_conj_symm, planeBargmann_inner_jet]
  simp only [map_mul, starRingEnd_self_apply, ← Complex.exp_conj]
  rw [mul_comm w (conj z)]

theorem planeJet_inner_jet (z w : ℂ) :
    inner ℂ (planeJet z) (planeJet w) = (1+conj z*w)*Complex.exp (conj z*w) := by
  have h : HasDerivAt (fun u => inner ℂ (planeJet z) (planeBargmann u))
      ((1+conj z*w)*Complex.exp (conj z*w)) w := by
    have hh := (hasDerivAt_id w).mul (((hasDerivAt_id w).const_mul (conj z)).cexp)
    convert hh using 1
    · funext u; exact planeJet_inner_bargmann z u
    · simp only [id_eq]; ring
  exact ((innerSL ℂ (planeJet z)).hasFDerivAt.comp_hasDerivAt w
    (planeBargmann_hasDerivAt w)).unique h

/-- Explicit displaced first oscillator mode, constructed from actual Hilbert vectors. -/
def planeExcited (z : ℂ) : CountableOrbital :=
  (Real.exp (-‖z‖^2/2) : ℂ) • (planeJet z - conj z • planeBargmann z)

theorem planeCoherent_inner_excited (z w : ℂ) :
    inner ℂ (planeCoherent z) (planeExcited w) =
      (conj z-conj w)*inner ℂ (planeCoherent z) (planeCoherent w) := by
  simp only [planeCoherent, planeExcited, inner_smul_left, inner_smul_right,
    inner_sub_right, Complex.conj_ofReal, planeBargmann_inner_jet, planeBargmann_inner]
  ring

theorem planeExcited_inner_coherent (z w : ℂ) :
    inner ℂ (planeExcited z) (planeCoherent w) =
      (w-z)*inner ℂ (planeCoherent z) (planeCoherent w) := by
  simp only [planeCoherent, planeExcited, inner_smul_left, inner_smul_right,
    inner_sub_left, Complex.conj_ofReal, starRingEnd_self_apply,
    planeJet_inner_bargmann, planeBargmann_inner]
  ring

theorem planeExcited_inner_excited (z w : ℂ) :
    inner ℂ (planeExcited z) (planeExcited w) =
      (1+(w-z)*(conj z-conj w))*inner ℂ (planeCoherent z) (planeCoherent w) := by
  simp only [planeCoherent, planeExcited, inner_smul_left, inner_smul_right,
    inner_sub_left, inner_sub_right, Complex.conj_ofReal, starRingEnd_self_apply,
    planeJet_inner_jet, planeJet_inner_bargmann, planeBargmann_inner_jet, planeBargmann_inner]
  ring

theorem planeCoherent_excited_orthogonal (z : ℂ) :
    inner ℂ (planeCoherent z) (planeExcited z) = 0 := by
  rw [planeCoherent_inner_excited, sub_self, zero_mul]

theorem planeExcited_norm_sq (z : ℂ) : ‖planeExcited z‖^2 = 1 := by
  have h : inner ℂ (planeExcited z) (planeExcited z) =
      inner ℂ (planeCoherent z) (planeCoherent z) := by
    simp only [planeExcited_inner_excited, sub_self, zero_mul, add_zero, one_mul]
  have hr := congrArg Complex.re h
  simpa only [← RCLike.re_eq_complex_re, ← norm_sq_eq_re_inner,
    planeCoherent_norm_sq] using hr

end VortexGap.Fermion

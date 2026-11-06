import VortexGap.Geometry.PlaneExcited
import VortexGap.Frame.CountablePairFrameFields
import VortexGap.Fermion.CountablePairCompression
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open VortexGap.Frame
open scoped InnerProduct ComplexConjugate

def planeTwoFrameMap (z : ℂ) : TwoSpace →ₗ[ℂ] CountableOrbital where
  toFun x := x 0 • planeCoherent z + x 1 • planeExcited z
  map_add' x y := by simp only [PiLp.add_apply, add_smul]; abel
  map_smul' a x := by simp only [PiLp.smul_apply, smul_eq_mul, smul_add, smul_smul, RingHom.id_apply]

theorem planeCoherent_inner_self (z : ℂ) : inner ℂ (planeCoherent z) (planeCoherent z) = 1 := by
  rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, planeCoherent_norm_sq]
  rfl

theorem planeExcited_inner_self (z : ℂ) : inner ℂ (planeExcited z) (planeExcited z) = 1 := by
  rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, planeExcited_norm_sq]
  rfl

theorem planeTwoFrameMap_inner (z : ℂ) (x y : TwoSpace) :
    inner ℂ (planeTwoFrameMap z x) (planeTwoFrameMap z y) = inner ℂ x y := by
  have hvu : inner ℂ (planeExcited z) (planeCoherent z) = 0 := by
    rw [planeExcited_inner_coherent, sub_self, zero_mul]
  change inner ℂ (x 0 • planeCoherent z + x 1 • planeExcited z)
    (y 0 • planeCoherent z + y 1 • planeExcited z) = _
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    planeCoherent_inner_self, planeExcited_inner_self, planeCoherent_excited_orthogonal,
    hvu, mul_zero, mul_one, zero_add, add_zero, PiLp.inner_apply,
    Fin.sum_univ_two, RCLike.inner_apply]

/-- The concrete planar two-frame, with orthonormality proved from its series. -/
def planeTwoFrame (z : ℂ) : CountableTwoFrame where
  toLinearMap := planeTwoFrameMap z
  norm_map' := (LinearMap.norm_map_iff_inner_map_map _).mpr (planeTwoFrameMap_inner z)

theorem planeTwoFrame_first (z : ℂ) :
    planeTwoFrame z (PiLp.single 2 0 1) = planeCoherent z := by
  change (PiLp.single 2 0 (1 : ℂ) : TwoSpace) 0 • planeCoherent z +
    (PiLp.single 2 0 (1 : ℂ) : TwoSpace) 1 • planeExcited z = _
  simp

theorem planeTwoFrame_second (z : ℂ) :
    planeTwoFrame z (PiLp.single 2 1 1) = planeExcited z := by
  change (PiLp.single 2 1 (1 : ℂ) : TwoSpace) 0 • planeCoherent z +
    (PiLp.single 2 1 (1 : ℂ) : TwoSpace) 1 • planeExcited z = _
  simp

theorem planeTwoFramePair_jet (z : ℂ) :
    countableTwoFramePair (planeTwoFrame z) =
      (Real.exp (-‖z‖^2) : ℂ) • countableWedge (planeBargmann z) (planeJet z) := by
  have h : countableWedge (planeBargmann z) (planeJet z - conj z • planeBargmann z) =
      countableWedge (planeBargmann z) (planeJet z) := by
    change countableWedgeRight (planeBargmann z) (planeJet z - conj z • planeBargmann z) = _
    rw [map_sub, map_smul]
    change countableWedge (planeBargmann z) (planeJet z) -
      conj z • countableWedge (planeBargmann z) (planeBargmann z) = _
    rw [countableWedge_self, smul_zero, sub_zero]
  rw [countableTwoFramePair, planeTwoFrame_first, planeTwoFrame_second,
    planeCoherent, planeExcited, countableWedge_smul_smul, h]
  congr 1
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

theorem planeTwoFramePair_norm_sq (z : ℂ) :
    ‖countableTwoFramePair (planeTwoFrame z)‖^2 = 1 := by
  have h : inner ℂ (countableTwoFramePair (planeTwoFrame z))
      (countableTwoFramePair (planeTwoFrame z)) = 1 := by
    simp only [countableTwoFramePair, planeTwoFrame_first, planeTwoFrame_second,
      countableWedge_inner, planeCoherent_inner_self, planeExcited_inner_self,
      planeCoherent_excited_orthogonal, zero_mul, mul_one, sub_zero]
  have hr := congrArg Complex.re h
  simpa only [← RCLike.re_eq_complex_re, ← norm_sq_eq_re_inner, RCLike.one_re] using hr

end VortexGap.Fermion

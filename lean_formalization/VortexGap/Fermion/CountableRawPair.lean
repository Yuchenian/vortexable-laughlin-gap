import VortexGap.Frame.NonorthogonalPair
import VortexGap.Fermion.CountableWedgeLinear
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open VortexGap.Frame
def countableWedgeBilinear : CountableOrbital →ₗ[ℂ] CountableOrbital →ₗ[ℂ] CountablePairSpace where
  toFun u := (countableWedgeRight u).toLinearMap
  map_add' u v := by
    ext w : 1
    exact (countableWedgeLeft w).map_add u v
  map_smul' c u := by
    ext w : 1
    exact (countableWedgeLeft w).map_smul c u

theorem countableWedge_normalized_columns
    (T : EuclideanSpace ℂ (Fin 2) →ₗᵢ[ℂ] CountableOrbital) :
    ‖countableWedge (T (PiLp.single 2 0 1)) (T (PiLp.single 2 1 1))‖ = 1 := by
  let u := T (PiLp.single 2 0 1)
  let v := T (PiLp.single 2 1 1)
  have hu : ‖u‖ = 1 := by simp [u]
  have hv : ‖v‖ = 1 := by simp [v]
  have huv : inner ℂ u v = 0 := by simp [u,v,EuclideanSpace.inner_single_left]
  have hh := countableWedge_inner u v u v
  rw [huv,zero_mul,sub_zero,inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K,
    inner_self_eq_norm_sq_to_K,hu,hv] at hh
  have hr := congrArg Complex.re hh
  simp at hr
  change (((‖countableWedge u v‖:ℝ):ℂ)^2).re = 1 at hr
  rw [← Complex.ofReal_pow,Complex.ofReal_re] at hr
  change ‖countableWedge u v‖ = 1
  nlinarith [norm_nonneg (countableWedge u v)]

theorem countableRawPair_normalize
    (base : EuclideanSpace ℂ (Fin 2) →ₗᵢ[ℂ] CountableOrbital) (u v : CountableOrbital) :
    let T := orthogonalPairFrame base u v
    countableWedge u v = (‖countableWedge u v‖:ℂ) •
      countableWedge (T (PiLp.single 2 0 1)) (T (PiLp.single 2 1 1)) := by
  have h := alternating_pair_normalize countableWedgeBilinear countableWedge_self base u v
  rw [alternating_pair_area_eq_norm countableWedgeBilinear countableWedge_self
    countableWedge_normalized_columns base u v] at h
  exact h
end VortexGap.Fermion

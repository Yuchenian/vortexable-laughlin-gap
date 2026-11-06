import VortexGap.Reference.PairOperator
import VortexGap.Reference.PairCoefficient
import VortexGap.Geometry.PlaneBlockCoordinates
import OAI.Analysis.Laughlin.Planar.Model
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion

theorem upstreamLimitCoefficient_swap (p i j : ℕ) :
    OAI.Laughlin.pairLimitCoefficient p j i = -OAI.Laughlin.pairLimitCoefficient p i j := by
  unfold OAI.Laughlin.pairLimitCoefficient
  by_cases h : i+j=p+1
  · have h' : j+i=p+1 := by omega
    simp only [ite_eq_left h, ite_eq_left h', Nat.cast_ofNat]
    have hd : (2 : ℝ)^p * (j.factorial : ℝ) * (i.factorial : ℝ) =
        (2 : ℝ)^p * (i.factorial : ℝ) * (j.factorial : ℝ) := by ring
    rw [hd]
    ring
  · have h' : j+i ≠ p+1 := by omega
    simp [h, h']

theorem upstreamPlanarCoefficient_swap (p i j : ℕ) :
    OAI.Laughlin.Planar.planarCoefficient p j i = -OAI.Laughlin.Planar.planarCoefficient p i j := by
  simp [OAI.Laughlin.Planar.planarCoefficient, upstreamLimitCoefficient_swap p i j, neg_div]

theorem upstreamPlanarCoefficient_difference (p i j : ℕ) :
    star (OAI.Laughlin.Planar.planarCoefficient p i j -
      OAI.Laughlin.Planar.planarCoefficient p j i) =
      if i+j=p+1 then -(planeBlockCoefficient (p+1) i : ℂ) else 0 := by
  rw [upstreamPlanarCoefficient_swap p i j, sub_neg_eq_add]
  by_cases h : i+j=p+1
  · rw [ite_eq_left h]
    have hi : i ≤ p+1 := by omega
    have hj : p+1-i=j := by omega
    have hr := upstream_ordered_coefficient (p+1) i (by omega) hi
    simp only [Nat.add_sub_cancel_right, hj] at hr
    simp only [OAI.Laughlin.Planar.planarCoefficient, star_add, Complex.star_def,
      Complex.conj_ofReal]
    have hc := congrArg (fun r : ℝ => (r : ℂ)) hr
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_neg, two_mul, Complex.ofReal_add, Nat.cast_ofNat] using hc
  · simp [h, OAI.Laughlin.Planar.planarCoefficient,
      OAI.Laughlin.pairLimitCoefficient]

def planeFiniteBlock (L p : ℕ) : PairSpace (L+1) :=
  WithLp.toLp 2 (fun a => planeBlockVector (p+1) (pairIndexNat a))

theorem upstreamPlanarPair_action (L p : ℕ) (x : OAI.Laughlin.Fock.Space L) :
    upstreamCoordinates L (OAI.Laughlin.Fock.pairEnd L
      (fun i j => OAI.Laughlin.Planar.planarCoefficient p i.val j.val) x) =
      -(pairAnnihilate (planeFiniteBlock L p) (upstreamCoordinates L x)) := by
  rw [upstreamCoordinates_pairAnnihilate]
  have hp : (WithLp.toLp 2 (fun a : PairIndex (L+1) =>
      star (OAI.Laughlin.Planar.planarCoefficient p a.val.1.val a.val.2.val -
        OAI.Laughlin.Planar.planarCoefficient p a.val.2.val a.val.1.val))) =
      (-1 : ℂ) • planeFiniteBlock L p := by
    ext a
    change star (_ - _) = (-1 : ℂ) * planeBlockVector (p+1) (pairIndexNat a)
    rw [upstreamPlanarCoefficient_difference, planeBlockVector_coordinate]
    simp only [pairIndexNat]
    split_ifs with h <;> simp_all
  rw [hp, pairAnnihilate_smul]
  simp

theorem upstreamPlanarPair_norm_sq (L p : ℕ) (x : OAI.Laughlin.Fock.Space L) :
    OAI.Laughlin.Fock.occupationNormSq L (OAI.Laughlin.Fock.pairEnd L
      (fun i j => OAI.Laughlin.Planar.planarCoefficient p i.val j.val) x) =
      ‖pairAnnihilate (planeFiniteBlock L p) (upstreamCoordinates L x)‖^2 := by
  rw [← upstreamCoordinates_norm_sq, upstreamPlanarPair_action, norm_neg]


open scoped BigOperators Matrix

theorem upstreamPairMatrix_toMatrix (L : ℕ) (c : Fin (L+1) → Fin (L+1) → ℂ) :
    OAI.Laughlin.Planar.pairMatrix L c = LinearMap.toMatrix
      (OAI.Laughlin.Fock.occupationBasis L) (OAI.Laughlin.Fock.occupationBasis L)
      (OAI.Laughlin.Fock.pairEnd L c) := by
  ext A B
  simp only [OAI.Laughlin.Planar.pairMatrix, LinearMap.toMatrix_apply,
    OAI.Laughlin.Fock.pairEnd, LinearMap.sum_apply, LinearMap.smul_apply,
    Module.End.mul_apply, map_sum, Finsupp.finsetSum_apply, map_smul,
    Finsupp.smul_apply, smul_eq_mul]

theorem upstreamPairMatrix_action (L : ℕ) (c : Fin (L+1) → Fin (L+1) → ℂ)
    (x : OAI.Laughlin.Fock.Space L) :
    OAI.Laughlin.Planar.pairMatrix L c *ᵥ (OAI.Laughlin.Fock.occupationBasis L).repr x =
      (fun A => upstreamCoordinates L (OAI.Laughlin.Fock.pairEnd L c x) A) := by
  rw [upstreamPairMatrix_toMatrix, LinearMap.toMatrix_mulVec_repr]
  rfl

theorem upstreamPlanar_pairEnergy (L : ℕ) (x : OAI.Laughlin.Fock.Space L) :
    OAI.Laughlin.Planar.pairEnergy L (OAI.Laughlin.Planar.planarPairMatrix L)
      ((OAI.Laughlin.Fock.occupationBasis L).repr x) =
      ∑ p ∈ Finset.range (2*L+1),
        ‖pairAnnihilate (planeFiniteBlock L p) (upstreamCoordinates L x)‖^2 := by
  unfold OAI.Laughlin.Planar.pairEnergy
  apply Finset.sum_congr rfl
  intro p hp
  rw [OAI.Laughlin.Planar.planarPairMatrix, upstreamPairMatrix_action,
    ← EuclideanSpace.norm_sq_eq, upstreamPlanarPair_action, norm_neg]

end VortexGap.Fermion

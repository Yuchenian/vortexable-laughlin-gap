import VortexGap.Reference.PairDegree
import VortexGap.Operator.QuadraticNorm
import OAI.Analysis.Laughlin.Planar.DegreeRestriction
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open Filter
open scoped BigOperators InnerProduct Topology

theorem upstreamDegree_of_countable (L : ℕ) (x : CountableSpace)
    (hx : CountableDegreeAtMost L x) :
    OAI.Laughlin.Fock.DegreeAtMost L L
      ((upstreamCoordinateEquiv L).symm (countableRestrict (L+1) x)) := by
  intro A hA
  have hu := (upstreamCoordinateEquiv L).apply_symm_apply (countableRestrict (L+1) x)
  have hc := congrArg (fun y : Space (L+1) => y A) hu
  change (OAI.Laughlin.Fock.occupationBasis L).repr
    ((upstreamCoordinateEquiv L).symm (countableRestrict (L+1) x)) A =
      countableRestrict (L+1) x A at hc
  rw [hc, countableRestrict_coefficient]
  apply hx (occupationIndex A)
  simpa [occupationIndex, Finset.sum_map] using hA

theorem countablePlane_degree_gap (γ : ℝ)
    (href : ∀ (L : ℕ) (z : OAI.Laughlin.Fock.Space L),
      OAI.Laughlin.Fock.DegreeAtMost L L z →
      γ * OAI.Laughlin.Planar.pairEnergy L (OAI.Laughlin.Planar.planarPairMatrix L)
        ((OAI.Laughlin.Fock.occupationBasis L).repr z) ≤
      OAI.Laughlin.Planar.squareNorm L (OAI.Laughlin.Planar.planarHamiltonian L)
        ((OAI.Laughlin.Fock.occupationBasis L).repr z))
    (L N : ℕ) (x : countableSector N) (hx : CountableDegreeAtMost L x) :
    γ * (inner ℂ x (countablePairLift N planePairOperator x)).re ≤
      ‖countablePairLift N planePairOperator x‖^2 := by
  let y := countableRestrict (L+1) x
  let z := (upstreamCoordinateEquiv L).symm y
  have hu : upstreamCoordinates L z = y := (upstreamCoordinateEquiv L).apply_symm_apply y
  have hf := href L z (upstreamDegree_of_countable L x hx)
  rw [upstreamPlanar_pairEnergy, upstreamPlanar_squareNorm, hu,
    ← planeFiniteHamiltonian_quadratic] at hf
  have he : countableEmbed (L+1) y = (x : CountableSpace) := countableDegree_exact_finite L x hx
  have hh : (countablePairLift N planePairOperator x : CountableSpace) =
      countableEmbed (L+1) (planeFiniteHamiltonian L y) := countablePlane_degree_finite L N x hx
  have hi : inner ℂ (x : CountableSpace) (countablePairLift N planePairOperator x : CountableSpace) =
      inner ℂ y (planeFiniteHamiltonian L y) := by
    rw [hh]
    calc
      _ = inner ℂ (countableEmbed (L+1) y) (countableEmbed (L+1) (planeFiniteHamiltonian L y)) := by rw [he]
      _ = _ := (countableEmbed (L+1)).inner_map_map _ _
  have hn : ‖(countablePairLift N planePairOperator x : CountableSpace)‖ =
      ‖planeFiniteHamiltonian L y‖ := by rw [hh, (countableEmbed (L+1)).norm_map]
  change γ * (inner ℂ (x : CountableSpace) (countablePairLift N planePairOperator x : CountableSpace)).re ≤
    ‖(countablePairLift N planePairOperator x : CountableSpace)‖^2
  rw [hi, hn]
  exact hf

theorem countablePlane_gap_of_upstream_finite (γ : ℝ)
    (href : ∀ (L : ℕ) (z : OAI.Laughlin.Fock.Space L),
      OAI.Laughlin.Fock.DegreeAtMost L L z →
      γ * OAI.Laughlin.Planar.pairEnergy L (OAI.Laughlin.Planar.planarPairMatrix L)
        ((OAI.Laughlin.Fock.occupationBasis L).repr z) ≤
      OAI.Laughlin.Planar.squareNorm L (OAI.Laughlin.Planar.planarHamiltonian L)
        ((OAI.Laughlin.Fock.occupationBasis L).repr z)) (N : ℕ) :
    (countablePairLift N planePairOperator * countablePairLift N planePairOperator -
      (γ : ℂ) • countablePairLift N planePairOperator).IsPositive := by
  let T := countablePairLift N planePairOperator
  apply (VortexGap.quadratic_positive_norm_iff T
    (countablePairLift_positive N _ planePairOperator_positive) γ).mpr
  intro x
  let xs : ℕ → countableSector N := fun n =>
    ⟨countableCutoff n x, countableCutoff_sector n x.property⟩
  have ht : Tendsto xs atTop (𝓝 x) := by
    apply tendsto_subtype_rng.mpr
    exact countableCutoff_tendsto (x : CountableSpace)
  have hl : Continuous (fun y : countableSector N => γ * (inner ℂ y (T y)).re) :=
    continuous_const.mul (Complex.continuous_re.comp (continuous_id.inner T.continuous))
  have hr : Continuous (fun y : countableSector N => ‖T y‖^2) := by fun_prop
  apply le_of_tendsto_of_tendsto ((hl.tendsto x).comp ht) ((hr.tendsto x).comp ht)
  exact Eventually.of_forall fun n => countablePlane_degree_gap γ href
    (∑ i ∈ Finset.range n, i) N (xs n) (countableCutoff_degree n x)
end VortexGap.Fermion


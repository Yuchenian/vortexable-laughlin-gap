import VortexGap.Fermion.PairCompatibility
import VortexGap.Examples.ExteriorPairs

noncomputable section
set_option autoImplicit false
namespace VortexGap.Examples
open VortexGap.Fermion
open scoped InnerProduct

/-- A singular, non-diagonal complex map; compatibility is not restricted to unitaries. -/
def orbitalMix4 : Module.End ℂ (EuclideanSpace ℂ (Fin 4)) :=
  (InnerProductSpace.rankOne ℂ mixedOrbital (PiLp.single 2 0 1)).toLinearMap +
  (InnerProductSpace.rankOne ℂ (PiLp.single 2 1 1) (PiLp.single 2 1 1)).toLinearMap

theorem orbitalMix4_zero : orbitalMix4 (PiLp.single 2 0 1) = mixedOrbital := by
  norm_num [orbitalMix4, InnerProductSpace.rankOne_apply, EuclideanSpace.inner_single_left,
    PiLp.single_apply]

theorem orbitalMix4_one : orbitalMix4 (PiLp.single 2 1 1) = PiLp.single 2 1 1 := by
  norm_num [orbitalMix4, InnerProductSpace.rankOne_apply, EuclideanSpace.inner_single_left,
    PiLp.single_apply]

theorem exteriorMix4_pair :
    exteriorPower orbitalMix4 2 (pairSectorEmbed (pairBasis pair01)) =
      (3 / 5 : ℂ) • pairSectorEmbed (pairBasis pair01) -
        (4 / 5 * Complex.I : ℂ) • pairSectorEmbed (pairBasis pair12) := by
  rw [exteriorPower_pairEmbed, exteriorSquare_pairBasis]
  change pairSectorEmbed (wedgePair (orbitalMix4 (PiLp.single 2 0 1))
    (orbitalMix4 (PiLp.single 2 1 1))) = _
  rw [orbitalMix4_zero, orbitalMix4_one]
  change pairSectorEmbed mixedDecomposable = _
  rw [mixedOrbital_pair, map_sub, map_smul, map_smul]

end VortexGap.Examples

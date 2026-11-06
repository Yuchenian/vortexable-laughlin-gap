import VortexGap.Fermion.PairCovariance
import VortexGap.Examples.Compatibility
import VortexGap.Examples.ExteriorPower

noncomputable section
set_option autoImplicit false
namespace VortexGap.Examples
open VortexGap.Fermion
open scoped InnerProduct ComplexConjugate

theorem fockMix4_pair :
    fockMap orbitalMix4 (pairEmbed (pairBasis pair01)) =
      (3 / 5 : ℂ) • pairEmbed (pairBasis pair01) -
        (4 / 5 * Complex.I : ℂ) • pairEmbed (pairBasis pair12) := by
  rw [fockMap_pairEmbed, exteriorSquare_pairBasis]
  change pairEmbed (wedgePair (orbitalMix4 (PiLp.single 2 0 1))
    (orbitalMix4 (PiLp.single 2 1 1))) = _
  rw [orbitalMix4_zero, orbitalMix4_one]
  change pairEmbed mixedDecomposable = _
  rw [mixedOrbital_pair, map_sub, map_smul, map_smul]

/-- A state spanning the vacuum and a two-particle sector. -/
def vacuumPairState : Space 4 :=
  (3 / 5 : ℂ) • ket ∅ + (4 / 5 * Complex.I : ℂ) • pairEmbed (pairBasis pair01)

theorem fockMix4_superposition :
    fockMap orbitalMix4 vacuumPairState =
      (3 / 5 : ℂ) • ket ∅ + (12 / 25 * Complex.I : ℂ) • pairEmbed (pairBasis pair01) +
        (16 / 25 : ℂ) • pairEmbed (pairBasis pair12) := by
  simp only [vacuumPairState, map_add, map_smul, fockMap_vacuum, fockMix4_pair, smul_sub,
    smul_smul]
  have h1 : (4 / 5 * Complex.I : ℂ) * (3 / 5) = 12 / 25 * Complex.I := by ring
  have h2 : (4 / 5 * Complex.I : ℂ) * (4 / 5 * Complex.I) = -(16 / 25) := by
    ring_nf
    norm_num
  rw [h1, h2, neg_smul, sub_neg_eq_add, add_assoc]

theorem orbitalMix4_two : orbitalMix4 (PiLp.single 2 2 1) = 0 := by
  norm_num [orbitalMix4, InnerProductSpace.rankOne_apply, EuclideanSpace.inner_single_left,
    PiLp.single_apply]

theorem fockMix4_threeParticle :
    fockMap orbitalMix4 (create (PiLp.single 2 2 1) (pairEmbed (pairBasis pair01))) = 0 := by
  have h := congrArg (fun T => T (pairEmbed (pairBasis pair01)))
    (fockMap_create orbitalMix4 (PiLp.single 2 2 1))
  change fockMap orbitalMix4 (create (PiLp.single 2 2 1) (pairEmbed (pairBasis pair01))) =
    create (orbitalMix4 (PiLp.single 2 2 1)) (fockMap orbitalMix4 (pairEmbed (pairBasis pair01))) at h
  simpa [orbitalMix4_two, create] using h

theorem phaseFock_threeParticle :
    fockMap phaseMap threeParticleState = (phaseSectorImage : Space 5) :=
  fockMap_on_sector phaseMap ⟨threeParticleState, threeParticleState_sector⟩

theorem phaseFock_norm (x : Space 5) : ‖fockMap phaseMap x‖ = ‖x‖ :=
  (fockIsometry phaseIsometry).norm_map x

end VortexGap.Examples

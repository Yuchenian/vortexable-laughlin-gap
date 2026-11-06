import VortexGap.Fermion.ExteriorSquare
import VortexGap.Examples.FinitePairs

/-! A decomposable complex pair mixes distinct orbitals, including an ordered-pair sign.
These exact regressions do not constitute a gap-transfer example. -/
noncomputable section
set_option autoImplicit false
namespace VortexGap.Examples
open VortexGap.Fermion
open scoped InnerProduct ComplexConjugate

def pair12 : PairIndex 4 := ⟨(1, 2), by decide⟩

def mixedOrbital : EuclideanSpace ℂ (Fin 4) :=
  (3 / 5 : ℂ) • PiLp.single 2 0 1 + (4 / 5 * Complex.I : ℂ) • PiLp.single 2 2 1

def mixedDecomposable : PairSpace 4 := wedgePair mixedOrbital (PiLp.single 2 1 1)

theorem mixedOrbital_pair :
    mixedDecomposable = (3 / 5 : ℂ) • pairBasis pair01 -
      (4 / 5 * Complex.I : ℂ) • pairBasis pair12 := by
  ext a
  fin_cases a <;> norm_num [mixedDecomposable, mixedOrbital, wedgePair, pairBasis, pair01, pair12]

theorem mixedDecomposable_inner : inner ℂ mixedDecomposable mixedDecomposable = 1 := by
  rw [mixedOrbital_pair]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
  norm_num [pairBasis, EuclideanSpace.inner_single_left, PiLp.single_apply, pair01, pair12,
    map_ofNat]
  ring_nf
  norm_num

theorem mixedDecomposable_annihilation :
    annihilate (PiLp.single 2 1 1) (annihilate mixedOrbital (pairEmbed mixedDecomposable)) =
      ket ∅ := by
  change ((annihilate (PiLp.single 2 (1 : Fin 4) 1) * annihilate mixedOrbital) :
    Module.End ℂ (Space 4)) (pairEmbed mixedDecomposable) = _
  rw [← pairAnnihilate_wedge]
  change pairAnnihilate mixedDecomposable (pairEmbed mixedDecomposable) = _
  rw [pairAnnihilate_pairEmbed, mixedDecomposable_inner, one_smul]

end VortexGap.Examples

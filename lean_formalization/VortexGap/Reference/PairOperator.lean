import VortexGap.Reference.InsertionSign
import VortexGap.Fermion.ExteriorSquare
import OAI.Analysis.Laughlin.Fock.Hamiltonian
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators

def upstreamCoordinateEquiv (L : ℕ) : OAI.Laughlin.Fock.Space L ≃ₗ[ℂ] Space (L+1) :=
  LinearEquiv.ofBijective
    { toFun := upstreamCoordinates L
      map_add' := by intro x y; ext A; simp [upstreamCoordinates]
      map_smul' := by intro c x; ext A; simp [upstreamCoordinates] }
    ⟨upstreamCoordinates_injective L, upstreamCoordinates_surjective L⟩

theorem upstreamCoordinateEquiv_apply (L : ℕ) (x : OAI.Laughlin.Fock.Space L) :
    upstreamCoordinateEquiv L x = upstreamCoordinates L x := rfl

theorem upstreamCoordinates_basis (L : ℕ) (A : Finset (Fin (L+1))) :
    upstreamCoordinates L (OAI.Laughlin.Fock.occupationBasis L A) = ket A := by
  ext B
  simp [upstreamCoordinates, ket, Module.Basis.repr_self, Finsupp.single_apply,
    PiLp.single_apply, eq_comm]

theorem upstreamCoordinates_pairEnd (L : ℕ) (c : Fin (L+1) → Fin (L+1) → ℂ)
    (x : OAI.Laughlin.Fock.Space L) :
    upstreamCoordinates L (OAI.Laughlin.Fock.pairEnd L c x) =
      ∑ i, ∑ j, c i j • annihilateMode j (annihilateMode i (upstreamCoordinates L x)) := by
  change upstreamCoordinateEquiv L _ = _
  simp only [OAI.Laughlin.Fock.pairEnd, LinearMap.sum_apply, LinearMap.smul_apply,
    Module.End.mul_apply, map_sum, map_smul, upstreamCoordinateEquiv_apply,
    upstreamCoordinates_annihilate]

theorem upstreamCoordinates_pairCreateEnd (L : ℕ) (c : Fin (L+1) → Fin (L+1) → ℂ)
    (x : OAI.Laughlin.Fock.Space L) :
    upstreamCoordinates L (OAI.Laughlin.Fock.pairCreateEnd L c x) =
      ∑ i, ∑ j, star (c i j) • createMode i (createMode j (upstreamCoordinates L x)) := by
  change upstreamCoordinateEquiv L _ = _
  simp only [OAI.Laughlin.Fock.pairCreateEnd, LinearMap.sum_apply, LinearMap.smul_apply,
    Module.End.mul_apply, map_sum, map_smul, upstreamCoordinateEquiv_apply,
    upstreamCoordinates_create]

theorem upstreamPair_complex_calibration :
    upstreamCoordinates 1 (OAI.Laughlin.Fock.pairEnd 1
      (fun i j => if i = 0 ∧ j = 1 then Complex.I else 0)
      (OAI.Laughlin.Fock.occupationBasis 1 {0,1})) = Complex.I • ket ∅ := by
  let a : PairIndex 2 := ⟨(0,1), by decide⟩
  have h := pairMode_pairKet a a
  rw [pairKet_occupation] at h
  change annihilateMode (1 : Fin 2) (annihilateMode (0 : Fin 2) (ket {0,1})) =
    (if a = a then ket ∅ else 0) at h
  simp only [ite_true] at h
  simp [upstreamCoordinates_pairEnd, Fin.sum_univ_two, upstreamCoordinates_basis, h]


theorem pairAnnihilate_ordered_coeff {n : ℕ} (c : Fin n → Fin n → ℂ) :
    pairAnnihilate (WithLp.toLp 2 (fun a : PairIndex n => star (c a.val.1 a.val.2 - c a.val.2 a.val.1))) =
      ∑ i, ∑ j, c i j • (annihilateMode j * annihilateMode i) := by
  rw [sum_split_orderedPairs (fun i j => c i j • (annihilateMode j * annihilateMode i))
    (by intro i; simp [mode_square])]
  unfold pairAnnihilate
  apply Finset.sum_congr rfl
  intro a _
  change star (star (c a.val.1 a.val.2 - c a.val.2 a.val.1)) •
    (annihilateMode a.val.2 * annihilateMode a.val.1) = _
  rw [mode_anticommute a.val.1 a.val.2]
  simp only [star_star, sub_smul, smul_neg, sub_eq_add_neg, add_smul, neg_smul]

theorem upstreamCoordinates_pairAnnihilate (L : ℕ)
    (c : Fin (L+1) → Fin (L+1) → ℂ) (x : OAI.Laughlin.Fock.Space L) :
    upstreamCoordinates L (OAI.Laughlin.Fock.pairEnd L c x) =
      pairAnnihilate (WithLp.toLp 2 (fun a : PairIndex (L+1) =>
        star (c a.val.1 a.val.2 - c a.val.2 a.val.1))) (upstreamCoordinates L x) := by
  rw [upstreamCoordinates_pairEnd, pairAnnihilate_ordered_coeff]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]

end VortexGap.Fermion

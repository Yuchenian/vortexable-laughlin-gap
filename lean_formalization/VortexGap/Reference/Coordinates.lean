import OAI.Analysis.Laughlin.Fock.Bidegree
import VortexGap.Fermion.NumberParity
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators InnerProduct

def upstreamCoordinates (L : ℕ) (x : OAI.Laughlin.Fock.Space L) : Space (L+1) :=
  WithLp.toLp 2 (fun A => (OAI.Laughlin.Fock.occupationBasis L).repr x A)

theorem upstreamCoordinates_apply (L : ℕ) (x : OAI.Laughlin.Fock.Space L)
    (A : Finset (Fin (L+1))) :
    upstreamCoordinates L x A = (OAI.Laughlin.Fock.occupationBasis L).repr x A := rfl

theorem upstreamCoordinates_injective (L : ℕ) : Function.Injective (upstreamCoordinates L) := by
  intro x y h
  apply (OAI.Laughlin.Fock.occupationBasis L).repr.injective
  ext A
  exact congrArg (fun z : Space (L+1) => z A) h

theorem upstreamCoordinates_inner (L : ℕ) (x y : OAI.Laughlin.Fock.Space L) :
    inner ℂ (upstreamCoordinates L x) (upstreamCoordinates L y) =
      OAI.Laughlin.Fock.occupationInner L x y := by
  simp [PiLp.inner_apply, RCLike.inner_apply, upstreamCoordinates,
    OAI.Laughlin.Fock.occupationInner, mul_comm]

theorem upstreamCoordinates_norm_sq (L : ℕ) (x : OAI.Laughlin.Fock.Space L) :
    ‖upstreamCoordinates L x‖ ^ 2 = OAI.Laughlin.Fock.occupationNormSq L x := by
  rw [EuclideanSpace.norm_sq_eq]
  rfl

theorem upstreamCoordinates_sector (L N w : ℕ) (x : OAI.Laughlin.Fock.Space L)
    (hx : OAI.Laughlin.Fock.OccupationBidegree L N w x) :
    InSector N (upstreamCoordinates L x) := by
  intro A hA
  exact hx A (Or.inl hA)
theorem upstreamCoordinates_surjective (L : ℕ) : Function.Surjective (upstreamCoordinates L) := by
  intro y
  refine ⟨∑ A, y A • OAI.Laughlin.Fock.occupationBasis L A, ?_⟩
  ext B
  simp [upstreamCoordinates, Module.Basis.repr_self, Finsupp.single_apply]

end VortexGap.Fermion

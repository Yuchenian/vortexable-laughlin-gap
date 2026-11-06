import VortexGap.Frame.ModeFrames

noncomputable section
set_option autoImplicit false
namespace VortexGap.Examples
open VortexGap.Fermion VortexGap.Frame
open scoped BigOperators InnerProduct ComplexOrder

/-- Any number of adjacent, disjoint two-mode cells. -/
def cellPair (k : ℕ) (j : Fin k) : PairIndex (2*k) :=
  ⟨(⟨2*j.val, by omega⟩, ⟨2*j.val+1, by omega⟩), by change 2*j.val < 2*j.val+1; omega⟩

def cellFrames (k : ℕ) : Fin k → TwoFrame (2*k) := fun j => modeFrame (cellPair k j)
def cellPairs (k : ℕ) : Fin k → PairSpace (2*k) := fun j => pairBasis (cellPair k j)

theorem cellPairs_eq (k : ℕ) : cellPairs k = (fun j => pairBasis (cellPair k j)) := rfl

theorem cellPair_injective (k : ℕ) : Function.Injective (cellPair k) := by
  intro j l h
  have hv := congrArg (fun a : PairIndex (2*k) => a.val.1.val) h
  dsimp [cellPair] at hv
  apply Fin.ext
  omega

theorem cell_overlap (k : ℕ) (j l : Fin k) :
    twoFrameOverlap (cellFrames k j) (cellFrames k l) =
      if j = l then LinearMap.id else 0 := by
  by_cases h : j = l
  · subst l; simp [twoFrameOverlap_self]
  · rw [ite_eq_right h]
    apply modeFrameOverlap_zero <;> intro he <;>
      have hv := congrArg Fin.val he <;> dsimp [cellPair] at hv <;>
      have hjl : j.val ≠ l.val := fun hh => h (Fin.ext hh) <;> omega

theorem cell_trace_overlap (k : ℕ) (j l : Fin k) :
    traceNormTwo (twoFrameOverlap (cellFrames k j) (cellFrames k l)) = if j=l then 2 else 0 := by
  rw [cell_overlap]
  split_ifs <;> simp [traceNormTwo_id, traceNormTwo_zero]

theorem cell_schur (k : ℕ) (j : Fin k) :
    ∑ l, traceNormTwo (twoFrameOverlap (cellFrames k j) (cellFrames k l)) = 2 := by
  simp [cell_trace_overlap]

theorem cell_frame_bound (k : ℕ) (q : PairSpace (2*k)) :
    (inner ℂ q ((∑ j, pairRankOne (cellPairs k j)) q)).re ≤ ‖q‖^2 :=
  pairBasis_frame_le_one (cellPair k) (cellPair_injective k) q

theorem cell_reference_gap (k : ℕ) (x : Space (2*k)) :
    (inner ℂ x (frameHamiltonian (fun _ => 1) (cellPairs k) x)).re ≤
      (inner ℂ x ((frameHamiltonian (fun _ => 1) (cellPairs k) *
        frameHamiltonian (fun _ => 1) (cellPairs k)) x)).re :=
  modePairHamiltonian_gap (cellPair k) x

/-- The complete finite transfer instantiated with gamma=beta=1 and C=2,
for arbitrary cell count and arbitrary positive contraction, including cell mixing. -/
theorem cell_frame_transfer {k N : ℕ}
    (M : EuclideanSpace ℂ (Fin (2*k)) →L[ℂ] EuclideanSpace ℂ (Fin (2*k)))
    (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) {x : Space (2*k)} (hx : InSector N x) :
    (1 - 2*‖1-M^2‖ - ‖1-M^2‖^2) *
      (inner ℂ x (filteredHamiltonian M (fun _ => 1) (cellPairs k) x)).re ≤
      (inner ℂ x ((filteredHamiltonian M (fun _ => 1) (cellPairs k) *
        filteredHamiltonian M (fun _ => 1) (cellPairs k)) x)).re := by
  have h := finite_frame_transfer M hM hc (fun _ : Fin k => 1) (by intro; norm_num)
    (cellFrames k) (fun _ => 1) (by intro; norm_num) 2
    (by intro i; simp only [one_mul, mul_one]; exact le_of_eq (cell_schur k i))
    1 (by norm_num)
    (by intro q; simpa only [cellFrames, cellPairs_eq, modeFrame_wedge, Complex.ofReal_one, one_smul, one_mul]
          using cell_frame_bound k q)
    1 (by intro K hK y hy; simpa only [cellFrames, cellPairs_eq, modeFrame_wedge, one_mul]
          using cell_reference_gap k y) hx
  simpa only [cellFrames, cellPairs_eq, modeFrame_wedge, one_mul] using h

end VortexGap.Examples

import VortexGap.Examples.FourModeRankTwo
import VortexGap.Examples.Cells
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open VortexGap.Frame VortexGap.Examples
open scoped InnerProduct ComplexConjugate ComplexOrder

/-- Pair a inside the four-mode cell j, numbered among all two-mode blocks. -/
def rankTwoSlot {k : ℕ} (j : Fin k) (a : Fin 2) : Fin (2*k) :=
  ⟨2*j.val+a.val, by omega⟩

private theorem slot_eq {k : ℕ} (i j : Fin k) (a b : Fin 2) :
    rankTwoSlot i a = rankTwoSlot j b ↔ i=j ∧ a=b := by
  constructor
  · intro h
    have hh := congrArg Fin.val h
    dsimp [rankTwoSlot] at hh
    exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
  · rintro ⟨rfl,rfl⟩; rfl

def rankTwoFrames {k : ℕ} (j : Fin k) (a : Fin 2) := cellFrames (2*k) (rankTwoSlot j a)
def rankTwoCellPair {k : ℕ} (j : Fin k) := slaterPair (fun _ => 1) (rankTwoFrames j)

theorem rankTwoCellPair_eq {k : ℕ} (j : Fin k) :
    rankTwoCellPair j = pairBasis (cellPair _ (rankTwoSlot j 0)) + pairBasis (cellPair _ (rankTwoSlot j 1)) := by
  simp [rankTwoCellPair, slaterPair, rankTwoFrames,cellFrames,Fin.sum_univ_two, modeFrame_wedge]

theorem rankTwoCell_kernel {k : ℕ} (i j : Fin k) :
    slaterKernel (fun _ => 1) (fun _ => 1) (rankTwoFrames i) (rankTwoFrames j) =
      if i=j then 4 else 0 := by
  by_cases h : i=j <;> norm_num [slaterKernel,rankTwoFrames, Fin.sum_univ_two,cell_trace_overlap,slot_eq,h]

theorem rankTwoCell_schur {k : ℕ} (i : Fin k) :
    ∑ j : Fin k, (1/2:ℝ)*slaterKernel (fun _ => 1) (fun _ => 1) (rankTwoFrames i) (rankTwoFrames j) = 2 := by
  norm_num [rankTwoCell_kernel,mul_ite]

theorem rankTwoCell_beta {k : ℕ} (q : PairSpace (2*(2*k))) :
    (inner ℂ q ((∑ j : Fin k, (1/2:ℂ) • pairRankOne (rankTwoCellPair j)) q)).re ≤ ‖q‖^2 := by
  let b := fun (i : Fin k × Fin 2) => cellPair (2*k) (rankTwoSlot i.1 i.2)
  have hinj : Function.Injective b := by
    intro i j h
    obtain ⟨h₁,h₂⟩ := (slot_eq ..).mp ((cellPair_injective _ ) h)
    exact Prod.ext h₁ h₂
  have h := pairBasis_frame_le_one b hinj q
  rw [pairBasis_frame_energy,Fintype.sum_prod_type] at h
  simp only [Fin.sum_univ_two] at h
  apply le_trans _ h
  simp only [LinearMap.sum_apply, inner_sum, Complex.re_sum]
  apply Finset.sum_le_sum
  intro j _
  let u := q (b (j,0))
  let v := q (b (j,1))
  have he : inner ℂ (rankTwoCellPair j) q = u+v := by
    rw [rankTwoCellPair_eq, inner_add_left]
    simp [u,v,b,pairBasis,EuclideanSpace.inner_single_left]
  change (inner ℂ q ((1/2:ℂ) • (inner ℂ (rankTwoCellPair j) q • rankTwoCellPair j))).re ≤ ‖u‖^2+‖v‖^2
  rw [inner_smul_right, inner_smul_right, ← inner_conj_symm q (rankTwoCellPair j), he, Complex.mul_conj]
  norm_num [Complex.mul_re, ← Complex.sq_norm]
  rw [← Complex.ofReal_pow,Complex.ofReal_re]
  have ht := norm_add_le u v
  nlinarith [sq_nonneg (‖u‖-‖v‖),sq_le_sq₀ (norm_nonneg (u+v)) (add_nonneg (norm_nonneg u) (norm_nonneg v)) |>.mpr ht]

end VortexGap.Fermion

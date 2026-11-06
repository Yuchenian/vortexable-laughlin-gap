import VortexGap.Examples.RankTwoCellCross
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open VortexGap.Examples VortexGap.Frame
open scoped InnerProduct ComplexOrder

theorem fourMode_embedded_reference (m : ℕ) (x : Space (4+m)) :
    let H := embeddedReferenceHamiltonian m (fun _ : Unit => (1/2:ℝ)) (fun _ => fourModePair)
    (1/2:ℝ)*(inner ℂ x (H x)).re ≤ ‖H x‖^2 := by
  let T := frameHamiltonian (fun _ : Unit => (1/2:ℝ)) (fun _ => fourModePair)
  let y := fockSplit 4 m x
  have h := Finset.sum_le_sum (s := Finset.univ) (fun (B : Finset (Fin m)) _ => fourMode_reference (referenceSlice B y))
  have hn : ‖referenceAmplify T y‖^2 = ∑ B, ‖T (referenceSlice B y)‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, referenceAmplify_apply]
    rw [Finset.sum_comm]
  dsimp only
  rw [← (fockSplit 4 m).inner_map_map, ← (fockSplit 4 m).norm_map (embeddedReferenceHamiltonian _ _ _ _)]
  change (1/2:ℝ)*(inner ℂ y (fockSplit 4 m (embeddedReferenceHamiltonian _ _ _ x))).re ≤ _
  rw [show fockSplit 4 m (embeddedReferenceHamiltonian m (fun _ : Unit => (1/2:ℝ)) (fun _ => fourModePair) x) =
    referenceAmplify T y from fockSplit_frameInteraction_env _ _ _, hn, referenceAmplify_inner, Complex.re_sum, Finset.mul_sum]
  exact h

private def cellPermutation {k : ℕ} (j : Fin k) :
    Fin (4+(2*(2*k)-4)) ≃ Fin (2*(2*k)) :=
  ((finCongr (show 4+(2*(2*k)-4) = (4*k-4*j.val)+4*j.val by omega)).trans
    (@finAddFlip (4*k-4*j.val) (4*j.val))).trans (finCongr (by omega))

private theorem cellPermutation_first {k : ℕ} (j : Fin k) (i : Fin 4) :
    (cellPermutation j (Fin.castAdd _ i)).val = 4*j.val+i.val := by
  have hi : i.val < 4*k-4*j.val := by omega
  change (finAddFlip (⟨i.val,_⟩ : Fin ((4*k-4*j.val)+4*j.val))).val = _
  rw [finAddFlip_apply_mk_left hi]

private def cellRotation {k : ℕ} (j : Fin k) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (cellPermutation j)

private theorem env_single {n m : ℕ} (i : Fin n) :
    orbitalEnv n m (PiLp.single 2 i 1) = PiLp.single 2 (Fin.castAdd m i) 1 := by
  ext s
  refine Fin.addCases (fun a => ?_) (fun b => ?_) s
  · simp [orbitalEnv_left, PiLp.single_apply]
  · have hn : Fin.natAdd n b ≠ Fin.castAdd m i := by
      intro he
      have hv := congrArg Fin.val he
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
      omega
    simp [orbitalEnv_right, hn]

private theorem cell_pair_rotate {k : ℕ} (j : Fin k) :
    exteriorSquare (cellRotation j).toLinearEquiv.toLinearMap
      (exteriorSquare (orbitalEnv 4 (2*(2*k)-4)).toLinearMap fourModePair) = rankTwoCellPair j := by
  rw [fourModePair_eq,rankTwoCellPair_eq,map_add,map_add]
  congr 1 <;>
    rw [exteriorSquare_pairBasis,exteriorSquare_wedge] <;>
    simp only [LinearIsometry.coe_toLinearMap, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
      env_single,cellRotation,LinearIsometryEquiv.piLpCongrLeft_single]
  all_goals
    convert wedgePair_basis _ using 2 <;> congr 1 <;> apply Fin.ext <;>
      rw [cellPermutation_first] <;> simp [cellPair,rankTwoSlot,pair01,pair23] <;> omega

set_option maxHeartbeats 1600000 in
theorem rankTwoCell_local_reference {k : ℕ} (j : Fin k) (x : Space (2*(2*k))) :
    let H := frameHamiltonian (fun _ : Unit => (1/2:ℝ)) (fun _ => rankTwoCellPair j)
    (1/2:ℝ)*(inner ℂ x (H x)).re ≤ ‖H x‖^2 := by
  let U := cellRotation j
  let m := 2*(2*k)-4
  let w := fun _ : Unit => (1/2:ℝ)
  let y := (fockEquiv U).symm x
  let E := embeddedReferenceHamiltonian m w (fun _ => fourModePair)
  let H := frameHamiltonian w (fun _ => rankTwoCellPair j)
  have hx : fockEquiv U y = x := (fockEquiv U).apply_symm_apply _
  have he := congrArg (fun T => T y) (fockMap_frameInteraction U.toLinearIsometry w
    (fun _ => exteriorSquare (orbitalEnv 4 m).toLinearMap fourModePair))
  change frameHamiltonian w (fun _ => exteriorSquare U.toLinearEquiv.toLinearMap
    (exteriorSquare (orbitalEnv 4 m).toLinearMap fourModePair)) (fockEquiv U y) = fockEquiv U (E y) at he
  simp_rw [show exteriorSquare U.toLinearEquiv.toLinearMap (exteriorSquare (orbitalEnv 4 m).toLinearMap fourModePair) =
    rankTwoCellPair j from cell_pair_rotate j] at he
  change H (fockEquiv U y) = fockEquiv U (E y) at he
  change (1/2:ℝ)*(inner ℂ x (H x)).re ≤ ‖H x‖^2
  rw [← hx,he,(fockEquiv U).inner_map_map,(fockEquiv U).norm_map]
  exact fourMode_embedded_reference m y

private abbrev localCell {k : ℕ} (j : Fin k) :=
  frameHamiltonian (fun _ : Unit => (1/2:ℝ)) (fun _ => rankTwoCellPair j)

private theorem localCell_eq {k : ℕ} (i : Fin k) :
    localCell i = (1/2:ℂ) • ((pairAnnihilate (rankTwoCellPair i)).adjoint * pairAnnihilate (rankTwoCellPair i)) := by
  simp [localCell,frameHamiltonian,pairLift_smul,pairLift_rankOne]

theorem rankTwoCells_reference {k : ℕ} (x : Space (2*(2*k))) :
    let H := frameHamiltonian (fun _ : Fin k => (1/2:ℝ)) rankTwoCellPair
    (1/2:ℝ)*(inner ℂ x (H x)).re ≤ ‖H x‖^2 := by
  have hsum : frameHamiltonian (fun _ : Fin k => (1/2:ℝ)) rankTwoCellPair = ∑ i : Fin k, localCell i := by
    change pairLiftLinear _ _ = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [localCell,frameHamiltonian,pairLiftLinear,pairLift_smul]
  have hp (i j : Fin k) : 0 ≤ (inner ℂ (localCell i x) (localCell j x)).re := by
    by_cases he : i=j
    · subst j; exact (sq_nonneg _).trans_eq (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
    simp only [localCell_eq, LinearMap.smul_apply, Module.End.mul_apply,inner_smul_left,inner_smul_right]
    have hc := rankTwoCell_cross_energy he x
    dsimp only at hc
    norm_num [Complex.mul_re,hc]
  dsimp only
  rw [hsum,LinearMap.sum_apply,inner_sum,Complex.re_sum,Finset.mul_sum]
  calc
    _ ≤ ∑ i : Fin k, ‖localCell i x‖^2 := Finset.sum_le_sum fun i _ => rankTwoCell_local_reference i x
    _ ≤ ∑ i : Fin k, ∑ j : Fin k, (inner ℂ (localCell i x) (localCell j x)).re := by
      apply Finset.sum_le_sum
      intro i _
      exact (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm.trans_le (Finset.single_le_sum (fun j _ => hp i j) (Finset.mem_univ i))
    _ = _ := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ),sum_inner]
      change _ = Complex.re _
      simp only [inner_sum,Complex.re_sum]

theorem rankTwoCells_transfer {k N : ℕ}
    (M : EuclideanSpace ℂ (Fin (2*(2*k))) →L[ℂ] EuclideanSpace ℂ (Fin (2*(2*k))))
    (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) {x : Space (2*(2*k))} (hx : InSector N x) :
    let H := filteredHamiltonian M (fun _ : Fin k => (1/2:ℝ)) rankTwoCellPair
    (1/2-2*‖1-M^2‖-‖1-M^2‖^2)*(inner ℂ x (H x)).re ≤ ‖H x‖^2 := by
  have ht := finite_slater_transfer M hM hc (fun _ : Fin k => (1/2:ℝ))
    (fun _ _ => 1) rankTwoFrames (fun _ => by norm_num)
    (fun _ => 1) (fun _ => by norm_num) 2
    (fun i => by simpa only [mul_one] using (rankTwoCell_schur i).le)
    1 (by norm_num) (fun q => by simpa only [rankTwoCellPair,one_mul,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using! rankTwoCell_beta q)
    (1/2) (fun _ _ y _ => rankTwoCells_reference y) hx
  simpa only [rankTwoCellPair,one_mul] using! ht

end VortexGap.Fermion

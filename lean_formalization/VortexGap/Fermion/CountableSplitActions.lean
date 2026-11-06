import VortexGap.Fermion.CountableSplitFock
import VortexGap.Fermion.CountableOccupationOperators

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct

def countableEnvBasis (j : ℕ) : CountableOrbital :=
  orbitalKet (Equiv.natSumNatEquivNat (Sum.inl j))

def countableSysBasis (j : ℕ) : CountableOrbital :=
  orbitalKet (Equiv.natSumNatEquivNat (Sum.inr j))

theorem countableJoinImage_product (A B : Finset ℕ) :
    countableJoinImage (A,B) =
      countableOccupationOperator countableEnvBasis A
        (countableOccupationImage countableSysBasis B) := by
  rw [countableJoinImage, countableJoinList, countableWord_append,
    countableWordOperator_map, countableWord_map]
  rfl

theorem countableJoinImage_create_env_of_mem (j : ℕ) (A B : Finset ℕ) (hj : j ∈ A) :
    countableCreate (countableEnvBasis j) (countableJoinImage (A,B)) = 0 := by
  rw [countableJoinImage_product, countableOccupationOperator_create_of_mem _ j A hj]

theorem countableJoinImage_create_env_of_not_mem (j : ℕ) (A B : Finset ℕ) (hj : j ∉ A) :
    countableCreate (countableEnvBasis j) (countableJoinImage (A,B)) =
      countableSign j A • countableJoinImage (insert j A,B) := by
  rw [countableJoinImage_product, countableOccupationOperator_create_of_not_mem _ j A hj,
    ← countableJoinImage_product]

theorem countableJoinImage_create_sys_of_mem (j : ℕ) (A B : Finset ℕ) (hj : j ∈ B) :
    countableCreate (countableSysBasis j) (countableJoinImage (A,B)) = 0 := by
  rw [countableJoinImage_product, countableOccupationOperator_create,
    countableCreate_image_of_mem _ j B hj, map_zero, smul_zero]

theorem countableJoinImage_create_sys_of_not_mem (j : ℕ) (A B : Finset ℕ) (hj : j ∉ B) :
    countableCreate (countableSysBasis j) (countableJoinImage (A,B)) =
      ((-1 : ℂ)^A.card * countableSign j B) • countableJoinImage (A,insert j B) := by
  rw [countableJoinImage_product, countableOccupationOperator_create,
    countableCreate_image_of_not_mem _ j B hj, map_smul,
    ← countableJoinImage_product, smul_smul]

theorem countableJoinImage_annihilate_env_of_not_mem (j : ℕ) (A B : Finset ℕ) (hj : j ∉ A) :
    countableAnnihilate (countableEnvBasis j) (countableJoinImage (A,B)) = 0 := by
  apply countableAnnihilate_word_of_not_mem orbitalKet orbitalKet_orthonormal
  simpa only [countableJoinList_mem_env] using hj

theorem countableJoinImage_annihilate_sys_of_not_mem (j : ℕ) (A B : Finset ℕ) (hj : j ∉ B) :
    countableAnnihilate (countableSysBasis j) (countableJoinImage (A,B)) = 0 := by
  apply countableAnnihilate_word_of_not_mem orbitalKet orbitalKet_orthonormal
  simpa only [countableJoinList_mem_sys] using hj

theorem countableAnnihilate_of_signed_create (v : CountableOrbital) (x y : CountableSpace)
    (z : ℂ) (hv : inner ℂ v v = 1) (hz : z * z = 1)
    (hx : countableAnnihilate v x = 0) (hy : countableCreate v x = z • y) :
    countableAnnihilate v y = z • x := by
  have h := congrArg (countableAnnihilate v) hy
  rw [countableAnnihilate_create, hv, one_smul, hx, map_zero, sub_zero, map_smul] at h
  calc
    _ = z • (z • countableAnnihilate v y) := by rw [smul_smul, hz, one_smul]
    _ = z • x := by rw [← h]

theorem countableJoinImage_annihilate_env_of_mem (j : ℕ) (A B : Finset ℕ) (hj : j ∈ A) :
    countableAnnihilate (countableEnvBasis j) (countableJoinImage (A,B)) =
      countableSign j A • countableJoinImage (A.erase j,B) := by
  have hs : countableSign j (A.erase j) = countableSign j A := by
    simpa only [countableFlip_of_mem hj] using countableSign_flip_self j A
  refine countableAnnihilate_of_signed_create _ _ _ _ ?_ (countableSign_sq j A)
    (countableJoinImage_annihilate_env_of_not_mem j _ B (Finset.notMem_erase j A)) ?_
  · exact (orthonormal_iff_ite.mp orbitalKet_orthonormal _ _).trans (ite_eq_left rfl)
  · simpa only [Finset.insert_erase hj, hs] using
      countableJoinImage_create_env_of_not_mem j (A.erase j) B (Finset.notMem_erase j A)

theorem countableJoinImage_annihilate_sys_of_mem (j : ℕ) (A B : Finset ℕ) (hj : j ∈ B) :
    countableAnnihilate (countableSysBasis j) (countableJoinImage (A,B)) =
      ((-1 : ℂ)^A.card * countableSign j B) • countableJoinImage (A,B.erase j) := by
  have hs : countableSign j (B.erase j) = countableSign j B := by
    simpa only [countableFlip_of_mem hj] using countableSign_flip_self j B
  have hz : ((-1 : ℂ)^A.card * countableSign j B) *
      ((-1 : ℂ)^A.card * countableSign j B) = 1 := by
    calc
      _ = ((-1 : ℂ)^A.card * (-1 : ℂ)^A.card) * (countableSign j B * countableSign j B) := by ring
      _ = 1 := by rw [countableSign_sq, ← mul_pow]; norm_num
  refine countableAnnihilate_of_signed_create _ _ _ _ ?_ hz
    (countableJoinImage_annihilate_sys_of_not_mem j A _ (Finset.notMem_erase j B)) ?_
  · exact (orthonormal_iff_ite.mp orbitalKet_orthonormal _ _).trans (ite_eq_left rfl)
  · simpa only [Finset.insert_erase hj, hs] using
      countableJoinImage_create_sys_of_not_mem j A (B.erase j) (Finset.notMem_erase j B)

end VortexGap.Fermion

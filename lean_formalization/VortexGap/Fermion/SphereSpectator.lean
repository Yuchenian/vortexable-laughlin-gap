import VortexGap.Fermion.TensorSector
import VortexGap.Fermion.PairKernelTransport
import Mathlib.Analysis.Calculus.Deriv.Mul
import VortexGap.Geometry.SphereRotatedContact

noncomputable section
namespace VortexGap.Fermion
open OAI.LaughlinGap.Occupation
open scoped ComplexConjugate
variable {n N : ℕ}

theorem pairAnnihilate_in_sector (p : PairSpace n) (x : particleSector n (N+2)) :
    InSector N (pairAnnihilate p x) := by
  simp only [pairAnnihilate, LinearMap.sum_apply,LinearMap.smul_apply]
  exact sector_sum _ _ fun a _ => sector_smul _ (pairMode_sector a x.property)

/-- Contract the first two indices against an ordered pair column, leaving
every spectator slot uncontracted. -/
def spectatorContraction (p : PairSpace n) (x : particleSector n (N+2))
    (a : Fin N → Fin n) : ℂ :=
  ∑ b : PairIndex n, conj (p b) * (sectorTensorIsometry _ _ x).val
    (Fin.cons b.val.1 (Fin.cons b.val.2 a))

theorem spectatorContraction_eq (p : PairSpace n) (x : particleSector n (N+2))
    (a : Fin N → Fin n) :
    spectatorContraction p x a = ((Real.sqrt ((N+2).factorial : ℝ))⁻¹ : ℂ) *
      rawReadout n N (pairAnnihilate p x) a := by
  simp only [spectatorContraction,sectorTensorIsometry_apply,List.ofFn_cons,word_cons,
    Module.End.mul_apply,pairAnnihilate,LinearMap.sum_apply,LinearMap.smul_apply,
    map_sum,map_smul,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [rawReadout_apply]
  change _ = _ * (conj (p b) * word (List.ofFn a) (annihilation b.val.2 (annihilation b.val.1 x)) ∅)
  ring

theorem pairAnnihilate_zero_iff_spectators (p : PairSpace n) (x : particleSector n (N+2)) :
    pairAnnihilate p x = 0 ↔ ∀ a : Fin N → Fin n, spectatorContraction p x a = 0 := by
  constructor
  · intro h a
    simp [spectatorContraction_eq,h]
  · intro h
    have hr (a : Fin N → Fin n) : rawReadout n N (pairAnnihilate p x) a = 0 := by
      have hh := h a
      rw [spectatorContraction_eq] at hh
      have hf : (0:ℝ) < (N+2).factorial := by exact_mod_cast Nat.factorial_pos _
      exact (mul_eq_zero.mp hh).resolve_left (by exact_mod_cast (inv_ne_zero (Real.sqrt_pos.mpr hf).ne'))
    let y : particleSector n N := ⟨pairAnnihilate p x,pairAnnihilate_in_sector p x⟩
    have hy : sectorTensorIsometry n N y = 0 := by
      apply Subtype.ext
      ext a
      rw [sectorTensorIsometry_apply]
      change _ * rawReadout n N (pairAnnihilate p x) a = 0
      rw [hr,mul_zero]
    exact congrArg Subtype.val ((sectorTensorIsometry n N).injective (hy.trans (map_zero _).symm))

open MeasureTheory
theorem continuousContact_zero_iff_all_spectators
    {G : Type*} [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (μ : Measure G) [Measure.IsOpenPosMeasure μ] (p : G → PairSpace n)
    (hp : Continuous p) (h₂ : MemLp p 2 μ) (x : particleSector n (N+2)) :
    continuousFrameHamiltonian μ p x = 0 ↔
      ∀ g a, spectatorContraction (p g) x a = 0 := by
  rw [continuousPairHam_zero_iff_ae μ p h₂]
  constructor
  · intro h
    have hc : Continuous (fun g => pairAnnihilate (p g) (x : Space n)) :=
      (pairAnnihilate_continuous.comp hp).clm_apply continuous_const
    have he : (fun g => pairAnnihilate (p g) (x : Space n)) = fun _ => 0 :=
      Measure.eq_of_ae_eq h hc continuous_const
    exact fun g => (pairAnnihilate_zero_iff_spectators _ x).mp (congrFun he g)
  · intro h
    exact Filter.Eventually.of_forall fun g => (pairAnnihilate_zero_iff_spectators _ x).mpr (h g)

/-- A complex unit phase on a selected ordered pair conjugates in the
annihilation amplitude, independently of the spectator configuration. -/
theorem spectator_phase_test (b : PairIndex n) (x : particleSector n (N+2)) (a : Fin N → Fin n) :
    spectatorContraction (PiLp.single 2 b Complex.I) x a =
      -Complex.I * (sectorTensorIsometry _ _ x).val (Fin.cons b.val.1 (Fin.cons b.val.2 a)) := by
  classical
  simp [spectatorContraction,PiLp.single_apply,apply_ite,ite_mul]

end VortexGap.Fermion
end

noncomputable section
namespace VortexGap.Fermion
open scoped ComplexConjugate
variable {n N : ℕ}

def pairSlice (x : particleSector n (N+2)) (a : Fin N → Fin n) : PairSpace n :=
  WithLp.toLp 2 (fun b => (sectorTensorIsometry _ _ x).val
    (Fin.cons b.val.1 (Fin.cons b.val.2 a)))

theorem spectatorContraction_inner (p : PairSpace n) (x : particleSector n (N+2))
    (a : Fin N → Fin n) : spectatorContraction p x a = inner ℂ p (pairSlice x a) := by
  simp only [spectatorContraction,PiLp.inner_apply,RCLike.inner_apply,pairSlice]
  apply Finset.sum_congr rfl
  intro b _
  exact mul_comm _ _

abbrev headCoeff (x : particleSector n (N+2)) (a : Fin N → Fin n) (i j : Fin n) :=
  (sectorTensorIsometry _ _ x).val (Fin.cons i (Fin.cons j a))

private theorem head_swap (x : particleSector n (N+2)) (a : Fin N → Fin n) (i j : Fin n) :
    headCoeff x a j i = -headCoeff x a i j := by
  let v : Fin (N+2) → Fin n := Fin.cons i (Fin.cons j a)
  have h := (sectorTensorIsometry _ _ x).property 0 1 (by exact Fin.zero_ne_one) v
  have he : v ∘ Equiv.swap 0 1 = Fin.cons j (Fin.cons i a) := by
    funext k
    refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => ?_) k) k
    · simp [v]
    · simp [v]
    · have hk : k.succ.succ ≠ (1 : Fin (N+2)) := by
        intro hk
        have := congrArg Fin.val hk
        simp at this
      simp [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) hk,v]
  rw [he] at h
  exact h

/-- First coordinate follows t and the second follows -t, with the
remaining orbital indices fixed. The ordered-pair Wronskian occurs twice. -/
theorem head_relative_derivative (x : particleSector n (N+2)) (a : Fin N → Fin n)
    (u : Fin n → ℝ → ℂ) (v : Fin n → ℂ) (hu : ∀ i, HasDerivAt (u i) (v i) 0) :
    HasDerivAt (fun t : ℝ => ∑ i, ∑ j, headCoeff x a i j * (u i t * u j (-t)))
      (-2 * ∑ b : PairIndex n, pairSlice x a b *
        (u b.val.1 0 * v b.val.2 - u b.val.2 0 * v b.val.1)) 0 := by
  let f := fun i j => headCoeff x a i j * (v i * u j 0 - u i 0 * v j)
  have hterm (i j : Fin n) : HasDerivAt (fun t : ℝ => headCoeff x a i j * (u i t * u j (-t))) (f i j) 0 := by
    have hj : HasDerivAt (fun t : ℝ => u j (-t)) (-v j) 0 := by
      simpa [Function.comp_def] using (hu j).scomp_of_eq (0:ℝ) (hasDerivAt_id (0:ℝ)).neg (by simp)
    simpa [f,sub_eq_add_neg,mul_comm] using! ((hu i).mul hj).const_mul (headCoeff x a i j)
  have hd : (∑ i, ∑ j, f i j) = _ := sum_split_orderedPairs f (fun i => by simp [f,mul_comm])
  rw [Finset.mul_sum]
  have he : (∑ i, ∑ j, f i j) = ∑ b : PairIndex n, -2 * (pairSlice x a b *
      (u b.val.1 0 * v b.val.2 - u b.val.2 0 * v b.val.1)) := by
    rw [hd]
    apply Finset.sum_congr rfl
    intro b _
    change headCoeff x a _ _ * _ + headCoeff x a b.val.2 b.val.1 * _ = -2 * (headCoeff x a b.val.1 b.val.2 * _)
    rw [head_swap x a b.val.1 b.val.2]
    ring
  rw [← he]
  exact HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => hterm i j

end VortexGap.Fermion
end

noncomputable section
namespace VortexGap.Fermion
open OAI.Laughlin.Rotation
variable {n N : ℕ}

def rotatedHeadAmplitude (x : particleSector (n+2) (N+2)) (a : Fin N → Fin (n+2))
    (g : SourceSU2) (R : ℝ) (d : ℂ) (t : ℝ) : ℂ :=
  ∑ i, ∑ j, headCoeff x a i j *
    (sphereRotatedOrbital n g i R (t*d) * sphereRotatedOrbital n g j R ((-t:ℝ)*d))

theorem rotatedHeadAmplitude_jet (x : particleSector (n+2) (N+2)) (a : Fin N → Fin (n+2))
    (g : SourceSU2) (R : ℝ) (d : ℂ) :
    HasDerivAt (rotatedHeadAmplitude x a g R d)
      (-2 * (sphereChartContact (n+1) 0 1 R d * spectatorContraction (sphereOrbitPair n g) x a)) 0 := by
  let u := fun (i : Fin (n+2)) (t : ℝ) => sphereRotatedOrbital n g i R (t*d)
  have hu (i) : DifferentiableAt ℝ (u i) 0 :=
    (HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin (n+2)))) (fun j _ =>
      (sphereChartOrbital_jet (n+1) j.val R d).const_mul
        (sourceSpinRepresentation (n+1) g⁻¹ j i))).differentiableAt
  rw [spectatorContraction_inner,← sphereRotatedContact_eq_inner]
  simpa only [u,Complex.ofReal_zero,zero_mul,sphereRotatedContact,rotatedHeadAmplitude]
    using! head_relative_derivative x a u (fun i => deriv (u i) 0) (fun i => (hu i).hasDerivAt)

theorem rotatedHeadAmplitude_zero_iff (x : particleSector (n+2) (N+2)) (a : Fin N → Fin (n+2))
    (g : SourceSU2) (R : ℝ) (hR : 0 < R) :
    deriv (rotatedHeadAmplitude x a g R 1) 0 = 0 ↔ spectatorContraction (sphereOrbitPair n g) x a = 0 := by
  rw [(rotatedHeadAmplitude_jet x a g R 1).deriv,sphereChartContact_apply _ _ _ (by decide)]
  have h₁ : 0 < Real.sqrt (((n+1+1:ℕ):ℝ)/(4*Real.pi*R^2)) := by positivity
  have h₂ : 0 < Real.sqrt (((n+1+1:ℕ):ℝ)*(n+1:ℕ)/(4*Real.pi*R^2)) := by positivity
  push_cast at h₁ h₂
  simp [h₁.ne', h₂.ne', hR.ne']

end VortexGap.Fermion
end

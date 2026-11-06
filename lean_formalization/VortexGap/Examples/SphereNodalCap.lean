import VortexGap.Physical.SphereProjectedKernel
import VortexGap.Geometry.SphereBloch
import VortexGap.Physical.SphereProjectedGap
import VortexGap.Examples.SphereAxial
import VortexGap.Physical.SphereRoundDensity

noncomputable section

namespace VortexGap.Fermion
open MeasureTheory OAI.Laughlin.Rotation VortexGap.Frame
open scoped InnerProduct ComplexOrder Matrix

private def capMass (m : ℕ) (g : SourceSU2) : ℝ := (‖g.val 0 0‖^2)^m

private theorem capMass_cont (m : ℕ) : Continuous (capMass m) :=
  by
    have hc : Continuous (fun g : SourceSU2 => g.val 0 0) := (continuous_apply 0).comp ((continuous_apply 0).comp continuous_subtype_val)
    exact (hc.norm.pow 2).pow m

private theorem capMass_bounds (m : ℕ) (g : SourceSU2) : 0 ≤ capMass m g ∧ capMass m g ≤ 1 := by
  have h := unitary_entry_norm_le_one g.val g.property.1 0 0
  exact ⟨by unfold capMass; positivity, pow_le_one₀ (sq_nonneg _) (by nlinarith [norm_nonneg (g.val 0 0)])⟩

def sphereCapNodal (n : ℕ) (g : SourceSU2) : ℂ := ((1-capMass (10000*(n+2)) g : ℝ):ℂ)

theorem sphereCapNodal_cont (n : ℕ) : Continuous (sphereCapNodal n) :=
  Complex.continuous_ofReal.comp (continuous_const.sub (capMass_cont _))

theorem sphereCapNodal_node (n : ℕ) : sphereCapNodal n 1 = 0 := by
  simp [sphereCapNodal,capMass]

private theorem cap_lower (n : ℕ) (j : ℕ) (hj : j=2 ∨ j=4) (g : SourceSU2) :
    1-4*capMass (10000*(n+2)) g ≤ ‖sphereCapNodal n g‖^j := by
  let m := capMass (10000*(n+2)) g
  have hb := capMass_bounds (10000*(n+2)) g
  have h0 : 0 ≤ m := hb.1
  have h1 : m ≤ 1 := hb.2
  change 1-4*m ≤ ‖((1-m : ℝ):ℂ)‖^j
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr h1)]
  rcases hj with rfl|rfl
  · nlinarith [sq_nonneg m]
  · nlinarith [mul_nonneg (sq_nonneg m) (show 0 ≤ 6-4*m+m^2 by nlinarith [sq_nonneg m])]

private theorem cap_energy (n j : ℕ) (hj : j=2 ∨ j=4) (D : ℝ) (hD : 0 ≤ D)
    (hsize : D ≤ 2*(n+2:ℕ)) (e : SourceSU2 → ℝ) (he : Continuous e)
    (hn : ∀ g, 0 ≤ e g) (hcap : ∀ g, e g ≤ D*(∫ h, e h ∂sourceHaar)) :
    (999/1000:ℝ)*(∫ g,e g ∂sourceHaar) ≤ ∫ g, ‖sphereCapNodal n g‖^j * e g ∂sourceHaar := by
  let m := 10000*(n+2)
  let T := ∫ g,e g ∂sourceHaar
  have hT : 0 ≤ T := integral_nonneg hn
  have point (g) : e g - 4*capMass m g*(D*T) ≤ ‖sphereCapNodal n g‖^j * e g := by
    have h := mul_le_mul_of_nonneg_right (cap_lower n j hj g) (hn g)
    have h' := mul_le_mul_of_nonneg_left (hcap g) (mul_nonneg (by norm_num : (0:ℝ)≤4) (capMass_bounds m g).1)
    change 4*capMass m g*e g ≤ 4*capMass m g*(D*T) at h'
    change (1-4*capMass m g)*e g ≤ _ at h
    linarith
  have hc : Continuous (fun g => 4*capMass m g*(D*T)) := (continuous_const.mul (capMass_cont m)).mul continuous_const
  have hi := integral_mono (μ := sourceHaar) ((he.sub hc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((((sphereCapNodal_cont n).norm.pow j).mul he).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) point
  change (∫ g, e g-4*capMass m g*(D*T) ∂sourceHaar) ≤ _ at hi
  rw [integral_sub (he.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)), integral_mul_const,
    integral_const_mul] at hi
  change T-4*(∫ g, capMass m g ∂sourceHaar)*(D*T) ≤ _ at hi
  rw [show (∫ g,capMass m g ∂sourceHaar)=1/((m:ℝ)+1) from sphereHaar_radial_moment m] at hi
  have hcoef : 4*D/((m:ℝ)+1) ≤ 1/1000 := by
    apply (div_le_iff₀ (by positivity)).mpr
    dsimp [m]; push_cast at *; linarith
  change T-4*(1/((m:ℝ)+1))*(D*T) ≤ ∫ g, ‖sphereCapNodal n g‖^j * e g ∂sourceHaar at hi
  apply le_trans _ hi
  change 999/1000*T ≤ _
  nlinarith [mul_le_mul_of_nonneg_right hcoef hT,show 4*(1/((m:ℝ)+1))*(D*T)=(4*D/((m:ℝ)+1))*T by ring]

private theorem orbital_value_le (n : ℕ) (x : EuclideanSpace ℂ (Fin (n+2))) (g : SourceSU2) :
    ‖sphereOrbitalValue (n+1) x g‖ ≤ ‖x‖ := by
  let v := sphereSpinFrame n g (PiLp.single 2 0 1)
  have hv : ‖v‖=1 := by simp [v]
  have hcol (i : Fin (n+2)) : v i = sourceSpinRepresentation (n+1) g i 0 := by
    change ((sphereSpinColumns n g) *ᵥ (Pi.single 0 (1:ℂ))) i = _
    simp [Matrix.mulVec,dotProduct,sphereSpinColumns]
  have he : sphereOrbitalValue (n+1) x g = inner ℂ v x := by
    simp only [sphereOrbitalValue,PiLp.inner_apply,RCLike.inner_apply,hcol,mul_comm]
  rw [he]
  simpa only [hv,one_mul] using norm_inner_le_norm v x

theorem sphereCapNodal_gram (n : ℕ) :
    let G := gramOperator (sphereScalarMap (n+1) (sphereCapNodal n) (sphereCapNodal_cont n))
    (999/1000:ℝ) • 1 ≤ G ∧ G ≤ (1:ℝ) • 1 := by
  let f := sphereCapNodal n
  have hf := sphereCapNodal_cont n
  let F := sphereScalarMap (n+1) f hf
  have hhi (z) : ‖f z‖^2 ≤ 1 := by
    have h := capMass_bounds (10000*(n+2)) z
    change ‖((1-capMass _ z : ℝ):ℂ)‖^2 ≤ 1
    rw [Complex.norm_real,Real.norm_eq_abs,sq_abs]
    exact pow_le_one₀ (by linarith [h.2]) (by linarith [h.1])
  refine ⟨?_,(sphereScalarGram_bounds (n+1) f hf 0 1 (by norm_num) (fun _ => sq_nonneg _) hhi).2⟩
  have hp : ((999/1000:ℝ) • (1 : EuclideanSpace ℂ (Fin (n+2)) →L[ℂ] _)).IsPositive := by
    change ((↑(999/1000:ℝ):ℂ) • (1 : EuclideanSpace ℂ (Fin (n+2)) →L[ℂ] _)).IsPositive
    exact ContinuousLinearMap.nonneg_iff_isPositive.mp (smul_nonneg (by exact_mod_cast (by norm_num : (0:ℝ) ≤ 999/1000)) zero_le_one)
  apply positive_operator_le_of_energy _ _ hp (ContinuousLinearMap.nonneg_iff_isPositive.mp (gramOperator_nonneg F))
  intro x
  let e := fun g => ‖sphereOrbitalValue (n+1) x g‖^2
  let D : ℝ := (n+1:ℕ)+1
  have hid : D*(∫ z,e z ∂sourceHaar) = ‖x‖^2 :=
    (sphereOrbitalValue_parseval (n+1) x).trans (EuclideanSpace.norm_sq_eq x).symm
  have h := cap_energy n 2 (Or.inl rfl) D (by dsimp [D]; positivity) (by dsimp [D]; push_cast; linarith)
    e ((sphereOrbitalValue_continuous (n+1) x).norm.pow 2) (fun _ => sq_nonneg _)
    (fun z => by rw [hid]; exact pow_le_pow_left₀ (norm_nonneg _) (orbital_value_le n x z) 2)
  change (inner ℂ x ((↑(999/1000:ℝ):ℂ) • x)).re ≤ (inner ℂ x (F.adjoint (F x))).re
  rw [inner_smul_right,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    ContinuousLinearMap.adjoint_inner_right, ← RCLike.re_eq_complex_re, ← norm_sq_eq_re_inner]
  rw [← norm_sq_eq_re_inner,← hid,sphereScalarMap_norm_sq]
  simp only [norm_mul,mul_pow]
  calc
    _ = D*(999/1000*(∫ z,e z ∂sourceHaar)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by dsimp [D]; positivity)

theorem sphereCapNodal_pair (n : ℕ) (q : PairSpace (n+2)) :
    (999/1000:ℝ)*(∫ g, ‖inner ℂ (sphereOrbitPair n g) q‖^2 ∂spherePairMeasure n) ≤
      ∫ g, ‖sphereCapNodal n g‖^4 * ‖inner ℂ (sphereOrbitPair n g) q‖^2 ∂spherePairMeasure n := by
  let p := sphereOrbitPair n
  let S := spherePairSector n
  let P := S.starProjection
  let e := fun g => ‖inner ℂ (p g) q‖^2
  let D : ℝ := 2*n+1
  have hp := (sphereOrbitPair_continuous n).memLp_of_hasCompactSupport (μ := spherePairMeasure n)
    (p := 2) (HasCompactSupport.of_compactSpace _)
  have henergy := continuousPairAnalysis_energy (spherePairMeasure n) p hp q
  rw [continuousPairAnalysis,operatorAnalysis_norm_sq,spherePairMeasure_operator] at henergy
  have fixP : P (P q) = P q := S.starProjection_eq_self_iff.mpr (S.starProjection_apply_mem q)
  have hnorm : (inner ℂ q (P q)).re = ‖P q‖^2 := by
    have h := S.inner_starProjection_left_eq_right q (P q)
    rw [fixP] at h
    rw [← h]
    exact (norm_sq_eq_re_inner (𝕜:=ℂ) _).symm
  have hid : D*(∫ z,e z ∂sourceHaar) = ‖P q‖^2 := by
    change (∫ z,e z ∂spherePairMeasure n) = (inner ℂ q (P q)).re at henergy
    rw [hnorm,spherePairMeasure,integral_smul_measure,ENNReal.toReal_ofReal (by positivity),smul_eq_mul] at henergy
    exact henergy
  have hcap (z) : e z ≤ D*(∫ g,e g ∂sourceHaar) := by
    have hmem : p z ∈ S := Submodule.subset_span (Set.mem_range_self z)
    have heq := S.inner_starProjection_left_eq_right (p z) q
    rw [S.starProjection_eq_self_iff.mpr hmem] at heq
    have hp1 : ‖p z‖^2=1 := by
      rw [norm_sq_eq_re_inner (𝕜:=ℂ),sphereOrbitPair_inner]
      simp
    have hp' : ‖p z‖=1 := by nlinarith [norm_nonneg (p z)]
    rw [hid]
    dsimp only [e]; rw [heq]
    exact pow_le_pow_left₀ (norm_nonneg _) (by simpa only [hp',one_mul] using norm_inner_le_norm (p z) (P q)) 2
  have h := cap_energy n 4 (Or.inr rfl) D (by dsimp [D]; positivity)
    (by dsimp [D]; push_cast; linarith) e (((sphereOrbitPair_continuous n).inner continuous_const).norm.pow 2)
    (fun _ => sq_nonneg _) hcap
  simp only [spherePairMeasure,integral_smul_measure,ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*(n:ℝ)+1),smul_eq_mul]
  calc
    _ = D*(999/1000*(∫ z,e z ∂sourceHaar)) := by dsimp [D,e,p]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by dsimp [D]; positivity)

theorem sphereCapNodal_gap (n N : ℕ) (γ : ℝ)
    (href : ∀ K ≤ N, ∀ y : Space (n+2), InSector K y →
      let H := pairLift (spherePairSector n).starProjection.toLinearMap
      γ*(inner ℂ y (H y)).re ≤ (inner ℂ y ((H*H) y)).re) :
    ∀ t ∈ spectrum ℝ (sphereSectorHam n N (spherePhysicalPair n (sphereCapNodal n) (sphereCapNodal_cont n))),
      t=0 ∨ (1000/999:ℝ)*(γ-14/1000-(1/1000)^2) ≤ t := by
  intro t ht
  have h := sphere_projected_gap n N _ (sphereCapNodal_cont n) (999/1000) 1 (999/1000) γ
    (by norm_num) (by norm_num) (by norm_num) (sphereCapNodal_gram n).1 (sphereCapNodal_gram n).2
    (sphereCapNodal_pair n) href t ht
  convert h using 2 <;> ring

theorem sphereCapNodal_two (n : ℕ) :
    ∀ t ∈ spectrum ℝ (sphereSectorHam n 2 (spherePhysicalPair n (sphereCapNodal n) (sphereCapNodal_cont n))),
      t=0 ∨ (0.9869:ℝ) < t := by
  intro t ht
  exact (sphereCapNodal_gap n 2 1 (sphereReference_two n) t ht).imp_right (fun hh => lt_of_lt_of_le (by norm_num) hh)

theorem sphereCapNodal_bloch (n : ℕ) (g : SourceSU2) :
    sphereCapNodal n g = ((1-((1+(sphereBloch g).val.2)/2)^(10000*(n+2)) : ℝ):ℂ) := by
  have h := congrArg Complex.re (congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp g.property.1) 0) 0)
  have h' : Complex.normSq (g.val 0 0) + Complex.normSq (g.val 1 0) = 1 := by
    simpa [Matrix.mul_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,Complex.mul_conj,
      Fin.sum_univ_two,mul_comm] using h
  have hs : ‖g.val 0 0‖^2 = (1+(sphereBloch g).val.2)/2 := by
    rw [← Complex.normSq_eq_norm_sq]
    change _ = (1+(Complex.normSq _-Complex.normSq _))/2
    linarith
  simp only [sphereCapNodal,capMass,hs]

theorem sphereCapNodal_fiber (n : ℕ) : sphereFiberInvariant (sphereCapNodal n) := by
  intro g z hz
  rw [sphereCapNodal_bloch,sphereCapNodal_bloch,sphereBloch_phase g z hz]

theorem sphereCapNodal_twentyFifth (n N : ℕ)
    (href : ∀ K ≤ N, ∀ y : Space (n+2), InSector K y →
      let H := pairLift (spherePairSector n).starProjection.toLinearMap
      (1/25:ℝ)*(inner ℂ y (H y)).re ≤ (inner ℂ y ((H*H) y)).re) :
    ∀ t ∈ spectrum ℝ (sphereSectorHam n N (spherePhysicalPair n (sphereCapNodal n) (sphereCapNodal_cont n))),
      t=0 ∨ (0.0260:ℝ) < t := by
  intro t ht
  exact (sphereCapNodal_gap n N (1/25) href t ht).imp_right (fun hh => lt_of_lt_of_le (by norm_num) hh)

theorem sphereCapNodal_fifth (n N : ℕ)
    (href : ∀ K ≤ N, ∀ y : Space (n+2), InSector K y →
      let H := pairLift (spherePairSector n).starProjection.toLinearMap
      (1/5:ℝ)*(inner ℂ y (H y)).re ≤ (inner ℂ y ((H*H) y)).re) :
    ∀ t ∈ spectrum ℝ (sphereSectorHam n N (spherePhysicalPair n (sphereCapNodal n) (sphereCapNodal_cont n))),
      t=0 ∨ (0.1861:ℝ) < t := by
  intro t ht
  exact (sphereCapNodal_gap n N (1/5) href t ht).imp_right (fun hh => lt_of_lt_of_le (by norm_num) hh)

theorem sphereCapNodal_laughlin (n N : ℕ) (hQ : 3*((N+2)-1)=n+1) :
    let f := sphereCapNodal n
    let hf := sphereCapNodal_cont n
    ∃ l y : particleSector (n+2) (N+2), VortexGap.SpherePolynomial.sectorPoly l = VortexGap.SpherePolynomial.laughlin (N+2) ∧ y ≠ 0 ∧
      LinearMap.ker (sphereSectorHam n (N+2) (spherePhysicalPair n f hf)).toLinearMap = ℂ ∙ y ∧
      ∀ z, sphereDeformedWave f hf y z = (∏ i, f (z i)) * sphereReferenceWave l z := by
  exact sphere_projected_laughlin n N hQ _ _ (gramOperator_strict _ (999/1000) (by norm_num) (sphereCapNodal_gram n).1)
    (999/1000) (by norm_num) (sphereCapNodal_pair n)

end VortexGap.Fermion

namespace VortexGap.Fermion
open MeasureTheory Metric VortexGap.Geometry OAI.Laughlin.Rotation VortexGap.SpherePolynomial VortexGap.Frame
open scoped ComplexConjugate

private theorem projected_orbital_gram (q : ℕ) (f : SourceSU2 → ℂ) (hf : Continuous f)
    (hF : IsStrictlyPositive (gramOperator (sphereScalarMap q f hf)))
    (i j : Fin (q+1)) :
    (∫ g, conj (sphereFilteredValue q f hf g i) * sphereFilteredValue q f hf g j
      ∂sphereOrbitalMeasure q) = if i=j then 1 else 0 := by
  let F := sphereScalarMap q f hf
  have h := gramNormalized_inner F hF (PiLp.single 2 i 1) (PiLp.single 2 j 1)
  change inner ℂ (F (gramInvSqrt F (PiLp.single 2 i 1))) (F (gramInvSqrt F (PiLp.single 2 j 1))) = _ at h
  rw [show F = operatorAnalysis _ _ (sphereScalarRow_memLp q f hf) from rfl,
    operatorAnalysis_inner_integral] at h
  simpa [sphereFilteredValue,F,RCLike.inner_apply,mul_comm,EuclideanSpace.inner_single_left,eq_comm] using! h

theorem sphereProjectedWave_inner {q N : ℕ} (f : SourceSU2 → ℂ) (hf : Continuous f)
    (hF : IsStrictlyPositive (gramOperator (sphereScalarMap q f hf)))
    (x y : particleSector (q+1) N) :
    (∫ z, conj (sphereDeformedWave f hf x z) * sphereDeformedWave f hf y z
      ∂Measure.pi (fun _ => sphereOrbitalMeasure q)) = inner ℂ x y := by
  let _ : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) := inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  let _ : SecondCountableTopology SourceSU2 := inferInstanceAs (SecondCountableTopology ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ)))
  exact sectorWave_gram _ _ (sphereFilteredValue_continuous q f hf)
    (projected_orbital_gram q f hf hF) x y

theorem sphereProjected_round_norm {q N : ℕ} (f : SourceSU2 → ℂ) (hf : Continuous f)
    (hi : sphereFiberInvariant f) (hG : IsStrictlyPositive (gramOperator (sphereScalarMap q f hf)))
    (x : particleSector (q+1) N) :
    (∫ p, roundDensity f hf hi x p ∂Measure.pi (fun _ => ENNReal.ofReal ((q:ℝ)+1) • normalizedRoundArea)) = ‖x‖^2 := by
  have hm := sphereOrbital_round_configuration q N
  rw [← hm.map_eq,integral_map hm.aemeasurable (roundDensity_continuous f hf hi x).aestronglyMeasurable]
  simp_rw [roundDensity_lift]
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have h := sphereProjectedWave_inner f hf hG x x
  simpa only [Complex.conj_mul',Complex.ofReal_pow] using! h.trans (inner_self_eq_norm_sq_to_K (𝕜:=ℂ) x)

def sphereCapRound (n : ℕ) (p : RoundPoint) : ℂ := ((1-((1+(cartesianBloch p).val.2)/2)^(10000*(n+2)) : ℝ):ℂ)

theorem sphereCapNodal_round_law (n N : ℕ) (hQ : 3*((N+2)-1)=n+1) :
    ∃ l y : particleSector (n+2) (N+2), sectorPoly l = laughlin (N+2) ∧ y ≠ 0 ∧
      LinearMap.ker (sphereSectorHam n (N+2) (spherePhysicalPair n (sphereCapNodal n) (sphereCapNodal_cont n))).toLinearMap = ℂ ∙ y ∧
      (∀ p, roundDensity (sphereCapNodal n) (sphereCapNodal_cont n) (sphereCapNodal_fiber n) y p =
        (∏ i, ‖sphereCapRound n (p i)‖^2) * roundReferenceDensity l p) ∧
      (∫ p, ((∏ i, ‖sphereCapRound n (p i)‖^2) * roundReferenceDensity l p)/‖y‖^2
        ∂Measure.pi (fun _ => ENNReal.ofReal ((n:ℝ)+2) • normalizedRoundArea)) = 1 := by
  obtain ⟨l,y,hp,hy,hk,hw⟩ := sphereCapNodal_laughlin n N hQ
  have hd (p : Fin (N+2) → RoundPoint) : roundDensity (sphereCapNodal n) (sphereCapNodal_cont n)
      (sphereCapNodal_fiber n) y p = (∏ i, ‖sphereCapRound n (p i)‖^2) * roundReferenceDensity l p := by
    let g := fun i => (roundBloch_onto (p i)).choose
    have hv (i) : roundBloch (g i) = p i := (roundBloch_onto (p i)).choose_spec
    have hr (i) : sphereCapNodal n (g i) = sphereCapRound n (p i) := by
      rw [← hv i,sphereCapNodal_bloch]; rfl
    have h := roundDensity_lift _ (sphereCapNodal_cont n) (sphereCapNodal_fiber n) y g
    rw [show (fun i => roundBloch (g i)) = p from funext hv,hw] at h
    simpa only [hr,norm_mul,norm_prod,mul_pow,Finset.prod_pow,roundReferenceDensity,g] using h
  refine ⟨l,y,hp,hy,hk,hd,?_⟩
  have hG := gramOperator_strict _ (999/1000) (by norm_num) (sphereCapNodal_gram n).1
  simp_rw [← hd]
  rw [integral_div]
  have ht := sphereProjected_round_norm (q:=n+1) _ (sphereCapNodal_cont n) (sphereCapNodal_fiber n) hG y
  rw [show (n:ℝ)+2 = ((n+1:ℕ):ℝ)+1 by push_cast; ring, ht]
  exact div_self (pow_ne_zero _ (norm_ne_zero_iff.mpr hy))

end VortexGap.Fermion

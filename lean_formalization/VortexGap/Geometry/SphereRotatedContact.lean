import VortexGap.Geometry.SphereChartContact
import VortexGap.Geometry.SpherePairOrbit
import VortexGap.Frame.ContinuousPairSynthesis
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open OAI.Laughlin.Rotation MeasureTheory
open scoped Matrix ComplexConjugate

/-- Orbital i in the local spin chart whose north pole has been rotated by g. -/
def sphereRotatedOrbital (n : ℕ) (g : SourceSU2) (i : Fin (n+2)) (R : ℝ) (z : ℂ) : ℂ :=
  ∑ j : Fin (n+2), sourceSpinRepresentation (n+1) g⁻¹ j i * sphereChartOrbital (n+1) j.val R z

/-- Homogeneous-polynomial evaluation in the rotated spinor coordinates. -/
theorem sphereRotatedOrbital_spinor (n : ℕ) (g : SourceSU2) (i : Fin (n+2)) (R : ℝ) (z : ℂ) :
    let w := z/(2*R)
    let k := g⁻¹
    sphereRotatedOrbital n g i R z =
      (Real.sqrt (((n+2:ℕ):ℝ)/(4*Real.pi*R^2)):ℂ) /
      ((Real.sqrt (1+‖w‖^2):ℂ)^(n+1)) *
      ((Real.sqrt ((n+1).choose i.val : ℝ):ℂ) *
       (k.val 0 1 + k.val 1 1*w)^i.val * (k.val 0 0 + k.val 1 0*w)^(n+1-i.val)) := by
  dsimp only
  have hh := sourceSpinRepresentation_polynomial (RingHom.id ℂ) (n+1) g⁻¹ 1 (z/(2*R)) i
  simp only [RingHom.id_apply, one_pow, mul_one] at hh
  rw [← hh, Finset.mul_sum, sphereRotatedOrbital]
  apply Finset.sum_congr rfl
  intro j _
  have hs : Real.sqrt (((n+2:ℕ):ℝ)*((n+1).choose j.val)/(4*Real.pi*R^2)) =
      Real.sqrt (((n+2:ℕ):ℝ)/(4*Real.pi*R^2))*Real.sqrt ((n+1).choose j.val : ℝ) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    ring
  simp only [sphereChartOrbital, hs, Complex.ofReal_mul]
  ring

private theorem sphereRotated_origin (n : ℕ) (g : SourceSU2) (i : Fin (n+2)) (R : ℝ) :
    sphereRotatedOrbital n g i R 0 =
      conj (sourceSpinRepresentation (n+1) g i 0) * sphereChartOrbital (n+1) 0 R 0 := by
  simp [sphereRotatedOrbital, sphereChartOrbital_origin, sourceSpinRepresentation_inv,
    Matrix.conjTranspose_apply, mul_ite]

private theorem sphereRotated_jet (n : ℕ) (g : SourceSU2) (i : Fin (n+2)) (R : ℝ) (d : ℂ) :
    deriv (fun t : ℝ => sphereRotatedOrbital n g i R (t*d)) 0 =
      conj (sourceSpinRepresentation (n+1) g i 1) *
        deriv (fun t : ℝ => sphereChartOrbital (n+1) 1 R (t*d)) 0 := by
  have h := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin (n+2))))
    (fun j _ => (sphereChartOrbital_jet (n+1) j.val R d).const_mul (sourceSpinRepresentation (n+1) g⁻¹ j i))
  rw [(sphereChartOrbital_jet (n+1) 1 R d).deriv]
  have h1 (j : Fin (n+2)) : j.val = 1 ↔ j = 1 := by change j.val = (1 : Fin (n+2)).val ↔ _; exact Fin.ext_iff.symm
  simpa [sphereRotatedOrbital, sourceSpinRepresentation_inv, Matrix.conjTranspose_apply,
    mul_ite, h1] using! h.deriv

/-- Antisymmetric derivative at coincidence, evaluated on arbitrary ordered-pair coefficients. -/
def sphereRotatedContact (n : ℕ) (R : ℝ) (g : SourceSU2) (d : ℂ) (x : PairSpace (n+2)) : ℂ :=
  ∑ a : PairIndex (n+2), x a *
    (sphereRotatedOrbital n g a.val.1 R 0 * deriv (fun t : ℝ => sphereRotatedOrbital n g a.val.2 R (t*d)) 0 -
     sphereRotatedOrbital n g a.val.2 R 0 * deriv (fun t : ℝ => sphereRotatedOrbital n g a.val.1 R (t*d)) 0)

theorem sphereRotatedContact_eq_inner (n : ℕ) (R : ℝ) (g : SourceSU2) (d : ℂ) (x : PairSpace (n+2)) :
    sphereRotatedContact n R g d x =
      sphereChartContact (n+1) 0 1 R d * inner ℂ (sphereOrbitPair n g) x := by
  have col (j : Fin 2) (i : Fin (n+2)) : sphereSpinFrame n g (PiLp.single 2 j 1) i =
      sourceSpinRepresentation (n+1) g i (Fin.castLE (by omega) j) := by
    change ((sphereSpinColumns n g) *ᵥ (Pi.single j (1:ℂ))) i = _
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, sphereSpinColumns]
  have h0 : sphereChartOrbital (n+1) 1 R 0 = 0 := by simp [sphereChartOrbital_origin]
  rw [sphereRotatedContact, PiLp.inner_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [sphereRotated_origin,sphereRotated_jet,sphereChartContact,h0,zero_mul,sub_zero,
    sphereOrbitPair, wedgePair, WithLp.ofLp_toLp, RCLike.inner_apply, map_sub, map_mul]
  simp only [col, show Fin.castLE (by omega : 2 ≤ n+2) (0:Fin 2) = 0 from rfl,
    show Fin.castLE (by omega : 2 ≤ n+2) (1:Fin 2) = 1 from rfl,
    (sphereChartOrbital_jet (n+1) 1 R d).deriv]
  ring

/-- Area times the finite-flux contact coefficient, using normalized rotation measure. -/
def sphereContactAreaFactor (n : ℕ) (R : ℝ) : ℝ :=
  (4*Real.pi*R^2)*(8*Real.pi*R^4*(2*(n:ℝ)+1)/(((n:ℝ)+1)*((n:ℝ)+2)^2))

theorem sphereRotatedContact_density (n : ℕ) (R : ℝ) (hR : 0 < R) (g : SourceSU2) (x : PairSpace (n+2)) :
    sphereContactAreaFactor n R *
      (‖sphereRotatedContact n R g 1 x‖^2 + ‖sphereRotatedContact n R g Complex.I x‖^2) =
      (2*(n:ℝ)+1)*‖inner ℂ (sphereOrbitPair n g) x‖^2 := by
  simp only [sphereRotatedContact_eq_inner, norm_mul, mul_pow, ← add_mul]
  rw [sphereContactAreaFactor, ← mul_assoc, mul_assoc (4*Real.pi*R^2),
    sphereChartContact_normalized n R hR]
  field_simp [Real.pi_ne_zero, hR.ne']

/-- Integrated derivative contact equals the normalized pair projector on every exterior vector. -/
theorem sphereRotatedContact_energy (n : ℕ) (R : ℝ) (hR : 0 < R) (x : PairSpace (n+2)) :
    (∫ g, sphereContactAreaFactor n R *
      (‖sphereRotatedContact n R g 1 x‖^2 + ‖sphereRotatedContact n R g Complex.I x‖^2) ∂sourceHaar) =
      (inner ℂ x ((spherePairSector n).starProjection x)).re := by
  simp_rw [sphereRotatedContact_density n R hR]
  rw [integral_const_mul]
  let p := sphereOrbitPair n
  have hp : MemLp p 2 sourceHaar := (sphereOrbitPair_continuous n).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have h := VortexGap.Frame.operatorAnalysis_norm_sq sourceHaar (fun g => innerSL ℂ (p g))
    (pairInner_memLp sourceHaar p hp) x
  change ‖continuousPairAnalysis sourceHaar p hp x‖^2 = ∫ g, ‖inner ℂ (p g) x‖^2 ∂sourceHaar at h
  rw [continuousPairAnalysis_energy] at h
  have he := congrArg (fun v => (inner ℂ x v).re) (DFunLike.congr_fun (spherePair_projector n) x)
  change (inner ℂ x (((2*n:ℕ)+1:ℂ) • continuousPairOperator sourceHaar p x)).re = _ at he
  rw [inner_smul_right, show ((2*n:ℕ)+1:ℂ) = (((2*(n:ℝ)+1):ℝ):ℂ) by push_cast; rfl,
    Complex.re_ofReal_mul, h] at he
  exact he

private theorem sphereRotated_diff (n : ℕ) (R : ℝ) (g : SourceSU2) (i : Fin (n+2)) (d : ℂ) :
    DifferentiableAt ℝ (fun t : ℝ => sphereRotatedOrbital n g i R (t*d)) 0 :=
  (HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin (n+2))))
    (fun j _ => (sphereChartOrbital_jet (n+1) j.val R d).const_mul
      (sourceSpinRepresentation (n+1) g⁻¹ j i))).differentiableAt

/-- Covariant first derivative in one gauge, along a tangent line through the chart origin. -/
def sphereCovariantJet (A : ℂ) (u : ℝ → ℂ) := deriv u 0 + A*u 0

/-- The derivatives of the multiplier and the local connection both cancel at coincidence. -/
theorem sphereContact_product_rule (f u v : ℝ → ℂ) (A : ℂ)
    (hf : DifferentiableAt ℝ f 0) (hu : DifferentiableAt ℝ u 0) (hv : DifferentiableAt ℝ v 0) :
    (f 0*u 0)*sphereCovariantJet A (fun t => f t*v t) -
      (f 0*v 0)*sphereCovariantJet A (fun t => f t*u t) =
    f 0^2 * (u 0*deriv v 0 - v 0*deriv u 0) := by
  simp only [sphereCovariantJet, (hf.hasDerivAt.fun_mul hu.hasDerivAt).deriv,
    (hf.hasDerivAt.fun_mul hv.hasDerivAt).deriv]
  ring

def sphereMultipliedContact (n : ℕ) (R : ℝ) (g : SourceSU2) (d A : ℂ) (f : ℝ → ℂ)
    (x : PairSpace (n+2)) : ℂ :=
  let u := fun (i : Fin (n+2)) (t : ℝ) => sphereRotatedOrbital n g i R (t*d)
  ∑ a : PairIndex (n+2), x a * ((f 0*u a.val.1 0)*sphereCovariantJet A (fun t => f t*u a.val.2 t) -
    (f 0*u a.val.2 0)*sphereCovariantJet A (fun t => f t*u a.val.1 t))

theorem sphereMultipliedContact_eq (n : ℕ) (R : ℝ) (g : SourceSU2) (d A : ℂ)
    (f : ℝ → ℂ) (hf : DifferentiableAt ℝ f 0) (x : PairSpace (n+2)) :
    sphereMultipliedContact n R g d A f x = f 0^2 * sphereRotatedContact n R g d x := by
  simp only [sphereMultipliedContact, sphereRotatedContact, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [sphereContact_product_rule _ _ _ _ hf (sphereRotated_diff ..) (sphereRotated_diff ..)]
  simp only [Complex.ofReal_zero, zero_mul]
  ring

/-- Pointwise physical density for two tangent paths of a scalar multiplier at the same point. -/
theorem sphereMultipliedContact_density (n : ℕ) (R : ℝ) (hR : 0 < R) (g : SourceSU2)
    (A B : ℂ) (f₁ f₂ : ℝ → ℂ) (h₁ : DifferentiableAt ℝ f₁ 0) (h₂ : DifferentiableAt ℝ f₂ 0)
    (hval : f₂ 0 = f₁ 0) (x : PairSpace (n+2)) :
    sphereContactAreaFactor n R *
      (‖sphereMultipliedContact n R g 1 A f₁ x‖^2 +
       ‖sphereMultipliedContact n R g Complex.I B f₂ x‖^2) =
      ‖f₁ 0‖^4 * ((2*(n:ℝ)+1)*‖inner ℂ (sphereOrbitPair n g) x‖^2) := by
  rw [sphereMultipliedContact_eq _ _ _ _ _ _ h₁, sphereMultipliedContact_eq _ _ _ _ _ _ h₂, hval,
    ← sphereRotatedContact_density n R hR g x]
  simp only [norm_mul, norm_pow]
  ring

end VortexGap.Fermion

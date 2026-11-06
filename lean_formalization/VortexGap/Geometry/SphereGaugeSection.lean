import VortexGap.Physical.SphereWaveEvaluation

noncomputable section
namespace VortexGap.Fermion
open OAI.Laughlin.Rotation
open scoped ComplexConjugate Matrix
variable {q N : ℕ}

def sphereFiberInvariant (f : SourceSU2 → ℂ) : Prop :=
  ∀ g z (hz : ‖z‖=1), f (g * sourceTorus z hz) = f g

theorem sphereOrbitalValue_gauge (q : ℕ) (x : Fin (q+1) → ℂ) (g : SourceSU2)
    (z : ℂ) (hz : ‖z‖=1) :
    sphereOrbitalValue q x (g * sourceTorus z hz) = (conj z)^q * sphereOrbitalValue q x g := by
  simp only [sphereOrbitalValue,map_mul,sourceSpinRepresentation_torus,Matrix.mul_diagonal,
    Fin.val_zero,pow_zero,Nat.sub_zero,one_mul,map_pow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem sphereAxial_fiberInvariant : sphereFiberInvariant sphereAxialMultiplier := by
  intro g z hz
  have h : (g * sourceTorus z hz).val 0 0 = g.val 0 0 * z := by
    change (g.val * Matrix.diagonal (fun i : Fin 2 => if i=0 then z else star z)) 0 0 = _
    simp [Matrix.mul_diagonal]
  simp [sphereAxialMultiplier,h,hz]

private theorem wave_gauge (u : SourceSU2 → Fin (q+1) → ℂ)
    (hu : ∀ g z (hz : ‖z‖=1) i, u (g * sourceTorus z hz) i = (conj z)^q * u g i)
    (x : particleSector (q+1) N) (g : Fin N → SourceSU2) (z : Fin N → ℂ) (hz : ∀ i, ‖z i‖=1) :
    sectorWave u x (fun i => g i * sourceTorus (z i) (hz i)) =
      (∏ i, (conj (z i))^q) * sectorWave u x g := by
  simp only [sectorWave,hu,Finset.prod_mul_distrib,Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => mul_left_comm _ _ _

theorem sphereReferenceWave_gauge (x : particleSector (q+1) N) (g : Fin N → SourceSU2)
    (z : Fin N → ℂ) (hz : ∀ i, ‖z i‖=1) :
    sphereReferenceWave x (fun i => g i * sourceTorus (z i) (hz i)) =
      (∏ i, (conj (z i))^q) * sphereReferenceWave x g :=
  wave_gauge _ (fun g z hz _ => sphereOrbitalValue_gauge q _ g z hz) x g z hz

theorem sphereDeformedWave_gauge (f : SourceSU2 → ℂ) (hf : Continuous f) (hi : sphereFiberInvariant f)
    (x : particleSector (q+1) N) (g : Fin N → SourceSU2) (z : Fin N → ℂ) (hz : ∀ i, ‖z i‖=1) :
    sphereDeformedWave f hf x (fun i => g i * sourceTorus (z i) (hz i)) =
      (∏ i, (conj (z i))^q) * sphereDeformedWave f hf x g := by
  apply wave_gauge (sphereFilteredValue q f hf) _ x g z hz
  intro k w hw i
  simp only [sphereFilteredValue,sphereScalarRow_apply,hi k w hw,sphereOrbitalValue_gauge q _ k w hw]
  ring

/-- Configurations modulo independent choices of phase at the N particles. -/
def spherePhaseRelation (g h : Fin N → SourceSU2) : Prop :=
  ∃ z : Fin N → ℂ, ∃ hz : ∀ i, ‖z i‖=1, h = fun i => g i * sourceTorus (z i) (hz i)

abbrev spherePhaseQuotient (N : ℕ) := Quot (@spherePhaseRelation N)

def sphereQuotientDensity (f : SourceSU2 → ℂ) (hf : Continuous f) (hi : sphereFiberInvariant f)
    (x : particleSector (q+1) N) : spherePhaseQuotient N → ℝ :=
  Quot.lift (fun g => ‖sphereDeformedWave f hf x g‖^2) (by
    rintro g _ ⟨z,hz,rfl⟩
    rw [sphereDeformedWave_gauge f hf hi x g z hz,norm_mul,norm_prod]
    simp [norm_pow,hz])

theorem sphereAxial_density_on_quotient (x : particleSector (q+1) N) (g : Fin N → SourceSU2) :
    sphereQuotientDensity sphereAxialMultiplier sphereAxialMultiplier_continuous
      sphereAxial_fiberInvariant x (Quot.mk _ g) =
      ‖sphereDeformedWave sphereAxialMultiplier sphereAxialMultiplier_continuous x g‖^2 := rfl

end VortexGap.Fermion
end

noncomputable section
namespace VortexGap.Fermion
open OAI.Laughlin.Rotation VortexGap.SpherePolynomial
open scoped ComplexConjugate Matrix
variable {q N : ℕ}
private abbrev Config (N : ℕ) := Fin N → SourceSU2

def sphereAmplitudeRelation (q : ℕ) (x y : Config N × ℂ) : Prop :=
  ∃ z : Fin N → ℂ, ∃ hz : ∀ i, ‖z i‖=1,
    y.1 = (fun i => x.1 i * sourceTorus (z i) (hz i)) ∧ y.2 = (∏ i, (conj (z i))^q) * x.2

abbrev sphereAmplitudeOrbit (q N : ℕ) := Quot (@sphereAmplitudeRelation N q)

def sphereAmplitudeBase : sphereAmplitudeOrbit q N → spherePhaseQuotient N :=
  Quot.lift (fun x => Quot.mk _ x.1) (by
    rintro x y ⟨z,hz,hg,_⟩
    exact Quot.sound ⟨z,hz,hg⟩)

def sphereAmplitudeScale (c : ℂ) : sphereAmplitudeOrbit q N → sphereAmplitudeOrbit q N :=
  Quot.lift (fun x => Quot.mk _ (x.1,c*x.2)) (by
    rintro x y ⟨z,hz,hg,hy⟩
    exact Quot.sound ⟨z,hz,hg,by simp only [hy]; ring⟩)

def sphereOrbitSection (q : ℕ) (w : Config N → ℂ)
    (hw : ∀ (g : Config N) (z : Fin N → ℂ) (hz : ∀ i, ‖z i‖=1), w (fun i => g i * sourceTorus (z i) (hz i)) =
      (∏ i, (conj (z i))^q) * w g) : spherePhaseQuotient N → sphereAmplitudeOrbit q N :=
  Quot.lift (fun g => Quot.mk _ (g,w g)) (by
    rintro g _ ⟨z,hz,rfl⟩
    exact Quot.sound ⟨z,hz,rfl,hw g z hz⟩)

theorem sphereOrbitSection_base (q : ℕ) (w : Config N → ℂ) (hw) (p : spherePhaseQuotient N) :
    sphereAmplitudeBase (sphereOrbitSection q w hw p) = p := by
  induction p using Quot.ind with | _ g => rfl

def sphereProductScalar (f : SourceSU2 → ℂ) (hi : sphereFiberInvariant f) :
    spherePhaseQuotient N → ℂ :=
  Quot.lift (fun g => ∏ i, f (g i)) (by rintro g _ ⟨z,hz,rfl⟩; exact Finset.prod_congr rfl fun i _ => (hi _ _ (hz i)).symm)

theorem sphere_laughlin_product_section (n N : ℕ) (hQ : 3*((N+2)-1) = n+1)
    (f : SourceSU2 → ℂ) (hf : Continuous f) (hi : sphereFiberInvariant f) (a b : ℝ)
    (ha : 0<a) (hl : ∀ g, a ≤ ‖f g‖^2) (hu : ∀ g, ‖f g‖^2 ≤ b) :
    ∃ l y : particleSector (n+2) (N+2), sectorPoly l = laughlin (N+2) ∧
      LinearMap.ker (sphereSectorHam n (N+2) (spherePhysicalPair n f hf)).toLinearMap = ℂ ∙ y ∧
      ∀ p : spherePhaseQuotient (N+2),
        sphereOrbitSection (n+1) _ (sphereDeformedWave_gauge f hf hi y) p =
          sphereAmplitudeScale (sphereProductScalar f hi p)
            (sphereOrbitSection (n+1) _ (sphereReferenceWave_gauge l) p) := by
  obtain ⟨l,y,hlp,hk,hp⟩ := sphere_laughlin_product_generator n N hQ f hf a b ha hl hu
  refine ⟨l,y,hlp,hk,?_⟩
  intro p
  induction p using Quot.ind with
  | _ g =>
    change Quot.mk _ (g,sphereDeformedWave f hf y g) =
      Quot.mk _ (g,(∏ i, f (g i)) * sphereReferenceWave l g)
    rw [hp]

/-- Read a class in the frame g. On its own fiber this recovers the
complex coefficient, so equality of classes preserves phase information. -/
def sphereFrameReadout (g : Config N) (q : ℕ) : sphereAmplitudeOrbit q N → ℂ :=
  Quot.lift (fun x => (∏ i, ((g i)⁻¹ * x.1 i).val 0 0 ^ q) * x.2) (by
    rintro ⟨h,v⟩ ⟨_,_⟩ ⟨z,hz,rfl,rfl⟩
    have ent (i : Fin N) : ((g i)⁻¹ * (h i * sourceTorus (z i) (hz i))).val 0 0 =
        ((g i)⁻¹ * h i).val 0 0 * z i := by
      rw [← mul_assoc]
      change (((g i)⁻¹*h i).val * Matrix.diagonal (fun k : Fin 2 => if k=0 then z i else star (z i))) 0 0 = _
      simp [Matrix.mul_diagonal]
    dsimp only
    simp_rw [ent,mul_pow]
    rw [Finset.prod_mul_distrib]
    have hz1 : (∏ i, (z i)^q) * (∏ i, (conj (z i))^q) = 1 := by
      rw [← Finset.prod_mul_distrib]
      simp only [← mul_pow,Complex.mul_conj',hz,Complex.ofReal_one,one_pow,Finset.prod_const_one]
    linear_combination -(∏ i, ((g i)⁻¹*h i).val 0 0 ^ q) * v * hz1)

theorem sphereAmplitude_fixed_lift_injective (g : Config N) :
    Function.Injective (fun v : ℂ => (Quot.mk _ (g,v) : sphereAmplitudeOrbit q N)) := by
  intro u v h
  have he := congrArg (sphereFrameReadout g q) h
  simpa [sphereFrameReadout] using he

end VortexGap.Fermion
end

import SMSFormula.RationalCliffordGeneralSpinHorizontalIntegralCentralFiber

/-!
# The normalized central-unit fiber on the complete horizontal good tail

The local compact central fibers assemble into an infinite product probability
measure on the integral `GSpin` tail.  Pointwise central translation gives a
measurable source-indexed kernel.  Its value at a tail point is the infinite
product of the local fiber kernels, and averaging it against normalized
integral `GSpin` Haar leaves that Haar measure unchanged.

For a lattice whose retained coordinates avoid the two explicit lifting bad
sets, this source kernel is constant on fibers of the complete tail projection
to integral `SO`.  The second half of this file descends it measurably and
proves the normalized infinite-tail Weil identity.  No product section of the
central extension is selected.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory
open Filter MeasurableSpace
open scoped ENNReal ProbabilityTheory Uniformity

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

local instance horizontalIntegralCentralFiberTailPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance horizontalIntegralCentralFiberTailDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance horizontalIntegralCentralFiberTailGroupMeasurableSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicCliffordGeneralSpinGroup v) :=
  borel _

local instance horizontalIntegralCentralFiberTailGroupBorelSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicCliffordGeneralSpinGroup v) :=
  ⟨rfl⟩

local instance horizontalIntegralCentralFiberTailMeasurableMul₂
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    MeasurableMul₂
      (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  ⟨by
    apply Measurable.subtype_mk
    exact measurable_mul.comp
      ((measurable_subtype_coe.comp measurable_fst).prodMk
        (measurable_subtype_coe.comp measurable_snd))⟩

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 3000000

/-! ## The product central measure and source-indexed kernel -/

/-- The product of the literal normalized scalar-unit fibers on every
unchanged horizontal good coordinate. -/
def cliffordGeneralSpinHorizontalIntegralCentralFiberTailMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.CliffordGeneralSpinHorizontalIntegralTail S) :=
  Measure.infinitePi fun
      v : V.CliffordGeneralSpinHorizontalIntegralPlace S ↦
    V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasure S v

instance
    cliffordGeneralSpinHorizontalIntegralCentralFiberTailMeasure_isProbability
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    IsProbabilityMeasure
      (V.cliffordGeneralSpinHorizontalIntegralCentralFiberTailMeasure S) := by
  letI (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
      IsProbabilityMeasure
        (V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasure S v) :=
    V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasure_isProbability S v
  unfold cliffordGeneralSpinHorizontalIntegralCentralFiberTailMeasure
  infer_instance

/-- Every finite-coordinate marginal of the central-tail measure is the
finite product of the corresponding literal local central fibers. -/
theorem
    cliffordGeneralSpinHorizontalIntegralCentralFiberTailMeasure_map_restrict
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (T : Finset (V.CliffordGeneralSpinHorizontalIntegralPlace S)) :
    (V.cliffordGeneralSpinHorizontalIntegralCentralFiberTailMeasure S).map
        T.restrict =
      Measure.pi fun v : {v // v ∈ T} ↦
        V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasure S v.1 := by
  letI (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
      IsProbabilityMeasure
        (V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasure S v) :=
    V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasure_isProbability S v
  simpa only [cliffordGeneralSpinHorizontalIntegralCentralFiberTailMeasure] using
    (Measure.infinitePi_map_restrict
      (μ := fun v : V.CliffordGeneralSpinHorizontalIntegralPlace S ↦
        V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasure S v)
      (I := T))

/-- Pointwise central multiplication, with the origin in the first product
coordinate to match the product-kernel convention. -/
def cliffordGeneralSpinHorizontalIntegralCentralFiberTailJointOrbit
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.CliffordGeneralSpinHorizontalIntegralTail S ×
        V.CliffordGeneralSpinHorizontalIntegralTail S →
      V.CliffordGeneralSpinHorizontalIntegralTail S :=
  fun p v ↦ p.2 v * p.1 v

theorem measurable_cliffordGeneralSpinHorizontalIntegralCentralFiberTailJointOrbit
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measurable
      (V.cliffordGeneralSpinHorizontalIntegralCentralFiberTailJointOrbit S) := by
  exact measurable_pi_lambda _ fun v ↦
    measurable_mul.comp
      (((measurable_pi_apply v).comp measurable_snd).prodMk
        ((measurable_pi_apply v).comp measurable_fst))

/-- The complete source-indexed central-fiber kernel on the normalized good
`GSpin` tail. -/
def cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernel
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    ProbabilityTheory.Kernel
      (V.CliffordGeneralSpinHorizontalIntegralTail S)
      (V.CliffordGeneralSpinHorizontalIntegralTail S) :=
  ProbabilityTheory.Kernel.map
    (ProbabilityTheory.Kernel.id ×ₖ
      ProbabilityTheory.Kernel.const
        (V.CliffordGeneralSpinHorizontalIntegralTail S)
        (V.cliffordGeneralSpinHorizontalIntegralCentralFiberTailMeasure S))
    (V.cliffordGeneralSpinHorizontalIntegralCentralFiberTailJointOrbit S)

@[simp]
theorem cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernel_apply
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.CliffordGeneralSpinHorizontalIntegralTail S) :
    V.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernel S g =
      Measure.map (fun z ↦ z * g)
        (V.cliffordGeneralSpinHorizontalIntegralCentralFiberTailMeasure S) := by
  ext A hA
  rw [cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernel,
    ProbabilityTheory.Kernel.map_apply'
      _
      (V.measurable_cliffordGeneralSpinHorizontalIntegralCentralFiberTailJointOrbit S)
      _ hA,
    ProbabilityTheory.Kernel.id_prod_apply' _ g
      (V.measurable_cliffordGeneralSpinHorizontalIntegralCentralFiberTailJointOrbit S hA),
    ProbabilityTheory.Kernel.const_apply,
    Measure.map_apply (measurable_mul_const g) hA]
  rfl

/-- A source fiber is literally the infinite product of its completed local
central-unit fibers. -/
theorem
    cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernel_apply_eq_infinitePi
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.CliffordGeneralSpinHorizontalIntegralTail S) :
    V.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernel S g =
      Measure.infinitePi fun
          v : V.CliffordGeneralSpinHorizontalIntegralPlace S ↦
        V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberKernel S v
          (g v) := by
  letI (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
      IsProbabilityMeasure
        (V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasure S v) :=
    V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasure_isProbability S v
  rw [V.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernel_apply,
    cliffordGeneralSpinHorizontalIntegralCentralFiberTailMeasure]
  change
    Measure.map (fun z v ↦ z v * g v)
        (Measure.infinitePi fun v : V.CliffordGeneralSpinHorizontalIntegralPlace S ↦
          V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasure S v) = _
  rw [Measure.infinitePi_map_pi
    (μ := fun v : V.CliffordGeneralSpinHorizontalIntegralPlace S ↦
      V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasure S v)
    (f := fun v z ↦ z * g v)
    (fun v ↦ measurable_mul_const (g v))]
  congr 1
  funext v
  exact
    (V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberKernel_apply
      S v (g v)).symm

/-- Averaging normalized horizontal good-tail Haar along the complete central
tail leaves that Haar measure unchanged. -/
theorem
    cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernel_comp_normalizedHaar
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernel S ∘ₘ
        V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S =
      V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S := by
  let muG := V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S
  let muZ := V.cliffordGeneralSpinHorizontalIntegralCentralFiberTailMeasure S
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_bind
    (V.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernel S).aemeasurable
    hf.aemeasurable]
  simp_rw [V.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernel_apply S]
  simp_rw [lintegral_map hf (measurable_mul_const _)]
  calc
    ∫⁻ g, ∫⁻ z, f (z * g) ∂muZ ∂muG =
        ∫⁻ z, ∫⁻ g, f (z * g) ∂muG ∂muZ := by
      exact lintegral_lintegral_swap
        (hf.comp
          (V.measurable_cliffordGeneralSpinHorizontalIntegralCentralFiberTailJointOrbit
            S)).aemeasurable
    _ = ∫⁻ z, ∫⁻ g, f g ∂muG ∂muZ := by
      apply lintegral_congr
      intro z
      exact lintegral_mul_left_eq_self f z
    _ = ∫⁻ g, f g ∂muG := by
      simp [muZ]

/-- Each local descended central-fiber kernel is Markov: every fiber carries
the transported probability Haar of the scalar-unit kernel. -/
instance
    padicCliffordGeneralSpinHorizontalIntegralCentralFiberKernelAtSO_isMarkov
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S)
    (hsurj : Function.Surjective
      (V.padicCliffordGeneralSpinHorizontalIntegralToSO S v)) :
    ProbabilityTheory.IsMarkovKernel
      (V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberKernelAtSO
        S v hsurj) := by
  constructor
  intro q
  change IsProbabilityMeasure
    (V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasureAtSO
      S v hsurj q)
  unfold padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasureAtSO
  rw [V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberKernel_apply]
  exact Measure.isProbabilityMeasure_map
    (measurable_mul_const _).aemeasurable

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

local instance horizontalIntegralCentralFiberTailLatticePrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance horizontalIntegralCentralFiberTailLatticeDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

noncomputable local instance
    horizontalIntegralCentralFiberTailLatticeSOMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalGroup v) :=
  L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalGroupMeasurableSpace_spinorNorm
    (Rat.HeightOneSpectrum.primesEquiv v).1

noncomputable local instance
    horizontalIntegralCentralFiberTailLatticeSOBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalGroup v) :=
  L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalGroupBorelSpace_spinorNorm
    (Rat.HeightOneSpectrum.primesEquiv v).1

noncomputable local instance
    horizontalIntegralCentralFiberTailLatticeSOSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalGroup v) :=
  L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalGroupSecondCountable_spinorNorm
    (Rat.HeightOneSpectrum.primesEquiv v).1

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 3000000

/-! ## Lattice good-tail descent -/

/-- The complete componentwise projection of the normalized integral `GSpin`
tail is surjective when every retained coordinate avoids the two constructive
lifting bad sets. -/
theorem cliffordGeneralSpinHorizontalIntegralTailToSO_surjective
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hvAdmissible : ∀
      v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace S,
      v.1 ∉
        L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateAdmissibleExceptionalPlaces ∅)
    (hvOdd : ∀
      v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace S,
      v.1 ∉
        L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces) :
    Function.Surjective
      (L.cliffordGeneralSpinHorizontalIntegralTailToSO S) := by
  intro q
  refine ⟨fun v ↦
    L.rationalQuadraticSpaceMatrix.padicCliffordGeneralSpinHorizontalIntegralCentralFiberLift
      S v
      (L.padicCliffordGeneralSpinHorizontalIntegralToSO_surjective
        S v (hvAdmissible v) (hvOdd v)) (q v), ?_⟩
  funext v
  exact
    L.rationalQuadraticSpaceMatrix.padicCliffordGeneralSpinHorizontalIntegralCentralFiberLift_spec
      S v
      (L.padicCliffordGeneralSpinHorizontalIntegralToSO_surjective
        S v (hvAdmissible v) (hvOdd v)) (q v)

/-- The complete source-indexed central kernel depends only on the integral
`SO` tail image of its origin. -/
theorem
    cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernel_eq_of_sameSO
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    {g w : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralTail S}
    (hgw : L.cliffordGeneralSpinHorizontalIntegralTailToSO S w =
      L.cliffordGeneralSpinHorizontalIntegralTailToSO S g) :
    L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernel
        S w =
      L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernel
        S g := by
  let V := L.rationalQuadraticSpaceMatrix
  rw [V.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernel_apply_eq_infinitePi,
    V.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernel_apply_eq_infinitePi]
  congr 1
  funext v
  exact V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberKernel_eq_of_sameSO
    S v (congrFun hgw v)

/-- A chosen complete integral `GSpin` tail origin over an integral `SO` tail
point, used only to define the representative-independent descended measure. -/
def cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hvAdmissible : ∀
      v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace S,
      v.1 ∉
        L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateAdmissibleExceptionalPlaces ∅)
    (hvOdd : ∀
      v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace S,
      v.1 ∉
        L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces)
    (q : L.rationalQuadraticSpaceMatrix.FiniteAdelicSpecialOrthogonalIntegralTail
      (S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralTail S :=
  Classical.choose
    (L.cliffordGeneralSpinHorizontalIntegralTailToSO_surjective
      S hvAdmissible hvOdd q)

@[simp]
theorem cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift_spec
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hvAdmissible : ∀
      v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace S,
      v.1 ∉
        L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateAdmissibleExceptionalPlaces ∅)
    (hvOdd : ∀
      v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace S,
      v.1 ∉
        L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces)
    (q : L.rationalQuadraticSpaceMatrix.FiniteAdelicSpecialOrthogonalIntegralTail
      (S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    L.cliffordGeneralSpinHorizontalIntegralTailToSO S
        (L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift
          S hvAdmissible hvOdd q) = q :=
  Classical.choose_spec
    (L.cliffordGeneralSpinHorizontalIntegralTailToSO_surjective
      S hvAdmissible hvOdd q)

/-- The representative-independent complete central-fiber measure indexed by
the normalized integral `SO` tail. -/
def cliffordGeneralSpinHorizontalIntegralCentralFiberTailMeasureAtSO
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hvAdmissible : ∀
      v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace S,
      v.1 ∉
        L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateAdmissibleExceptionalPlaces ∅)
    (hvOdd : ∀
      v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace S,
      v.1 ∉
        L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces)
    (q : L.rationalQuadraticSpaceMatrix.FiniteAdelicSpecialOrthogonalIntegralTail
      (S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    Measure
      (L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralTail S) :=
  L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernel
    S (L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift
      S hvAdmissible hvOdd q)

theorem
    cliffordGeneralSpinHorizontalIntegralCentralFiberTailMeasureAtSO_image
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hvAdmissible : ∀
      v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace S,
      v.1 ∉
        L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateAdmissibleExceptionalPlaces ∅)
    (hvOdd : ∀
      v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace S,
      v.1 ∉
        L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces)
    (g : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralTail S) :
    L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailMeasureAtSO
        S hvAdmissible hvOdd
          (L.cliffordGeneralSpinHorizontalIntegralTailToSO S g) =
      L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernel
        S g := by
  unfold cliffordGeneralSpinHorizontalIntegralCentralFiberTailMeasureAtSO
  exact
    L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernel_eq_of_sameSO
      S
      (L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift_spec
        S hvAdmissible hvOdd _)

/-- The representative-independent complete central-fiber family is
measurable on the normalized integral `SO` tail. -/
theorem
    measurable_cliffordGeneralSpinHorizontalIntegralCentralFiberTailMeasureAtSO
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hvAdmissible : ∀
      v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace S,
      v.1 ∉
        L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateAdmissibleExceptionalPlaces ∅)
    (hvOdd : ∀
      v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace S,
      v.1 ∉
        L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces) :
    Measurable
      (L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailMeasureAtSO
        S hvAdmissible hvOdd) := by
  let V := L.rationalQuadraticSpaceMatrix
  let pi := L.cliffordGeneralSpinHorizontalIntegralTailToSO S
  let hsurj :=
    L.cliffordGeneralSpinHorizontalIntegralTailToSO_surjective
      S hvAdmissible hvOdd
  letI (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
      PolishSpace (V.HeightOnePadicCliffordGeneralSpinGroup v.1) :=
    V.padicCliffordGeneralSpinHorizontalPolishSpace v.1
  letI (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
      PolishSpace (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
    (V.isCompact_padicCliffordGeneralSpinHorizontalIntegralSubgroup S v
      ).isClosed.polishSpace
  letI : StandardBorelSpace
      (V.CliffordGeneralSpinHorizontalIntegralTail S) := by
    infer_instance
  letI (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
      SecondCountableTopology
        (V.HeightOnePadicSpecialOrthogonalIntegralGroup v.1) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  letI (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
      BorelSpace
        (V.HeightOnePadicSpecialOrthogonalIntegralGroup v.1) :=
    Subtype.borelSpace _
  letI (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
      CountablySeparated
        (V.HeightOnePadicSpecialOrthogonalIntegralGroup v.1) := by
    infer_instance
  letI : SecondCountableTopology
      (V.FiniteAdelicSpecialOrthogonalIntegralTail
        (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  letI : BorelSpace
      (V.FiniteAdelicSpecialOrthogonalIntegralTail
        (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :=
    Pi.borelSpace
  letI : CountablySeparated
      (V.FiniteAdelicSpecialOrthogonalIntegralTail
        (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)) := by
    letI : CountablyGenerated
        (V.FiniteAdelicSpecialOrthogonalIntegralTail
          (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :=
      BorelSpace.countablyGenerated
    letI : SeparatesPoints
        (V.FiniteAdelicSpecialOrthogonalIntegralTail
          (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)) := by
      infer_instance
    exact countablySeparated_of_separatesPoints
  apply
    ((L.measurable_cliffordGeneralSpinHorizontalIntegralTailToSO S
      ).measurable_comp_iff_of_surjective hsurj).mp
  have hmeas : Measurable
      (fun g ↦
        V.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernel S g) :=
    (V.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernel S).measurable
  change Measurable (fun g ↦
    L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailMeasureAtSO
      S hvAdmissible hvOdd (pi g))
  rw [show
    (fun g ↦
      L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailMeasureAtSO
        S hvAdmissible hvOdd (pi g)) =
      (fun g ↦
        V.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernel S g) by
      funext g
      exact
        L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailMeasureAtSO_image
          S hvAdmissible hvOdd g]
  exact hmeas

/-- The genuine normalized integral-`SO`-tail-indexed central-fiber kernel. -/
def cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernelAtSO
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hvAdmissible : ∀
      v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace S,
      v.1 ∉
        L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateAdmissibleExceptionalPlaces ∅)
    (hvOdd : ∀
      v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace S,
      v.1 ∉
        L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces) :
    ProbabilityTheory.Kernel
      (L.rationalQuadraticSpaceMatrix.FiniteAdelicSpecialOrthogonalIntegralTail
        (S ∪
          L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces))
      (L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralTail S) :=
  ⟨L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailMeasureAtSO
      S hvAdmissible hvOdd,
    L.measurable_cliffordGeneralSpinHorizontalIntegralCentralFiberTailMeasureAtSO
      S hvAdmissible hvOdd⟩

@[simp]
theorem
    cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernelAtSO_comp_projection
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hvAdmissible : ∀
      v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace S,
      v.1 ∉
        L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateAdmissibleExceptionalPlaces ∅)
    (hvOdd : ∀
      v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace S,
      v.1 ∉
        L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces)
    (g : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralTail S) :
    L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernelAtSO
        S hvAdmissible hvOdd
          (L.cliffordGeneralSpinHorizontalIntegralTailToSO S g) =
      L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernel
        S g :=
  L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailMeasureAtSO_image
    S hvAdmissible hvOdd g

/-- Each descended good-tail fiber is literally the infinite product of the
already completed local `SO`-indexed central-unit fibers. -/
theorem
    cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernelAtSO_apply_eq_infinitePi
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hvAdmissible : ∀
      v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace S,
      v.1 ∉
        L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateAdmissibleExceptionalPlaces ∅)
    (hvOdd : ∀
      v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace S,
      v.1 ∉
        L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces)
    (q : L.rationalQuadraticSpaceMatrix.FiniteAdelicSpecialOrthogonalIntegralTail
      (S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernelAtSO
        S hvAdmissible hvOdd q =
      Measure.infinitePi fun
          v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace S ↦
        L.rationalQuadraticSpaceMatrix.padicCliffordGeneralSpinHorizontalIntegralCentralFiberKernelAtSO
          S v
            (L.padicCliffordGeneralSpinHorizontalIntegralToSO_surjective
              S v (hvAdmissible v) (hvOdd v)) (q v) := by
  let V := L.rationalQuadraticSpaceMatrix
  let g := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift
    S hvAdmissible hvOdd q
  change
    V.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernel S g = _
  rw [V.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernel_apply_eq_infinitePi]
  congr 1
  funext v
  have hq := congrFun
    (L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift_spec
      S hvAdmissible hvOdd q) v
  change
    V.padicCliffordGeneralSpinHorizontalIntegralToSO S v (g v) = q v at hq
  rw [← hq]
  exact
    (V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberKernelAtSO_comp_projection
      S v
        (L.padicCliffordGeneralSpinHorizontalIntegralToSO_surjective
          S v (hvAdmissible v) (hvOdd v)) (g v)).symm

instance cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernelAtSO_isMarkov
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hvAdmissible : ∀
      v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace S,
      v.1 ∉
        L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateAdmissibleExceptionalPlaces ∅)
    (hvOdd : ∀
      v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace S,
      v.1 ∉
        L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces) :
    ProbabilityTheory.IsMarkovKernel
      (L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernelAtSO
        S hvAdmissible hvOdd) := by
  constructor
  intro q
  rw [L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernelAtSO_apply_eq_infinitePi
    S hvAdmissible hvOdd q]
  infer_instance

/-- The normalized infinite good-tail central-extension Weil identity. -/
theorem
    cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernelAtSO_comp_normalizedSO
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hvAdmissible : ∀
      v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace S,
      v.1 ∉
        L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateAdmissibleExceptionalPlaces ∅)
    (hvOdd : ∀
      v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace S,
      v.1 ∉
        L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces) :
    L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernelAtSO
        S hvAdmissible hvOdd ∘ₘ
      L.rationalQuadraticSpaceMatrix.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure
        (S ∪
          L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces) =
      L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure
        S := by
  let V := L.rationalQuadraticSpaceMatrix
  let pi := L.cliffordGeneralSpinHorizontalIntegralTailToSO S
  let muG := V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S
  let muSO := V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure
    (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)
  let kappa := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernelAtSO
    S hvAdmissible hvOdd
  have hmarginal : Measure.map pi muG = muSO :=
    L.map_cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure_toSO
      S hvAdmissible hvOdd
  change kappa ∘ₘ muSO = muG
  rw [← hmarginal]
  calc
    kappa ∘ₘ Measure.map pi muG =
        V.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernel S ∘ₘ muG := by
      ext t ht
      rw [Measure.bind_apply ht kappa.aemeasurable,
        Measure.bind_apply ht
          (V.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernel S).aemeasurable,
        lintegral_map (kappa.measurable_coe ht)
          (L.measurable_cliffordGeneralSpinHorizontalIntegralTailToSO S)]
      apply lintegral_congr
      intro g
      exact congrArg (fun mu : Measure _ ↦ mu t)
        (L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernelAtSO_comp_projection
          S hvAdmissible hvOdd g)
    _ = muG :=
      V.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernel_comp_normalizedHaar
        S

/-! ## A canonical retained exceptional enlargement -/

/-- Enlarge a retained exceptional set by exactly the two finite lattice bad
sets required by the constructive integral `GSpin -> SO` lift. -/
def cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Finset (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  (S ∪
    L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateAdmissibleExceptionalPlaces ∅) ∪
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces

theorem
    cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces S)) :
    v.1 ∉
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateAdmissibleExceptionalPlaces ∅ := by
  intro hv
  exact v.2 (by
    simp [cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces, hv])

theorem
    cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces S)) :
    v.1 ∉
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces := by
  intro hv
  exact v.2 (by
    simp [cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces, hv])

/-- The normalized infinite-tail Weil identity at the canonical enlargement,
with no residual good-place hypotheses. -/
theorem
    cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernelAtSO_comp_normalizedSO_canonical
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernelAtSO
        (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces S)
        (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible S)
        (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd S) ∘ₘ
      L.rationalQuadraticSpaceMatrix.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure
        (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces S ∪
          L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces) =
      L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure
        (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces S) :=
  L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernelAtSO_comp_normalizedSO
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces S)
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible S)
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd S)

end PositiveDefiniteIntegralLattice

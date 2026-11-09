import SMSFormula.RationalCliffordGeneralSpinLatticeIntegralSpinorRange
import SMSFormula.RationalCliffordGeneralSpinFiniteAdelicRestrictedFamily

/-!
# Cofinite integral general-Spin similitude lifts

This file records the finite Clifford-coordinate denominator condition used
to build integral intrinsic `GSpin` points.  The condition holds at cofinitely
many rational places because it mentions only finitely many rational
structure constants.  At an odd-unimodular place, an integral
special-orthogonal reflection word then gives a `GSpin` lift whose Clifford
unit and inverse have integral coordinates.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open QuadraticMap.ReflectionWord
open scoped Matrix RestrictedProduct

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

local instance integralGeneralSpinSimilitudePrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000

/-- The finite rational Clifford-coordinate denominator condition needed for
integral reflection-word products at one height-one place. -/
def CliffordGeneralSpinIntegralStructureAt
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) : Prop :=
  (∀ s t u : Finset (Fin n),
      algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
          (V.cliffordMulStructureConstant s t u) ∈
        PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1) ∧
  (∀ s u : Finset (Fin n),
      algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
          (V.cliffordReverseStructureConstant s u) ∈
        PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1) ∧
  (∀ i : Fin n, ∀ u : Finset (Fin n),
      algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
          (V.cliffordVectorBasisCoordinate i u) ∈
        PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1) ∧
  ∀ u : Finset (Fin n),
      algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
          (V.cliffordSpinOneCoordinate u) ∈
        PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1

private theorem eventually_rationalCliffordConstant_integral
    (q : ℚ) :
    ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum ℤ in Filter.cofinite,
      algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] q ∈
        PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1 := by
  have h := (algebraMap ℚ RationalFiniteAdele q).2
  filter_upwards [h] with v hv
  have hv' : algebraMap ℚ (v.adicCompletion ℚ) q ∈
      v.adicCompletionIntegers ℚ := by
    change algebraMap ℚ (v.adicCompletion ℚ) q ∈
      v.adicCompletionIntegers ℚ at hv
    exact hv
  simpa using (mem_adicCompletionIntegers_iff_padic v _).1 hv'

/-- All rational Clifford structure constants are integral at cofinitely many
places, simultaneously. -/
theorem eventually_cliffordGeneralSpinIntegralStructureAt :
    ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum ℤ in Filter.cofinite,
      V.CliffordGeneralSpinIntegralStructureAt v := by
  have hmul : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum ℤ in Filter.cofinite,
      ∀ s t u : Finset (Fin n),
      algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
          (V.cliffordMulStructureConstant s t u) ∈
        PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1 := by
    rw [Filter.eventually_all]
    intro s
    rw [Filter.eventually_all]
    intro t
    rw [Filter.eventually_all]
    intro u
    exact eventually_rationalCliffordConstant_integral
      (V.cliffordMulStructureConstant s t u)
  have hreverse :
      ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum ℤ in Filter.cofinite,
        ∀ s u : Finset (Fin n),
      algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
          (V.cliffordReverseStructureConstant s u) ∈
        PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1 := by
    rw [Filter.eventually_all]
    intro s
    rw [Filter.eventually_all]
    intro u
    exact eventually_rationalCliffordConstant_integral
      (V.cliffordReverseStructureConstant s u)
  have hvector :
      ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum ℤ in Filter.cofinite,
        ∀ i : Fin n,
      ∀ u : Finset (Fin n),
      algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
          (V.cliffordVectorBasisCoordinate i u) ∈
        PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1 := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro u
    exact eventually_rationalCliffordConstant_integral
      (V.cliffordVectorBasisCoordinate i u)
  have hone :
      ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum ℤ in Filter.cofinite,
        ∀ u : Finset (Fin n),
      algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
          (V.cliffordSpinOneCoordinate u) ∈
        PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1 := by
    rw [Filter.eventually_all]
    intro u
    exact eventually_rationalCliffordConstant_integral
      (V.cliffordSpinOneCoordinate u)
  filter_upwards [hmul, hreverse, hvector, hone] with v hm hr hv ho
  exact ⟨hm, hr, hv, ho⟩

/-! ## Integral Clifford-coordinate closure -/

theorem cliffordGeneralSpinIntegralStructureAt_one
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : V.CliffordGeneralSpinIntegralStructureAt v)
    (u : Finset (Fin n)) :
    (V.cliffordCoordinateBaseChangeBasis
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).repr 1 u ∈
      PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1 := by
  rw [← map_one (Algebra.TensorProduct.includeRight :
    CliffordAlgebra V.quadraticForm →ₐ[ℚ]
      V.cliffordCoordinateBaseChangeAlgebra
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])]
  change (V.cliffordCoordinateBaseChangeBasis
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).repr
        (V.cliffordCoordinateBaseChangeOfRational
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] 1) u ∈ _
  rw [V.cliffordCoordinateBaseChangeOfRational_repr]
  exact hv.2.2.2 u

theorem cliffordGeneralSpinIntegralStructureAt_vector
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : V.CliffordGeneralSpinIntegralStructureAt v)
    (x : Fin n → ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
    (hx : ∀ i, x i ∈
      PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1)
    (u : Finset (Fin n)) :
    (V.cliffordCoordinateBaseChangeBasis
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).repr
        (V.cliffordCoordinateBaseChangeVectorOfCoordinates
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] x) u ∈
      PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1 := by
  rw [cliffordCoordinateBaseChangeVectorOfCoordinates, map_sum,
    Finsupp.coe_finset_sum, Finset.sum_apply]
  exact Subring.sum_mem _ fun i _ => by
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    apply Subring.mul_mem _ (hx i)
    simpa using hv.2.2.1 i u

theorem cliffordGeneralSpinIntegralStructureAt_mul
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : V.CliffordGeneralSpinIntegralStructureAt v)
    {x y : V.cliffordCoordinateBaseChangeAlgebra
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]}
    (hx : ∀ s, (V.cliffordCoordinateBaseChangeBasis
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).repr x s ∈
      PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1)
    (hy : ∀ s, (V.cliffordCoordinateBaseChangeBasis
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).repr y s ∈
      PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1)
    (u : Finset (Fin n)) :
    (V.cliffordCoordinateBaseChangeBasis
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).repr (x * y) u ∈
      PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1 := by
  rw [V.cliffordCoordinateBaseChangeBasis_repr_mul]
  exact Subring.sum_mem _ fun s _ => Subring.sum_mem _ fun t _ =>
    Subring.mul_mem _ (Subring.mul_mem _ (hx s) (hy t)) (hv.1 s t u)

theorem cliffordGeneralSpinIntegralStructureAt_reverse
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : V.CliffordGeneralSpinIntegralStructureAt v)
    {x : V.cliffordCoordinateBaseChangeAlgebra
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]}
    (hx : ∀ s, (V.cliffordCoordinateBaseChangeBasis
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).repr x s ∈
      PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1)
    (u : Finset (Fin n)) :
    (V.cliffordCoordinateBaseChangeBasis
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).repr
        (V.cliffordCoordinateBaseChangeReverse
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] x) u ∈
      PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1 := by
  rw [V.cliffordCoordinateBaseChangeBasis_repr_reverse]
  exact Subring.sum_mem _ fun s _ =>
    Subring.mul_mem _ (hx s) (hv.2.1 s u)

theorem cliffordGeneralSpinIntegralStructureAt_smul
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    {a : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]}
    (ha : a ∈ PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1)
    {x : V.cliffordCoordinateBaseChangeAlgebra
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]}
    (hx : ∀ s, (V.cliffordCoordinateBaseChangeBasis
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).repr x s ∈
      PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1)
    (u : Finset (Fin n)) :
    (V.cliffordCoordinateBaseChangeBasis
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).repr (a • x) u ∈
      PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1 := by
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact Subring.mul_mem _ ha (hx u)

/-! ## Integral reflection-pair words -/

/-- An anisotropic vector has integral coordinates and unit quadratic value
at the specified p-adic place. -/
def IsIntegralAnisotropicVectorAt
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (x : (V.commutativeScalarExtensionQuadraticForm
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).AnisotropicVector) : Prop :=
  (∀ i, x.1 i ∈ PadicInt.subring
    (Rat.HeightOneSpectrum.primesEquiv v).1) ∧
  Units.mk0
      (V.commutativeScalarExtensionQuadraticForm
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] x.1)
      x.2 ∈ padicIntegralUnitsSubgroup
        (Rat.HeightOneSpectrum.primesEquiv v).1

theorem CliffordSpinCandidateIntegralSpinorRangeGoodPlace.unitVectorToPadic_isIntegral
    {v : IsDedekindDomain.HeightOneSpectrum ℤ}
    (P : V.CliffordSpinCandidateIntegralSpinorRangeGoodPlace v)
    (x : P.unimodularForm.UnitVector) :
    V.IsIntegralAnisotropicVectorAt v (P.unitVectorToPadic x) := by
  constructor
  · intro i
    exact (x.1 i).property
  · rw [mem_padicIntegralUnitsSubgroup_iff]
    constructor
    · change V.commutativeScalarExtensionQuadraticForm
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
          (P.unitVectorToPadic x).1 ∈ _
      rw [P.quadraticForm_unitVectorToPadic]
      exact (x.property.unit :
        ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ).1.property
    · let q : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ := x.property.unit
      have hunit :
          Units.mk0
              (V.commutativeScalarExtensionQuadraticForm
                ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
                (P.unitVectorToPadic x).1)
              (P.unitVectorToPadic x).2 =
            Units.map PadicInt.Coe.ringHom.toMonoidHom q := by
        apply Units.ext
        change V.commutativeScalarExtensionQuadraticForm
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
            (P.unitVectorToPadic x).1 =
          ((q : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) :
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
        rw [P.quadraticForm_unitVectorToPadic]
        exact congrArg
          (fun z : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).1] ↦
            (z : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]))
          (IsUnit.unit_spec x.property).symm
      rw [hunit, ← map_inv]
      exact (q⁻¹ : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ).1.property

/-- Every vector occurring in a reflection-pair list is integral with unit
quadratic value. -/
def AreIntegralReflectionPairsAt
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (ps : List (QuadraticMap.ReflectionWord.ReflectionPair
      (V.commutativeScalarExtensionQuadraticForm
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]))) : Prop :=
  ∀ p ∈ ps,
    V.IsIntegralAnisotropicVectorAt v p.1 ∧
      V.IsIntegralAnisotropicVectorAt v p.2

theorem reflectionPairsCoordinateCliffordUnit_integral
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : V.CliffordGeneralSpinIntegralStructureAt v)
    (ps : List (QuadraticMap.ReflectionWord.ReflectionPair
      (V.commutativeScalarExtensionQuadraticForm
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])))
    (hps : V.AreIntegralReflectionPairsAt v ps) :
    ∀ u, (V.cliffordCoordinateBaseChangeBasis
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).repr
          (V.reflectionPairsCoordinateCliffordUnit
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] ps :
              V.cliffordCoordinateBaseChangeAlgebra
                ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) u ∈
      PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1 := by
  induction ps with
  | nil =>
      intro u
      rw [V.coe_reflectionPairsCoordinateCliffordUnit_nil]
      exact V.cliffordGeneralSpinIntegralStructureAt_one v hv u
  | cons p ps ih =>
      have hp := hps p (List.mem_cons_self)
      have htail : V.AreIntegralReflectionPairsAt v ps := by
        intro q hq
        exact hps q (List.mem_cons_of_mem p hq)
      intro u
      rw [V.coe_reflectionPairsCoordinateCliffordUnit_cons]
      apply V.cliffordGeneralSpinIntegralStructureAt_mul v hv (ih htail)
      intro s
      apply V.cliffordGeneralSpinIntegralStructureAt_mul v hv
      · exact V.cliffordGeneralSpinIntegralStructureAt_vector v hv p.2 hp.2.1
      · exact V.cliffordGeneralSpinIntegralStructureAt_vector v hv p.1 hp.1.1

theorem reflectionPairsQuadraticUnit_mem_padicIntegralUnitsSubgroup
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (ps : List (QuadraticMap.ReflectionWord.ReflectionPair
      (V.commutativeScalarExtensionQuadraticForm
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])))
    (hps : V.AreIntegralReflectionPairsAt v ps) :
    reflectionPairsQuadraticUnit
        (V.commutativeScalarExtensionQuadraticForm
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) ps ∈
      padicIntegralUnitsSubgroup
        (Rat.HeightOneSpectrum.primesEquiv v).1 := by
  induction ps with
  | nil => exact Subgroup.one_mem _
  | cons p ps ih =>
      rw [reflectionPairsQuadraticUnit_cons]
      apply Subgroup.mul_mem
      · exact Subgroup.mul_mem _
          (hps p List.mem_cons_self).1.2
          (hps p List.mem_cons_self).2.2
      · apply ih
        intro q hq
        exact hps q (List.mem_cons_of_mem p hq)

theorem reflectionPairsCoordinateCliffordUnit_inv_integral
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : V.CliffordGeneralSpinIntegralStructureAt v)
    (g : V.specialOrthogonalMatrixGroup
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
    (ps : List (QuadraticMap.ReflectionWord.ReflectionPair
      (V.commutativeScalarExtensionQuadraticForm
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])))
    (hword : eval
        (V.commutativeScalarExtensionQuadraticForm
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
        (flattenPairs
          (V.commutativeScalarExtensionQuadraticForm
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) ps) =
      V.specialOrthogonalMatrixGroupIsometryEquiv
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] g)
    (hps : V.AreIntegralReflectionPairsAt v ps) :
    ∀ u, (V.cliffordCoordinateBaseChangeBasis
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).repr
          (((CliffordGeneralSpinIntrinsicPoint.ofReflectionPairs V
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] g ps hword).cliffordUnit⁻¹ :
                (V.cliffordCoordinateBaseChangeAlgebra
                  ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])ˣ) :
            V.cliffordCoordinateBaseChangeAlgebra
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) u ∈
      PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1 := by
  let y := CliffordGeneralSpinIntrinsicPoint.ofReflectionPairs V
    ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] g ps hword
  have hforward := V.reflectionPairsCoordinateCliffordUnit_integral v hv ps hps
  have hnu := V.reflectionPairsQuadraticUnit_mem_padicIntegralUnitsSubgroup v ps hps
  intro u
  rw [V.coe_inv_cliffordUnit_eq_inv_similitude_mul_reverse
    ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] y]
  rw [← Algebra.smul_def]
  apply V.cliffordGeneralSpinIntegralStructureAt_smul v
  · change (((reflectionPairsQuadraticUnit
        (V.commutativeScalarExtensionQuadraticForm
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) ps)⁻¹ :
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ) :
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) ∈ _
    exact (mem_padicIntegralUnitsSubgroup_iff _ _).1 hnu |>.2
  · exact V.cliffordGeneralSpinIntegralStructureAt_reverse v hv hforward

theorem ofReflectionPairs_isIntegral
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : V.CliffordGeneralSpinIntegralStructureAt v)
    (g : V.HeightOnePadicSpecialOrthogonalIntegralGroup v)
    (ps : List (QuadraticMap.ReflectionWord.ReflectionPair
      (V.commutativeScalarExtensionQuadraticForm
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])))
    (hword : eval
        (V.commutativeScalarExtensionQuadraticForm
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
        (flattenPairs
          (V.commutativeScalarExtensionQuadraticForm
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) ps) =
      V.specialOrthogonalMatrixGroupIsometryEquiv
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] g.1)
    (hps : V.AreIntegralReflectionPairsAt v ps) :
    V.PadicCliffordGeneralSpinIsIntegral
      (Rat.HeightOneSpectrum.primesEquiv v).1
      (CliffordGeneralSpinIntrinsicPoint.ofReflectionPairs V
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] g.1 ps hword) := by
  let y := CliffordGeneralSpinIntrinsicPoint.ofReflectionPairs V
    ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] g.1 ps hword
  unfold PadicCliffordGeneralSpinIsIntegral
  refine ⟨V.reflectionPairsCoordinateCliffordUnit_integral v hv ps hps,
    V.reflectionPairsCoordinateCliffordUnit_inv_integral
      v hv g.1 ps hword hps, ?_, ?_⟩
  · exact V.reflectionPairsQuadraticUnit_mem_padicIntegralUnitsSubgroup v ps hps
  · rw [CliffordGeneralSpinIntrinsicPoint.ofReflectionPairs_matrixGroup]
    rw [V.mem_padicSpecialOrthogonalIntegralSubgroup_iff]
    exact (V.mem_heightOnePadicSpecialOrthogonalIntegralSubgroup_iff_padic
      v g.1).1 g.2

private theorem first_mem_flattenPairs_of_mem
    {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (Q : QuadraticForm K M)
    {p : QuadraticMap.ReflectionWord.ReflectionPair Q}
    {ps : List (QuadraticMap.ReflectionWord.ReflectionPair Q)}
    (hp : p ∈ ps) : p.1 ∈ flattenPairs Q ps := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
      rw [flattenPairs_cons]
      rcases List.mem_cons.mp hp with rfl | hp
      · simp
      · simp only [List.mem_cons]
        exact Or.inr (Or.inr (ih hp))

private theorem second_mem_flattenPairs_of_mem
    {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (Q : QuadraticForm K M)
    {p : QuadraticMap.ReflectionWord.ReflectionPair Q}
    {ps : List (QuadraticMap.ReflectionWord.ReflectionPair Q)}
    (hp : p ∈ ps) : p.2 ∈ flattenPairs Q ps := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
      rw [flattenPairs_cons]
      rcases List.mem_cons.mp hp with rfl | hp
      · simp
      · simp only [List.mem_cons]
        exact Or.inr (Or.inr (ih hp))

theorem areIntegralReflectionPairsAt_of_unitReflectionWord
    {v : IsDedekindDomain.HeightOneSpectrum ℤ}
    (P : V.CliffordSpinCandidateIntegralSpinorRangeGoodPlace v)
    (xs : P.unimodularForm.UnitReflectionWord)
    (ps : List (QuadraticMap.ReflectionWord.ReflectionPair
      (V.commutativeScalarExtensionQuadraticForm
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])))
    (hps : flattenPairs
        (V.commutativeScalarExtensionQuadraticForm
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) ps =
      P.unitReflectionWordToPadic xs) :
    V.AreIntegralReflectionPairsAt v ps := by
  intro p hp
  have hfirst : p.1 ∈ P.unitReflectionWordToPadic xs := by
    rw [← hps]
    exact first_mem_flattenPairs_of_mem _ hp
  have hsecond : p.2 ∈ P.unitReflectionWordToPadic xs := by
    rw [← hps]
    exact second_mem_flattenPairs_of_mem _ hp
  simp only [CliffordSpinCandidateIntegralSpinorRangeGoodPlace.unitReflectionWordToPadic,
    List.mem_map] at hfirst hsecond
  obtain ⟨x, _hx, hx⟩ := hfirst
  obtain ⟨y, _hy, hy⟩ := hsecond
  have hxi :=
    CliffordSpinCandidateIntegralSpinorRangeGoodPlace.unitVectorToPadic_isIntegral
      (V := V) P x
  have hyi :=
    CliffordSpinCandidateIntegralSpinorRangeGoodPlace.unitVectorToPadic_isIntegral
      (V := V) P y
  rw [← hx, ← hy]
  exact ⟨hxi, hyi⟩

/-! ## Closure under integral central correction -/

theorem padicCliffordGeneralSpin_ofScalar_isIntegral
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : V.CliffordGeneralSpinIntegralStructureAt v)
    (z : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ)
    (hz : z ∈ padicIntegralUnitsSubgroup
      (Rat.HeightOneSpectrum.primesEquiv v).1) :
    V.PadicCliffordGeneralSpinIsIntegral
      (Rat.HeightOneSpectrum.primesEquiv v).1
      (CliffordGeneralSpinIntrinsicPoint.ofScalar V
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] z) := by
  have hz' := (mem_padicIntegralUnitsSubgroup_iff _ _).1 hz
  unfold PadicCliffordGeneralSpinIsIntegral
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u
    change (V.cliffordCoordinateBaseChangeBasis
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).repr
        ((CliffordGeneralSpinIntrinsicPoint.scalarCliffordUnit V
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] z :
            V.cliffordCoordinateBaseChangeAlgebra
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])) u ∈
      PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1
    rw [CliffordGeneralSpinIntrinsicPoint.coe_scalarCliffordUnit]
    rw [V.cliffordCoordinateBaseChangeBasis_repr_algebraMap]
    apply Subring.mul_mem _ hz'.1
    simpa [cliffordSpinOneCoordinate] using hv.2.2.2 u
  · intro u
    rw [show
      ((CliffordGeneralSpinIntrinsicPoint.ofScalar V
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] z).cliffordUnit⁻¹ :
          (V.cliffordCoordinateBaseChangeAlgebra
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])ˣ) =
        CliffordGeneralSpinIntrinsicPoint.scalarCliffordUnit V
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] z⁻¹ by
      change (CliffordGeneralSpinIntrinsicPoint.scalarCliffordUnit V
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] z)⁻¹ = _
      simp [CliffordGeneralSpinIntrinsicPoint.scalarCliffordUnit]]
    change (V.cliffordCoordinateBaseChangeBasis
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).repr
        ((CliffordGeneralSpinIntrinsicPoint.scalarCliffordUnit V
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] z⁻¹ :
            V.cliffordCoordinateBaseChangeAlgebra
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])) u ∈
      PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1
    rw [CliffordGeneralSpinIntrinsicPoint.coe_scalarCliffordUnit]
    rw [V.cliffordCoordinateBaseChangeBasis_repr_algebraMap]
    apply Subring.mul_mem _ hz'.2
    simpa [cliffordSpinOneCoordinate] using hv.2.2.2 u
  · rw [CliffordGeneralSpinIntrinsicPoint.ofScalar_similitude]
    simpa [pow_two] using Subgroup.mul_mem _ hz hz
  · rw [CliffordGeneralSpinIntrinsicPoint.ofScalar_matrixGroup]
    exact Subgroup.one_mem _

theorem padicCliffordGeneralSpinIsIntegral_mul
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : V.CliffordGeneralSpinIntegralStructureAt v)
    {x y : V.HeightOnePadicCliffordGeneralSpinGroup v}
    (hx : V.PadicCliffordGeneralSpinIsIntegral
      (Rat.HeightOneSpectrum.primesEquiv v).1 x)
    (hy : V.PadicCliffordGeneralSpinIsIntegral
      (Rat.HeightOneSpectrum.primesEquiv v).1 y) :
    V.PadicCliffordGeneralSpinIsIntegral
      (Rat.HeightOneSpectrum.primesEquiv v).1 (x * y) := by
  unfold PadicCliffordGeneralSpinIsIntegral at hx hy ⊢
  refine ⟨V.cliffordGeneralSpinIntegralStructureAt_mul v hv hx.1 hy.1,
    ?_, ?_, ?_⟩
  · simpa only [mul_inv_rev] using
      V.cliffordGeneralSpinIntegralStructureAt_mul v hv hy.2.1 hx.2.1
  · exact Subgroup.mul_mem _ hx.2.2.1 hy.2.2.1
  · rw [CliffordGeneralSpinIntrinsicPoint.mul_matrixGroup]
    exact Subgroup.mul_mem _ hx.2.2.2 hy.2.2.2

theorem mem_padicIntegralUnitsSubgroup_of_sq_mem
    (p : ℕ) [Fact p.Prime] (z : ℚ_[p]ˣ)
    (hz : z ^ 2 ∈ padicIntegralUnitsSubgroup p) :
    z ∈ padicIntegralUnitsSubgroup p := by
  rw [mem_padicIntegralUnitsSubgroup_iff] at hz ⊢
  constructor
  · rw [PadicInt.mem_subring_iff] at hz ⊢
    have hpow : ‖((z : ℚ_[p]))‖ ^ 2 ≤ 1 := by
      simpa [norm_pow] using hz.1
    nlinarith [norm_nonneg (z : ℚ_[p])]
  · rw [PadicInt.mem_subring_iff] at hz ⊢
    have hpow : ‖(((z⁻¹ : ℚ_[p]ˣ) : ℚ_[p]))‖ ^ 2 ≤ 1 := by
      simpa [norm_pow] using hz.2
    nlinarith [norm_nonneg ((z⁻¹ : ℚ_[p]ˣ) : ℚ_[p])]

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

local instance latticeIntegralGeneralSpinSimilitudePrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000

/-- A p-adic unit with integral value and inverse, regarded as a literal
unit of `Z_p`. -/
def padicIntUnitOfPadicIntegralUnit
    (p : ℕ) [Fact p.Prime] (a : ℚ_[p]ˣ)
    (ha : a ∈ RationalQuadraticSpaceMatrix.padicIntegralUnitsSubgroup p) :
    ℤ_[p]ˣ := by
  rw [RationalQuadraticSpaceMatrix.mem_padicIntegralUnitsSubgroup_iff] at ha
  refine ⟨⟨(a : ℚ_[p]), (PadicInt.mem_subring_iff p).mp ha.1⟩,
    ⟨((a⁻¹ : ℚ_[p]ˣ) : ℚ_[p]), (PadicInt.mem_subring_iff p).mp ha.2⟩, ?_, ?_⟩
  · apply Subtype.ext
    exact congrArg Units.val (mul_inv_cancel a)
  · apply Subtype.ext
    exact congrArg Units.val (inv_mul_cancel a)

@[simp]
theorem coe_padicIntUnitOfPadicIntegralUnit
    (p : ℕ) [Fact p.Prime] (a : ℚ_[p]ˣ)
    (ha : a ∈ RationalQuadraticSpaceMatrix.padicIntegralUnitsSubgroup p) :
    (((padicIntUnitOfPadicIntegralUnit p a ha : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) = a :=
  rfl

/-- At every odd-unimodular admissible place where the finite rational
Clifford structure constants are integral, every p-adic integral unit has an
integral intrinsic `GSpin` lift with that literal similitude. -/
theorem exists_integral_padicCliffordGeneralSpin_similitude_eq
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (v : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateAdmissibleIntegralPlace
      (∅ : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)))
    (hvOdd : v.1 ∉
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces)
    (hvStructure :
      L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinIntegralStructureAt v.1)
    (a : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ)
    (ha : a ∈ RationalQuadraticSpaceMatrix.padicIntegralUnitsSubgroup
      (Rat.HeightOneSpectrum.primesEquiv v.1).1) :
    ∃ x : L.rationalQuadraticSpaceMatrix.HeightOnePadicCliffordGeneralSpinGroup v.1,
      L.rationalQuadraticSpaceMatrix.PadicCliffordGeneralSpinIsIntegral
          (Rat.HeightOneSpectrum.primesEquiv v.1).1 x ∧
        x.similitude = a := by
  let V := L.rationalQuadraticSpaceMatrix
  let p := (Rat.HeightOneSpectrum.primesEquiv v.1).1
  let za : ℤ_[p]ˣ := padicIntUnitOfPadicIntegralUnit p a ha
  have haClass : (a : Rat.SquareClass ℚ_[p]) ∈
      Rat.padicUnitSquareClassSubgroup p := by
    refine ⟨za, ?_⟩
    exact congrArg (fun u : ℚ_[p]ˣ ↦ (u : Rat.SquareClass ℚ_[p]))
      (Units.ext (coe_padicIntUnitOfPadicIntegralUnit p a ha))
  have hRange :=
    heightOnePadicSpecialOrthogonalIntegralSpinorNormRange_eq_padicUnitSquareClassSubgroup
      L (∅ : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) v hvOdd
  have haRange : (a : Rat.SquareClass ℚ_[p]) ∈
      (V.heightOnePadicSpecialOrthogonalIntegralSpinorNormHom v.1).range := by
    rw [hRange]
    exact haClass
  obtain ⟨g, hg⟩ := haRange
  let P :=
    V.cliffordSpinCandidateIntegralSpinorRangeGoodPlace_of_not_mem_badPlaces
      (by omega : 2 ≤ r + 2) v.1 hvOdd
  obtain ⟨xs, hxs, _hlen⟩ :=
    RationalQuadraticSpaceMatrix.CliffordSpinCandidateIntegralSpinorRangeGoodPlace.exists_unitReflectionWord_eval_eq
      V P g
  let Q := V.commutativeScalarExtensionQuadraticForm ℚ_[p]
  let word := P.unitReflectionWordToPadic xs
  have hwordEval : eval Q word =
      V.specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] g.1 :=
    P.eval_unitReflectionWordToPadic_eq_original g xs hxs
  have hdet : LinearMap.det (eval Q word).toLinearEquiv.toLinearMap = 1 := by
    rw [hwordEval]
    exact detOneIsometryGroup_det Q
      (V.specialOrthogonalMatrixGroupDetOneIsometryHom ℚ_[p] g.1)
  obtain ⟨ps, hps⟩ := exists_pairs_flatten_eq Q word
    (even_length_of_det_eval_eq_one Q word hdet)
  have hpairsEval : eval Q (flattenPairs Q ps) =
      V.specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] g.1 := by
    rw [hps, hwordEval]
  have hpairsIntegral : V.AreIntegralReflectionPairsAt v.1 ps :=
    V.areIntegralReflectionPairsAt_of_unitReflectionWord P xs ps hps
  let y :=
    RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.ofReflectionPairs
      V ℚ_[p] g.1 ps hpairsEval
  have hyIntegral : V.PadicCliffordGeneralSpinIsIntegral p y :=
    V.ofReflectionPairs_isIntegral v.1 hvStructure g ps hpairsEval hpairsIntegral
  have hyNuIntegral : y.similitude ∈
      RationalQuadraticSpaceMatrix.padicIntegralUnitsSubgroup p :=
    hyIntegral.2.2.1
  have hclass : (a : Rat.SquareClass ℚ_[p]) =
      (y.similitude : Rat.SquareClass ℚ_[p]) := by
    calc
      (a : Rat.SquareClass ℚ_[p]) =
          V.heightOnePadicSpecialOrthogonalIntegralSpinorNormHom v.1 g := hg.symm
      _ = V.specialOrthogonalSpinorNormHom ℚ_[p] g.1 := rfl
      _ = V.specialOrthogonalSpinorNormHom ℚ_[p] y.matrixGroup := by
        rw [RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.ofReflectionPairs_matrixGroup]
      _ = (y.similitude : Rat.SquareClass ℚ_[p]) :=
        RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.specialOrthogonalSpinorNorm_matrixGroup_eq_similitudeSquareClass
          V ℚ_[p] y
  have hsq : a / y.similitude ∈ Subgroup.square ℚ_[p]ˣ :=
    QuotientGroup.eq_iff_div_mem.mp hclass
  rw [Subgroup.mem_square] at hsq
  obtain ⟨z, hz⟩ := hsq
  have hzpow : z ^ 2 ∈
      RationalQuadraticSpaceMatrix.padicIntegralUnitsSubgroup p := by
    rw [pow_two, ← hz]
    exact Subgroup.div_mem _ ha hyNuIntegral
  have hzIntegral : z ∈
      RationalQuadraticSpaceMatrix.padicIntegralUnitsSubgroup p :=
    RationalQuadraticSpaceMatrix.mem_padicIntegralUnitsSubgroup_of_sq_mem p z hzpow
  let x :=
    RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.ofScalar
      V ℚ_[p] z * y
  refine ⟨x, ?_, ?_⟩
  · exact V.padicCliffordGeneralSpinIsIntegral_mul v.1 hvStructure
      (V.padicCliffordGeneralSpin_ofScalar_isIntegral v.1 hvStructure z hzIntegral)
      hyIntegral
  · change z ^ 2 * y.similitude = a
    rw [pow_two, ← hz]
    simp

end PositiveDefiniteIntegralLattice

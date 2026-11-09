import SMSFormula.RationalCliffordSpinCandidateIntegralReflectionFieldBridge
import SMSFormula.RationalPadicUnitSquareClass

/-!
# Integral p-adic spinor norms are unit-valued at odd unimodular places

The integral Cartan--Dieudonne word from the recursive carrier is cast to the
original p-adic quadratic space.  Every factor has unit quadratic value, so
the word's square-class product lies in the unit square-class subgroup.
Determinant one forces the word length to be even; pairing consecutive
reflections and applying the reflection-pair formula identifies
that product with the special-orthogonal spinor norm.

This proves the good-place upper inclusion without using
integral Spin lifting, the covering degree, or Haar comparison.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open QuadraticMap.ReflectionWord

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

local instance integralSpinorNormUnitValuedPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- The square class of a cast integral unit vector is the image of its
literal `Z_p` unit. -/
theorem CliffordSpinCandidateIntegralSpinorRangeGoodPlace.quadraticValueSquareClass_unitVectorToPadic
    {V : RationalQuadraticSpaceMatrix n}
    {v : IsDedekindDomain.HeightOneSpectrum ℤ}
    (P : V.CliffordSpinCandidateIntegralSpinorRangeGoodPlace v)
    (x : P.unimodularForm.UnitVector) :
    quadraticValueSquareClass
        (V.commutativeScalarExtensionQuadraticForm
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
        (P.unitVectorToPadic x) =
      Rat.padicUnitSquareClassHom
        (Rat.HeightOneSpectrum.primesEquiv v).1 x.property.unit := by
  rw [Rat.padicUnitSquareClassHom_apply]
  refine congrArg
    (fun u : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ ↦
      (u : Rat.SquareClass
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])) ?_
  apply Units.ext
  change
    V.commutativeScalarExtensionQuadraticForm
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
        (P.unitVectorToPadic x) =
      (((x.property.unit :
          ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) :
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]))
  rw [P.quadraticForm_unitVectorToPadic]
  exact congrArg
    (fun z : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).1] ↦
      (z : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]))
    (IsUnit.unit_spec x.property).symm

/-- Each cast integral unit vector contributes a unit square class. -/
theorem CliffordSpinCandidateIntegralSpinorRangeGoodPlace.quadraticValueSquareClass_unitVectorToPadic_mem
    {V : RationalQuadraticSpaceMatrix n}
    {v : IsDedekindDomain.HeightOneSpectrum ℤ}
    (P : V.CliffordSpinCandidateIntegralSpinorRangeGoodPlace v)
    (x : P.unimodularForm.UnitVector) :
    quadraticValueSquareClass
        (V.commutativeScalarExtensionQuadraticForm
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
        (P.unitVectorToPadic x) ∈
      Rat.padicUnitSquareClassSubgroup
        (Rat.HeightOneSpectrum.primesEquiv v).1 := by
  change _ ∈
    (Rat.padicUnitSquareClassHom
      (Rat.HeightOneSpectrum.primesEquiv v).1).range
  refine ⟨x.property.unit, ?_⟩
  exact (P.quadraticValueSquareClass_unitVectorToPadic x).symm

/-- The full cast word has unit-valued square-class product. -/
theorem CliffordSpinCandidateIntegralSpinorRangeGoodPlace.squareClassProduct_unitReflectionWordToPadic_mem
    {V : RationalQuadraticSpaceMatrix n}
    {v : IsDedekindDomain.HeightOneSpectrum ℤ}
    (P : V.CliffordSpinCandidateIntegralSpinorRangeGoodPlace v)
    (xs : P.unimodularForm.UnitReflectionWord) :
    squareClassProduct
        (V.commutativeScalarExtensionQuadraticForm
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
        (P.unitReflectionWordToPadic xs) ∈
      Rat.padicUnitSquareClassSubgroup
        (Rat.HeightOneSpectrum.primesEquiv v).1 := by
  induction xs with
  | nil =>
      simp [CliffordSpinCandidateIntegralSpinorRangeGoodPlace.unitReflectionWordToPadic]
  | cons x xs ih =>
      rw [CliffordSpinCandidateIntegralSpinorRangeGoodPlace.unitReflectionWordToPadic,
        List.map_cons, squareClassProduct_cons]
      exact Subgroup.mul_mem _
        (P.quadraticValueSquareClass_unitVectorToPadic_mem x) ih

/-- A reflection word representing a special-orthogonal matrix has spinor
norm equal to its whole-word square-class product; hence any subgroup
containing that product contains the spinor norm. -/
theorem specialOrthogonalSpinorNormHom_mem_padicUnitSquareClassSubgroup_of_word
    {p : ℕ} [Fact p.Prime]
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.specialOrthogonalMatrixGroup ℚ_[p])
    (xs :
      (V.commutativeScalarExtensionQuadraticForm ℚ_[p]).ReflectionWord)
    (hxs :
      eval (V.commutativeScalarExtensionQuadraticForm ℚ_[p]) xs =
        V.specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] g)
    (hunit :
      squareClassProduct
          (V.commutativeScalarExtensionQuadraticForm ℚ_[p]) xs ∈
        Rat.padicUnitSquareClassSubgroup p) :
    V.specialOrthogonalSpinorNormHom ℚ_[p] g ∈
      Rat.padicUnitSquareClassSubgroup p := by
  let Q := V.commutativeScalarExtensionQuadraticForm ℚ_[p]
  have hdet :
      LinearMap.det (eval Q xs).toLinearEquiv.toLinearMap = 1 := by
    rw [hxs]
    exact detOneIsometryGroup_det Q
      (V.specialOrthogonalMatrixGroupDetOneIsometryHom ℚ_[p] g)
  obtain ⟨ps, hps⟩ :=
    exists_pairs_flatten_eq Q xs
      (even_length_of_det_eval_eq_one Q xs hdet)
  have hpairs :
      eval Q (flattenPairs Q ps) =
        V.specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] g := by
    rw [hps, hxs]
  have hspin :
      V.specialOrthogonalSpinorNormHom ℚ_[p] g =
        reflectionPairSquareClassProduct Q ps :=
    V.specialOrthogonalSpinorNormHom_eq_reflectionPairSquareClassProduct
      ℚ_[p] g ps hpairs
  have hclass :
      V.specialOrthogonalSpinorNormHom ℚ_[p] g =
        squareClassProduct Q xs := by
    calc
      _ = reflectionPairSquareClassProduct Q ps := hspin
      _ = squareClassProduct Q (flattenPairs Q ps) :=
        (squareClassProduct_flattenPairs Q ps).symm
      _ = squareClassProduct Q xs := by rw [hps]
  rw [hclass]
  exact hunit

/-- At a certified odd-unimodular place, the spinor norm of every integral
special-orthogonal point is represented by a p-adic unit. -/
theorem CliffordSpinCandidateIntegralSpinorRangeGoodPlace.specialOrthogonalSpinorNorm_mem_padicUnitSquareClassSubgroup
    {V : RationalQuadraticSpaceMatrix n}
    {v : IsDedekindDomain.HeightOneSpectrum ℤ}
    (P : V.CliffordSpinCandidateIntegralSpinorRangeGoodPlace v)
    (g : V.HeightOnePadicSpecialOrthogonalIntegralGroup v) :
    V.specialOrthogonalSpinorNormHom
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] g.1 ∈
      Rat.padicUnitSquareClassSubgroup
        (Rat.HeightOneSpectrum.primesEquiv v).1 := by
  obtain ⟨xs, hxs, _hlen⟩ :=
    CliffordSpinCandidateIntegralSpinorRangeGoodPlace.exists_unitReflectionWord_eval_eq
      V P g
  apply
    V.specialOrthogonalSpinorNormHom_mem_padicUnitSquareClassSubgroup_of_word
      g.1 (P.unitReflectionWordToPadic xs)
  · exact P.eval_unitReflectionWordToPadic_eq_original g xs hxs
  · exact P.squareClassProduct_unitReflectionWordToPadic_mem xs

/-- The integral spinor-norm upper inclusion, proved from
the certified odd-unimodular model. -/
theorem CliffordSpinCandidateIntegralSpinorRangeGoodPlace.spinorNormUnitValued
    {V : RationalQuadraticSpaceMatrix n}
    {v : IsDedekindDomain.HeightOneSpectrum ℤ}
    (P : V.CliffordSpinCandidateIntegralSpinorRangeGoodPlace v) :
    V.CliffordSpinCandidateIntegralSpinorNormUnitValuedAt v := by
  rintro _ ⟨g, rfl⟩
  rw [V.heightOnePadicSpecialOrthogonalIntegralSpinorNormHom_apply]
  exact P.specialOrthogonalSpinorNorm_mem_padicUnitSquareClassSubgroup g

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

/-- Outside the explicit odd-unimodular bad set, the restricted integral
spinor range has degree two with no remaining upper-inclusion hypothesis. -/
theorem heightOnePadicSpecialOrthogonalIntegralSpinorNormRangeDegree_eq_two_of_not_mem_badPlaces
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateAdmissibleIntegralPlace S)
    (hv : v.1 ∉
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces) :
    L.rationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalIntegralSpinorNormRangeDegree
        v.1 = 2 := by
  let P :=
    L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateIntegralSpinorRangeGoodPlace_of_not_mem_badPlaces
      (by omega : 2 ≤ r + 2) v.1 hv
  exact
    heightOnePadicSpecialOrthogonalIntegralSpinorNormRangeDegree_eq_two_of_not_mem_badPlaces_of_unitValued
      L S v hv P.spinorNormUnitValued

/-- Away from the completed lifting and odd-unimodular bad sets, the integral
Spin and `SO` differential volumes are equal without an arithmetic upper
hypothesis. -/
theorem heightOnePadicCliffordSpinCandidateIntegralVolume_eq_soIntegralVolume_of_not_mem_badPlaces
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateAdmissibleIntegralPlace S)
    (hvRange : v.1 ∉
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces)
    (hvLift : v.1 ∉
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateIntegralLiftingBadPlaces) :
    L.rationalQuadraticSpaceMatrix.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume
        v.1 =
      L.rationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalIntegralVolume
        v.1 := by
  let P :=
    L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateIntegralSpinorRangeGoodPlace_of_not_mem_badPlaces
      (by omega : 2 ≤ r + 2) v.1 hvRange
  exact
    heightOnePadicCliffordSpinCandidateIntegralVolume_eq_soIntegralVolume_of_not_mem_badPlaces_of_unitValued
      L S v hvRange hvLift P.spinorNormUnitValued

end PositiveDefiniteIntegralLattice

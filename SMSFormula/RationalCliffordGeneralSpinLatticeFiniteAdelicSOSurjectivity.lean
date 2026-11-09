import SMSFormula.RationalCliffordGeneralSpinLatticeIntegralSimilitude
import SMSFormula.RationalCliffordGeneralSpinFiniteAdelicRestrictedFamily

/-!
# Finite-adelic surjectivity of lattice general Spin onto special orthogonal

At every good integral place, the completed integral Cartan--Dieudonne word
for an integral `SO` point gives an integral intrinsic `GSpin` lift by the
literal reflection-pair Clifford product.  Arbitrary fieldwise lifts are used
at the finite exceptional set.  Restricted-family assembly then proves that
the actual finite-adelic intrinsic `GSpin -> SO` map is onto.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open QuadraticMap.ReflectionWord

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

local instance latticeFiniteAdelicGeneralSpinSOPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000

/-- At a good odd-unimodular place with integral Clifford structure, every
integral `SO` point has an integral intrinsic `GSpin` lift. -/
theorem exists_integral_padicCliffordGeneralSpin_toSpecialOrthogonal_eq
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (v : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateAdmissibleIntegralPlace
      (∅ : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)))
    (hvOdd : v.1 ∉
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces)
    (hvStructure :
      L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinIntegralStructureAt v.1)
    (g : L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalIntegralGroup
      v.1) :
    ∃ x : L.rationalQuadraticSpaceMatrix.HeightOnePadicCliffordGeneralSpinGroup v.1,
      L.rationalQuadraticSpaceMatrix.PadicCliffordGeneralSpinIsIntegral
          (Rat.HeightOneSpectrum.primesEquiv v.1).1 x ∧
        L.rationalQuadraticSpaceMatrix.padicCliffordGeneralSpinToSpecialOrthogonalHom
            (Rat.HeightOneSpectrum.primesEquiv v.1).1 x = g.1 := by
  let V := L.rationalQuadraticSpaceMatrix
  let p := (Rat.HeightOneSpectrum.primesEquiv v.1).1
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
  let x :=
    RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.ofReflectionPairs
      V ℚ_[p] g.1 ps hpairsEval
  refine ⟨x,
    V.ofReflectionPairs_isIntegral v.1 hvStructure g ps hpairsEval hpairsIntegral,
    ?_⟩
  exact
    RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.ofReflectionPairs_matrixGroup
      V ℚ_[p] g.1 ps hpairsEval

/-- Every finite-adelic lattice `SO` point has a cofinally integral family
of local intrinsic `GSpin` lifts. -/
theorem exists_finiteAdelicCliffordGeneralSpinRestrictedLift_toSO
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (g : L.rationalQuadraticSpaceMatrix.FiniteAdelicSpecialOrthogonalGroup) :
    ∃ x : L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordGeneralSpinRestrictedFamily,
      ∀ v,
        L.rationalQuadraticSpaceMatrix.padicCliffordGeneralSpinToSpecialOrthogonalHom
            (Rat.HeightOneSpectrum.primesEquiv v).1 (x.1 v) =
          L.rationalQuadraticSpaceMatrix.finiteAdelicSpecialOrthogonalHeightOneComponentHom
            v g := by
  let V := L.rationalQuadraticSpaceMatrix
  have hlocalLift : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
      ∃ x : V.HeightOnePadicCliffordGeneralSpinGroup v,
        V.padicCliffordGeneralSpinToSpecialOrthogonalHom
            (Rat.HeightOneSpectrum.primesEquiv v).1 x =
            V.finiteAdelicSpecialOrthogonalHeightOneComponentHom v g ∧
          (v ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces ∅ →
            v ∉ V.cliffordSpinCandidateOddUnimodularBadPlaces →
            V.CliffordGeneralSpinIntegralStructureAt v →
            V.HeightOnePadicSpecialOrthogonalIsIntegral v
                (V.finiteAdelicSpecialOrthogonalHeightOneComponentHom v g) →
              V.PadicCliffordGeneralSpinIsIntegral
                (Rat.HeightOneSpectrum.primesEquiv v).1 x) := by
    intro v
    by_cases hgood :
        v ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces ∅ ∧
          v ∉ V.cliffordSpinCandidateOddUnimodularBadPlaces ∧
          V.CliffordGeneralSpinIntegralStructureAt v ∧
          V.HeightOnePadicSpecialOrthogonalIsIntegral v
            (V.finiteAdelicSpecialOrthogonalHeightOneComponentHom v g)
    · let w : V.CliffordSpinCandidateAdmissibleIntegralPlace ∅ :=
        ⟨v, hgood.1⟩
      let gv : V.HeightOnePadicSpecialOrthogonalIntegralGroup v :=
        ⟨V.finiteAdelicSpecialOrthogonalHeightOneComponentHom v g,
          hgood.2.2.2⟩
      obtain ⟨x, hxIntegral, hx⟩ :=
        exists_integral_padicCliffordGeneralSpin_toSpecialOrthogonal_eq
          L w hgood.2.1 hgood.2.2.1 gv
      exact ⟨x, hx, fun _ _ _ _ => hxIntegral⟩
    · obtain ⟨x, hx⟩ :=
        RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom_surjective
          V ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
          (V.finiteAdelicSpecialOrthogonalHeightOneComponentHom v g)
      exact ⟨x, hx, fun h1 h2 h3 h4 =>
        False.elim (hgood ⟨h1, h2, h3, h4⟩)⟩
  let localLift : V.HeightOnePadicCliffordGeneralSpinGroupProduct :=
    fun v => Classical.choose (hlocalLift v)
  have hlocalLift_map : ∀ v,
      V.padicCliffordGeneralSpinToSpecialOrthogonalHom
          (Rat.HeightOneSpectrum.primesEquiv v).1 (localLift v) =
        V.finiteAdelicSpecialOrthogonalHeightOneComponentHom v g :=
    fun v => (Classical.choose_spec (hlocalLift v)).1
  have hrestricted : V.IsFiniteAdelicCliffordGeneralSpinRestrictedFamily localLift := by
    have hSORestricted :=
      V.finiteAdelicSpecialOrthogonalHeightOneComponents_isRestrictedFamily g
    filter_upwards
      [hSORestricted,
        (V.cliffordSpinCandidateAdmissibleExceptionalPlaces ∅).eventually_cofinite_notMem,
        V.cliffordSpinCandidateOddUnimodularBadPlaces.eventually_cofinite_notMem,
        V.eventually_cliffordGeneralSpinIntegralStructureAt]
        with v hvSO hvAdmissible hvOdd hvStructure
    exact (Classical.choose_spec (hlocalLift v)).2
      hvAdmissible hvOdd hvStructure hvSO
  exact ⟨⟨localLift, hrestricted⟩, hlocalLift_map⟩

/-- The actual finite-adelic intrinsic `GSpin -> SO` map for a lattice form
is surjective in every rank at least two. -/
theorem finiteAdelicCliffordGeneralSpinToSpecialOrthogonalHom_surjective
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    Function.Surjective
      L.rationalQuadraticSpaceMatrix.finiteAdelicCliffordGeneralSpinToSpecialOrthogonalHom := by
  intro g
  let V := L.rationalQuadraticSpaceMatrix
  obtain ⟨x, hx⟩ := exists_finiteAdelicCliffordGeneralSpinRestrictedLift_toSO L g
  let y := V.finiteAdelicCliffordGeneralSpinRestrictedFamilyAssembly x
  refine ⟨y, ?_⟩
  apply V.finiteAdelicSpecialOrthogonalHeightOneComponentsHom_injective
  funext v
  change V.finiteAdelicSpecialOrthogonalHeightOneComponent
      (V.finiteAdelicCliffordGeneralSpinToSpecialOrthogonalHom y) v =
    V.finiteAdelicSpecialOrthogonalHeightOneComponent g v
  have hy := congrFun
    (V.finiteAdelicCliffordGeneralSpinHeightOneComponents_assembly x) v
  change V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v y = x.1 v at hy
  change V.specialOrthogonalMatrixGroupMap
      (RationalQuadraticSpaceMatrix.finiteAdelicCliffordGeneralSpinHeightOneAlgHom v)
        (V.finiteAdelicCliffordGeneralSpinToSpecialOrthogonalHom y) =
    V.finiteAdelicSpecialOrthogonalHeightOneComponentHom v g
  have hnatur := DFunLike.congr_fun
    (RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonal_naturality
      V (RationalQuadraticSpaceMatrix.finiteAdelicCliffordGeneralSpinHeightOneAlgHom v)) y
  change
    V.specialOrthogonalMatrixGroupMap
        (RationalQuadraticSpaceMatrix.finiteAdelicCliffordGeneralSpinHeightOneAlgHom v)
        (RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom
          V RationalFiniteAdele y) =
      RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom
        V ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
        (RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.mapGroupHom V
          (RationalQuadraticSpaceMatrix.finiteAdelicCliffordGeneralSpinHeightOneAlgHom v) y)
      at hnatur
  calc
    V.specialOrthogonalMatrixGroupMap
        (RationalQuadraticSpaceMatrix.finiteAdelicCliffordGeneralSpinHeightOneAlgHom v)
        (V.finiteAdelicCliffordGeneralSpinToSpecialOrthogonalHom y) =
        V.padicCliffordGeneralSpinToSpecialOrthogonalHom
          (Rat.HeightOneSpectrum.primesEquiv v).1
          (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v y) := hnatur
    _ = V.padicCliffordGeneralSpinToSpecialOrthogonalHom
          (Rat.HeightOneSpectrum.primesEquiv v).1 (x.1 v) := by rw [hy]
    _ = V.finiteAdelicSpecialOrthogonalHeightOneComponentHom v g := hx v

end PositiveDefiniteIntegralLattice

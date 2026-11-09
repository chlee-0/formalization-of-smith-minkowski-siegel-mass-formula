import SMSFormula.RationalCliffordGeneralSpinFiniteAdelicShell
import SMSFormula.RationalCliffordGeneralSpinAdelicProduct

/-!
# Full-adelic nonisotropic block shells

The existing real/finite product equivalence for intrinsic `GSpin` combines
the field-valued real shell lift with the restricted finite-adelic shell lift.
Scalar-extension naturality detects the resulting orbit equality in the two
literal components of the rational adele ring.  No new adelic carrier or
unrestricted product of local points is introduced.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The block-shell orbit commutes literally with the existing rational
diagonal into the full adeles. -/
@[simp]
theorem CliffordGeneralSpinIntrinsicPoint.rationalDiagonal_nonisotropicLastShellOrbitMap
    (W : RationalQuadraticSpaceMatrix n)
    (a : ℚ) (ha : a ≠ 0)
    (z : (W.nonisotropicLastExtension a ha).RationalCliffordGeneralSpinGroup) :
    W.nonisotropicLastQuadraticShellMap a ha
        (Algebra.ofId ℚ RationalAdele)
        (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
          W a ha ℚ z) =
      CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
        W a ha RationalAdele
        ((W.nonisotropicLastExtension a ha)
          |>.rationalCliffordGeneralSpinFullAdelicDiagonalHom z) := by
  exact
    CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap_naturality
      W a ha (Algebra.ofId ℚ RationalAdele) z

/-- The existing intrinsic full-adelic GSpin group is transitive on the
nonisotropic last-coordinate shell. -/
theorem CliffordGeneralSpinIntrinsicPoint.fullAdelic_nonisotropicLastShellOrbitMap_surjective
    (W : RationalQuadraticSpaceMatrix n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0) :
    Function.Surjective
      (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
        W a ha RationalAdele) := by
  intro y
  let V := W.nonisotropicLastExtension a ha
  let yReal := W.nonisotropicLastQuadraticShellMap a ha
    fullAdelicCliffordGeneralSpinRealAlgHom y
  let yFinite := W.nonisotropicLastQuadraticShellMap a ha
    fullAdelicCliffordGeneralSpinFiniteAlgHom y
  obtain ⟨zReal, hzReal⟩ :=
    CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap_surjective
      W a ha ℝ yReal
  obtain ⟨zFinite, hzFinite⟩ :=
    CliffordGeneralSpinIntrinsicPoint.finiteAdelic_nonisotropicLastShellOrbitMap_surjective
      W a ha yFinite
  let z : V.FullAdelicCliffordGeneralSpinGroup :=
    V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm
      (zReal, zFinite)
  refine ⟨z, Subtype.ext ?_⟩
  funext i
  apply Prod.ext
  · apply rationalInfiniteAdeleRingEquivReal.injective
    have hzComponents :=
      V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.apply_symm_apply
        (zReal, zFinite)
    have hzRealComponent := congrArg Prod.fst hzComponents
    have hzRealMap :
        CliffordGeneralSpinIntrinsicPoint.map V
            fullAdelicCliffordGeneralSpinRealAlgHom z = zReal := by
      change
        (V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv z).1 = zReal
      simpa only [z] using hzRealComponent
    have hnaturality := congrArg Subtype.val
      (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap_naturality
        W a ha fullAdelicCliffordGeneralSpinRealAlgHom z)
    have horbit := congrArg Subtype.val hzReal
    change fullAdelicCliffordGeneralSpinRealAlgHom
        ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
          W a ha RationalAdele z).1 i) =
      fullAdelicCliffordGeneralSpinRealAlgHom (y.1 i)
    calc
      fullAdelicCliffordGeneralSpinRealAlgHom
          ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
            W a ha RationalAdele z).1 i) =
        (W.nonisotropicLastQuadraticShellMap a ha
          fullAdelicCliffordGeneralSpinRealAlgHom
          (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
            W a ha RationalAdele z)).1 i := rfl
      _ = (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
            W a ha ℝ
            (CliffordGeneralSpinIntrinsicPoint.map V
              fullAdelicCliffordGeneralSpinRealAlgHom z)).1 i :=
        congrFun hnaturality i
      _ = (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
            W a ha ℝ zReal).1 i := by rw [hzRealMap]
      _ = yReal.1 i := congrFun horbit i
      _ = fullAdelicCliffordGeneralSpinRealAlgHom (y.1 i) := rfl
  · have hzComponents :=
      V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.apply_symm_apply
        (zReal, zFinite)
    have hzFiniteComponent := congrArg Prod.snd hzComponents
    have hzFiniteMap :
        CliffordGeneralSpinIntrinsicPoint.map V
            fullAdelicCliffordGeneralSpinFiniteAlgHom z = zFinite := by
      change
        (V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv z).2 = zFinite
      simpa only [z] using hzFiniteComponent
    have hnaturality := congrArg Subtype.val
      (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap_naturality
        W a ha fullAdelicCliffordGeneralSpinFiniteAlgHom z)
    have horbit := congrArg Subtype.val hzFinite
    change fullAdelicCliffordGeneralSpinFiniteAlgHom
        ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
          W a ha RationalAdele z).1 i) =
      fullAdelicCliffordGeneralSpinFiniteAlgHom (y.1 i)
    calc
      fullAdelicCliffordGeneralSpinFiniteAlgHom
          ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
            W a ha RationalAdele z).1 i) =
        (W.nonisotropicLastQuadraticShellMap a ha
          fullAdelicCliffordGeneralSpinFiniteAlgHom
          (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
            W a ha RationalAdele z)).1 i := rfl
      _ = (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
            W a ha RationalFiniteAdele
            (CliffordGeneralSpinIntrinsicPoint.map V
              fullAdelicCliffordGeneralSpinFiniteAlgHom z)).1 i :=
        congrFun hnaturality i
      _ = (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
            W a ha RationalFiniteAdele zFinite).1 i := by rw [hzFiniteMap]
      _ = yFinite.1 i := congrFun horbit i
      _ = fullAdelicCliffordGeneralSpinFiniteAlgHom (y.1 i) := rfl

/-- The fiber of the full-adelic shell orbit above the last-coordinate
basepoint is exactly the certified complement GSpin stabilizer. -/
theorem CliffordGeneralSpinIntrinsicPoint.fullAdelic_nonisotropicLastShellOrbitMap_eq_last_iff
    (W : RationalQuadraticSpaceMatrix n)
    (a : ℚ) (ha : a ≠ 0)
    (z : (W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup) :
    CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
        W a ha RationalAdele z =
      ⟨lastCoordinateVector,
        W.lastCoordinateVector_mem_nonisotropicLastQuadraticShell
          a ha RationalAdele⟩ ↔
    z ∈ W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      a ha RationalAdele := by
  rw [W.mem_nonisotropicLastComplementGeneralSpinStabilizerSubgroup_iff]
  constructor
  · intro hz
    apply Subtype.ext_iff.mp at hz
    unfold IsNonisotropicLastBlockGeneralSpinFixedPoint
    unfold FixesLastCoordinate
    simpa only [CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap,
      CliffordGeneralSpinIntrinsicPoint.matrixGroup_coe] using hz
  · intro hz
    apply Subtype.ext
    unfold IsNonisotropicLastBlockGeneralSpinFixedPoint at hz
    unfold FixesLastCoordinate at hz
    simpa only [CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap,
      CliffordGeneralSpinIntrinsicPoint.matrixGroup_coe] using hz

end RationalQuadraticSpaceMatrix

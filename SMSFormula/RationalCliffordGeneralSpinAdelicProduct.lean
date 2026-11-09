import SMSFormula.RationalCliffordGeneralSpinFiniteAdelicLocalCompactness

/-!
# Real/finite splitting for intrinsic full-adelic general Spin

The finite closed-coordinate realization of intrinsic `GSpin` is compatible
with the literal product presentation `A_Q = A_Q,infinity x A_Q,f`.  This file
assembles a full-adelic point from a real point and a finite-adelic point and
proves the resulting algebraic product equivalence.  The construction uses
the already completed real/finite splitting of `SO`; it introduces no measure
or Tamagawa normalization.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

def fullAdelicCliffordGeneralSpinRealAlgHom : RationalAdele →ₐ[ℚ] ℝ :=
  rationalInfiniteAdeleRingEquivReal.toRingHom.toRatAlgHom.comp
    (AlgHom.fst ℚ RationalInfiniteAdele RationalFiniteAdele)

def fullAdelicCliffordGeneralSpinFiniteAlgHom :
    RationalAdele →ₐ[ℚ] RationalFiniteAdele :=
  AlgHom.snd ℚ RationalInfiniteAdele RationalFiniteAdele

def fullAdelicCliffordGeneralSpinToRealFiniteHom :
    V.FullAdelicCliffordGeneralSpinGroup →*
      V.RealCliffordGeneralSpinGroup ×
        V.FiniteAdelicCliffordGeneralSpinGroup where
  toFun x :=
    (CliffordGeneralSpinIntrinsicPoint.map V
        fullAdelicCliffordGeneralSpinRealAlgHom x,
      CliffordGeneralSpinIntrinsicPoint.map V
        fullAdelicCliffordGeneralSpinFiniteAlgHom x)
  map_one' := by
    apply Prod.ext <;>
      exact map_one (CliffordGeneralSpinIntrinsicPoint.mapGroupHom V _)
  map_mul' x y := by
    apply Prod.ext <;>
      exact map_mul (CliffordGeneralSpinIntrinsicPoint.mapGroupHom V _) x y

def fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate
    (x : V.RealCliffordGeneralSpinGroup ×
      V.FiniteAdelicCliffordGeneralSpinGroup) :
    V.CliffordGeneralSpinClosedCoordinateSpace RationalAdele :=
  ((((fun s =>
      (rationalInfiniteAdeleRingEquivReal.symm
          ((V.cliffordCoordinateBaseChangeBasis ℝ).repr
            (x.1.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra ℝ) s),
        (V.cliffordCoordinateBaseChangeBasis RationalFiniteAdele).repr
          (x.2.cliffordUnit :
            V.cliffordCoordinateBaseChangeAlgebra RationalFiniteAdele) s)),
    (fun s =>
      (rationalInfiniteAdeleRingEquivReal.symm
          ((V.cliffordCoordinateBaseChangeBasis ℝ).repr
            (((x.1.cliffordUnit⁻¹ :
              (V.cliffordCoordinateBaseChangeAlgebra ℝ)ˣ) :
                V.cliffordCoordinateBaseChangeAlgebra ℝ)) s),
        (V.cliffordCoordinateBaseChangeBasis RationalFiniteAdele).repr
          (((x.2.cliffordUnit⁻¹ :
            (V.cliffordCoordinateBaseChangeAlgebra RationalFiniteAdele)ˣ) :
              V.cliffordCoordinateBaseChangeAlgebra RationalFiniteAdele)) s))),
    MulEquiv.prodUnits.symm
      (Units.map
        rationalInfiniteAdeleRingEquivReal.symm.toMonoidHom x.1.similitude,
        x.2.similitude)),
    V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.symm
      (x.1.matrixGroup, x.2.matrixGroup))

theorem fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate_clifford_real
    (x : V.RealCliffordGeneralSpinGroup ×
      V.FiniteAdelicCliffordGeneralSpinGroup) :
    V.cliffordCoordinateBaseChangeMap
        fullAdelicCliffordGeneralSpinRealAlgHom
        (V.cliffordGeneralSpinClosedCoordinateClifford RationalAdele
          (V.fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate x)) =
      (x.1.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra ℝ) := by
  apply (V.cliffordCoordinateBaseChangeBasis ℝ).repr.injective
  ext s
  rw [V.cliffordCoordinateBaseChangeBasis_repr_map]
  simp [fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate,
    cliffordGeneralSpinClosedCoordinateClifford,
    fullAdelicCliffordGeneralSpinRealAlgHom]
  exact rationalInfiniteAdeleRingEquivReal.apply_symm_apply _

theorem fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate_clifford_finite
    (x : V.RealCliffordGeneralSpinGroup ×
      V.FiniteAdelicCliffordGeneralSpinGroup) :
    V.cliffordCoordinateBaseChangeMap
        fullAdelicCliffordGeneralSpinFiniteAlgHom
        (V.cliffordGeneralSpinClosedCoordinateClifford RationalAdele
          (V.fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate x)) =
      (x.2.cliffordUnit :
        V.cliffordCoordinateBaseChangeAlgebra RationalFiniteAdele) := by
  apply (V.cliffordCoordinateBaseChangeBasis RationalFiniteAdele).repr.injective
  ext s
  rw [V.cliffordCoordinateBaseChangeBasis_repr_map]
  simp [fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate,
    cliffordGeneralSpinClosedCoordinateClifford,
    fullAdelicCliffordGeneralSpinFiniteAlgHom]
  rfl

theorem fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate_cliffordInv_real
    (x : V.RealCliffordGeneralSpinGroup ×
      V.FiniteAdelicCliffordGeneralSpinGroup) :
    V.cliffordCoordinateBaseChangeMap
        fullAdelicCliffordGeneralSpinRealAlgHom
        (V.cliffordGeneralSpinClosedCoordinateCliffordInv RationalAdele
          (V.fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate x)) =
      (((x.1.cliffordUnit⁻¹ :
        (V.cliffordCoordinateBaseChangeAlgebra ℝ)ˣ) :
          V.cliffordCoordinateBaseChangeAlgebra ℝ)) := by
  apply (V.cliffordCoordinateBaseChangeBasis ℝ).repr.injective
  ext s
  rw [V.cliffordCoordinateBaseChangeBasis_repr_map]
  simp [fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate,
    cliffordGeneralSpinClosedCoordinateCliffordInv,
    fullAdelicCliffordGeneralSpinRealAlgHom]
  exact rationalInfiniteAdeleRingEquivReal.apply_symm_apply _

theorem fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate_cliffordInv_finite
    (x : V.RealCliffordGeneralSpinGroup ×
      V.FiniteAdelicCliffordGeneralSpinGroup) :
    V.cliffordCoordinateBaseChangeMap
        fullAdelicCliffordGeneralSpinFiniteAlgHom
        (V.cliffordGeneralSpinClosedCoordinateCliffordInv RationalAdele
          (V.fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate x)) =
      (((x.2.cliffordUnit⁻¹ :
        (V.cliffordCoordinateBaseChangeAlgebra RationalFiniteAdele)ˣ) :
          V.cliffordCoordinateBaseChangeAlgebra RationalFiniteAdele)) := by
  apply (V.cliffordCoordinateBaseChangeBasis RationalFiniteAdele).repr.injective
  ext s
  rw [V.cliffordCoordinateBaseChangeBasis_repr_map]
  simp [fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate,
    cliffordGeneralSpinClosedCoordinateCliffordInv,
    fullAdelicCliffordGeneralSpinFiniteAlgHom]
  rfl

theorem fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate_similitude_real
    (x : V.RealCliffordGeneralSpinGroup ×
      V.FiniteAdelicCliffordGeneralSpinGroup) :
    Units.map fullAdelicCliffordGeneralSpinRealAlgHom.toMonoidHom
        (V.fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate x).1.2 =
      x.1.similitude := by
  apply Units.ext
  simp [fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate,
    fullAdelicCliffordGeneralSpinRealAlgHom]
  exact rationalInfiniteAdeleRingEquivReal.apply_symm_apply _

theorem fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate_similitude_finite
    (x : V.RealCliffordGeneralSpinGroup ×
      V.FiniteAdelicCliffordGeneralSpinGroup) :
    Units.map fullAdelicCliffordGeneralSpinFiniteAlgHom.toMonoidHom
        (V.fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate x).1.2 =
      x.2.similitude := by
  apply Units.ext
  rfl

theorem fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate_so_real
    (x : V.RealCliffordGeneralSpinGroup ×
      V.FiniteAdelicCliffordGeneralSpinGroup) :
    V.specialOrthogonalMatrixGroupMap
        fullAdelicCliffordGeneralSpinRealAlgHom
        (V.fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate x).2 =
      x.1.matrixGroup := by
  have h := congrArg Prod.fst
    (V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.apply_symm_apply
      (x.1.matrixGroup, x.2.matrixGroup))
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  exact congrArg (fun g => g.1.1.1 i j) h

theorem fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate_so_finite
    (x : V.RealCliffordGeneralSpinGroup ×
      V.FiniteAdelicCliffordGeneralSpinGroup) :
    V.specialOrthogonalMatrixGroupMap
        fullAdelicCliffordGeneralSpinFiniteAlgHom
        (V.fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate x).2 =
      x.2.matrixGroup := by
  have h := congrArg Prod.snd
    (V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.apply_symm_apply
      (x.1.matrixGroup, x.2.matrixGroup))
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  apply funext
  intro i
  apply funext
  intro j
  exact congrArg (fun g => g.1.1.1 i j) h

/-- Equality of full-adelic Clifford elements is detected by the real and
finite scalar-extension maps. -/
theorem cliffordCoordinateBaseChange_eq_of_real_finite_maps_eq
    {a b : V.cliffordCoordinateBaseChangeAlgebra RationalAdele}
    (hreal : V.cliffordCoordinateBaseChangeMap
        fullAdelicCliffordGeneralSpinRealAlgHom a =
      V.cliffordCoordinateBaseChangeMap
        fullAdelicCliffordGeneralSpinRealAlgHom b)
    (hfinite : V.cliffordCoordinateBaseChangeMap
        fullAdelicCliffordGeneralSpinFiniteAlgHom a =
      V.cliffordCoordinateBaseChangeMap
        fullAdelicCliffordGeneralSpinFiniteAlgHom b) :
    a = b := by
  apply (V.cliffordCoordinateBaseChangeBasis RationalAdele).repr.injective
  ext s
  apply Prod.ext
  · apply rationalInfiniteAdeleRingEquivReal.injective
    have h := congrArg (fun z =>
      (V.cliffordCoordinateBaseChangeBasis ℝ).repr z s) hreal
    simpa [V.cliffordCoordinateBaseChangeBasis_repr_map,
      fullAdelicCliffordGeneralSpinRealAlgHom] using h
  · have h := congrArg (fun z =>
      (V.cliffordCoordinateBaseChangeBasis RationalFiniteAdele).repr z s)
        hfinite
    simpa [V.cliffordCoordinateBaseChangeBasis_repr_map,
      fullAdelicCliffordGeneralSpinFiniteAlgHom] using h

theorem isCliffordGeneralSpinClosedCoordinate_realFinite
    (x : V.RealCliffordGeneralSpinGroup ×
      V.FiniteAdelicCliffordGeneralSpinGroup) :
    V.IsCliffordGeneralSpinClosedCoordinate RationalAdele
      (V.fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate x) := by
  let z := V.fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate x
  let u := V.cliffordGeneralSpinClosedCoordinateClifford RationalAdele z
  let uInv := V.cliffordGeneralSpinClosedCoordinateCliffordInv RationalAdele z
  change u * uInv = 1 ∧ uInv * u = 1 ∧
    V.cliffordCoordinateBaseChangeInvolute RationalAdele u = u ∧
    u * V.cliffordCoordinateBaseChangeReverse RationalAdele u =
      algebraMap RationalAdele
        (V.cliffordCoordinateBaseChangeAlgebra RationalAdele) z.1.2 ∧
    ∀ i, u * V.cliffordCoordinateBaseChangeVector RationalAdele i * uInv =
      ∑ j, z.2.1.1.1 j i •
        V.cliffordCoordinateBaseChangeVector RationalAdele j
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply V.cliffordCoordinateBaseChange_eq_of_real_finite_maps_eq
    · rw [map_mul,
        V.fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate_clifford_real,
        V.fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate_cliffordInv_real,
        map_one]
      exact congrArg Units.val (mul_inv_cancel x.1.cliffordUnit)
    · rw [map_mul,
        V.fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate_clifford_finite,
        V.fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate_cliffordInv_finite,
        map_one]
      exact congrArg Units.val (mul_inv_cancel x.2.cliffordUnit)
  · apply V.cliffordCoordinateBaseChange_eq_of_real_finite_maps_eq
    · rw [map_mul,
        V.fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate_cliffordInv_real,
        V.fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate_clifford_real,
        map_one]
      exact congrArg Units.val (inv_mul_cancel x.1.cliffordUnit)
    · rw [map_mul,
        V.fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate_cliffordInv_finite,
        V.fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate_clifford_finite,
        map_one]
      exact congrArg Units.val (inv_mul_cancel x.2.cliffordUnit)
  · apply V.cliffordCoordinateBaseChange_eq_of_real_finite_maps_eq
    · rw [V.cliffordCoordinateBaseChangeMap_involute,
        V.fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate_clifford_real]
      exact x.1.involute_eq
    · rw [V.cliffordCoordinateBaseChangeMap_involute,
        V.fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate_clifford_finite]
      exact x.2.involute_eq
  · apply V.cliffordCoordinateBaseChange_eq_of_real_finite_maps_eq
    · rw [map_mul, V.cliffordCoordinateBaseChangeMap_reverse,
        V.fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate_clifford_real,
        CliffordGeneralSpinIntrinsicPoint.cliffordCoordinateBaseChangeMap_algebraMap]
      have hnu := congrArg Units.val
        (V.fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate_similitude_real x)
      change fullAdelicCliffordGeneralSpinRealAlgHom (↑z.1.2) =
        ↑x.1.similitude at hnu
      rw [hnu]
      exact x.1.mul_reverse_eq
    · rw [map_mul, V.cliffordCoordinateBaseChangeMap_reverse,
        V.fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate_clifford_finite,
        CliffordGeneralSpinIntrinsicPoint.cliffordCoordinateBaseChangeMap_algebraMap]
      have hnu := congrArg Units.val
        (V.fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate_similitude_finite x)
      change fullAdelicCliffordGeneralSpinFiniteAlgHom (↑z.1.2) =
        ↑x.2.similitude at hnu
      rw [hnu]
      exact x.2.mul_reverse_eq
  · intro i
    apply V.cliffordCoordinateBaseChange_eq_of_real_finite_maps_eq
    · change V.cliffordCoordinateBaseChangeMap
          fullAdelicCliffordGeneralSpinRealAlgHom
          (u * V.cliffordCoordinateBaseChangeVector RationalAdele i * uInv) =
        V.cliffordCoordinateBaseChangeMap
          fullAdelicCliffordGeneralSpinRealAlgHom
          (V.cliffordCoordinateBaseChangeVectorOfCoordinates RationalAdele
            (fun j => z.2.1.1.1 j i))
      rw [map_mul, map_mul, V.cliffordCoordinateBaseChangeMap_vector,
        V.fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate_clifford_real,
        V.fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate_cliffordInv_real,
        V.cliffordCoordinateBaseChangeMap_vectorOfCoordinates]
      have hso :=
        V.fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate_so_real x
      have hentry (j : Fin n) :
          fullAdelicCliffordGeneralSpinRealAlgHom (z.2.1.1.1 j i) =
            x.1.matrixGroup.1.1.1 j i := by
        exact congrArg (fun q => q.1.1.1 j i) hso
      calc
        (x.1.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra ℝ) *
            V.cliffordCoordinateBaseChangeVector ℝ i *
            (((x.1.cliffordUnit⁻¹ :
              (V.cliffordCoordinateBaseChangeAlgebra ℝ)ˣ) :
                V.cliffordCoordinateBaseChangeAlgebra ℝ)) =
          V.cliffordCoordinateBaseChangeVectorOfCoordinates ℝ
            (fun j => x.1.matrixGroup.1.1.1 j i) := by
              rw [x.1.vectorGraph]
              rfl
        _ = V.cliffordCoordinateBaseChangeVectorOfCoordinates ℝ
            (fun j => fullAdelicCliffordGeneralSpinRealAlgHom
              (z.2.1.1.1 j i)) := by
              congr 2
              funext j
              exact (hentry j).symm
    · change V.cliffordCoordinateBaseChangeMap
          fullAdelicCliffordGeneralSpinFiniteAlgHom
          (u * V.cliffordCoordinateBaseChangeVector RationalAdele i * uInv) =
        V.cliffordCoordinateBaseChangeMap
          fullAdelicCliffordGeneralSpinFiniteAlgHom
          (V.cliffordCoordinateBaseChangeVectorOfCoordinates RationalAdele
            (fun j => z.2.1.1.1 j i))
      rw [map_mul, map_mul, V.cliffordCoordinateBaseChangeMap_vector,
        V.fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate_clifford_finite,
        V.fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate_cliffordInv_finite,
        V.cliffordCoordinateBaseChangeMap_vectorOfCoordinates]
      have hso :=
        V.fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate_so_finite x
      have hentry (j : Fin n) :
          fullAdelicCliffordGeneralSpinFiniteAlgHom (z.2.1.1.1 j i) =
            x.2.matrixGroup.1.1.1 j i := by
        exact congrArg (fun q => q.1.1.1 j i) hso
      calc
        (x.2.cliffordUnit :
            V.cliffordCoordinateBaseChangeAlgebra RationalFiniteAdele) *
            V.cliffordCoordinateBaseChangeVector RationalFiniteAdele i *
            (((x.2.cliffordUnit⁻¹ :
              (V.cliffordCoordinateBaseChangeAlgebra RationalFiniteAdele)ˣ) :
                V.cliffordCoordinateBaseChangeAlgebra RationalFiniteAdele)) =
          V.cliffordCoordinateBaseChangeVectorOfCoordinates RationalFiniteAdele
            (fun j => x.2.matrixGroup.1.1.1 j i) := by
              rw [x.2.vectorGraph]
              rfl
        _ = V.cliffordCoordinateBaseChangeVectorOfCoordinates
            RationalFiniteAdele
            (fun j => fullAdelicCliffordGeneralSpinFiniteAlgHom
              (z.2.1.1.1 j i)) := by
              congr 2
              funext j
              exact (hentry j).symm

def fullAdelicCliffordGeneralSpinRealFiniteAssembly
    (x : V.RealCliffordGeneralSpinGroup ×
      V.FiniteAdelicCliffordGeneralSpinGroup) :
    V.FullAdelicCliffordGeneralSpinGroup :=
  Classical.choose
    ((Set.ext_iff.1 (V.range_cliffordGeneralSpinClosedCoordinateMap
      RationalAdele)
      (V.fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate x)).2
      (V.isCliffordGeneralSpinClosedCoordinate_realFinite x))

theorem fullAdelicCliffordGeneralSpinRealFiniteAssembly_closedCoordinate
    (x : V.RealCliffordGeneralSpinGroup ×
      V.FiniteAdelicCliffordGeneralSpinGroup) :
    V.cliffordGeneralSpinClosedCoordinateMap RationalAdele
        (V.fullAdelicCliffordGeneralSpinRealFiniteAssembly x) =
      V.fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate x :=
  Classical.choose_spec
    ((Set.ext_iff.1 (V.range_cliffordGeneralSpinClosedCoordinateMap
      RationalAdele)
      (V.fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate x)).2
      (V.isCliffordGeneralSpinClosedCoordinate_realFinite x))

theorem fullAdelicCliffordGeneralSpinRealFiniteAssembly_clifford
    (x : V.RealCliffordGeneralSpinGroup ×
      V.FiniteAdelicCliffordGeneralSpinGroup) :
    ((V.fullAdelicCliffordGeneralSpinRealFiniteAssembly x).cliffordUnit :
      V.cliffordCoordinateBaseChangeAlgebra RationalAdele) =
      V.cliffordGeneralSpinClosedCoordinateClifford RationalAdele
        (V.fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate x) := by
  have hz :=
    V.fullAdelicCliffordGeneralSpinRealFiniteAssembly_closedCoordinate x
  have hx := congrArg
    (V.cliffordGeneralSpinClosedCoordinateClifford RationalAdele) hz
  exact (V.cliffordGeneralSpinCliffordOfCoordinates_repr_self
    RationalAdele _).symm.trans hx

theorem fullAdelicCliffordGeneralSpinRealFiniteAssembly_cliffordCoordinate
    (x : V.RealCliffordGeneralSpinGroup ×
      V.FiniteAdelicCliffordGeneralSpinGroup)
    (s : Finset (Fin n)) :
    (V.cliffordCoordinateBaseChangeBasis RationalAdele).repr
        ((V.fullAdelicCliffordGeneralSpinRealFiniteAssembly x).cliffordUnit :
          V.cliffordCoordinateBaseChangeAlgebra RationalAdele) s =
      (rationalInfiniteAdeleRingEquivReal.symm
          ((V.cliffordCoordinateBaseChangeBasis ℝ).repr
            (x.1.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra ℝ) s),
        (V.cliffordCoordinateBaseChangeBasis RationalFiniteAdele).repr
          (x.2.cliffordUnit :
            V.cliffordCoordinateBaseChangeAlgebra RationalFiniteAdele) s) := by
  rw [V.fullAdelicCliffordGeneralSpinRealFiniteAssembly_clifford]
  simp [cliffordGeneralSpinClosedCoordinateClifford,
    fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate]

theorem fullAdelicCliffordGeneralSpinRealFiniteAssembly_similitude
    (x : V.RealCliffordGeneralSpinGroup ×
      V.FiniteAdelicCliffordGeneralSpinGroup) :
    (V.fullAdelicCliffordGeneralSpinRealFiniteAssembly x).similitude =
      MulEquiv.prodUnits.symm
        (Units.map
          rationalInfiniteAdeleRingEquivReal.symm.toMonoidHom x.1.similitude,
          x.2.similitude) := by
  exact congrArg (fun z => z.1.2)
    (V.fullAdelicCliffordGeneralSpinRealFiniteAssembly_closedCoordinate x)

theorem fullAdelicCliffordGeneralSpinRealFiniteAssembly_matrixGroup
    (x : V.RealCliffordGeneralSpinGroup ×
      V.FiniteAdelicCliffordGeneralSpinGroup) :
    (V.fullAdelicCliffordGeneralSpinRealFiniteAssembly x).matrixGroup =
      V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.symm
        (x.1.matrixGroup, x.2.matrixGroup) := by
  exact congrArg (fun z => z.2)
    (V.fullAdelicCliffordGeneralSpinRealFiniteAssembly_closedCoordinate x)

theorem continuous_fullAdelicCliffordGeneralSpinRealFiniteAssembly :
    Continuous V.fullAdelicCliffordGeneralSpinRealFiniteAssembly := by
  let soPair := fun x : V.RealCliffordGeneralSpinGroup ×
      V.FiniteAdelicCliffordGeneralSpinGroup =>
    (x.1.matrixGroup, x.2.matrixGroup)
  have hsoPair : Continuous soPair :=
    (V.continuous_realCliffordGeneralSpinToSpecialOrthogonalHom.comp
      continuous_fst).prodMk
      (V.continuous_finiteAdelicCliffordGeneralSpinToSpecialOrthogonalHom.comp
        continuous_snd)
  let soFull := fun x : V.RealCliffordGeneralSpinGroup ×
      V.FiniteAdelicCliffordGeneralSpinGroup =>
    V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.symm (soPair x)
  have hsoFull : Continuous soFull :=
    V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.symm.continuous.comp
      hsoPair
  have hsoMatrix : Continuous (fun x : V.RealCliffordGeneralSpinGroup ×
      V.FiniteAdelicCliffordGeneralSpinGroup => (soFull x).1.1.1) :=
    Units.continuous_val.comp
      ((continuous_subtype_val.comp continuous_subtype_val).comp hsoFull)
  have hsoInvMatrix : Continuous (fun x : V.RealCliffordGeneralSpinGroup ×
      V.FiniteAdelicCliffordGeneralSpinGroup => (soFull x)⁻¹.1.1.1) :=
    Units.continuous_val.comp
      ((continuous_subtype_val.comp continuous_subtype_val).comp
        (continuous_inv.comp hsoFull))
  have hrealUnitMap : Continuous
      (Units.map rationalInfiniteAdeleRingEquivReal.symm.toMonoidHom) :=
    rationalInfiniteAdeleHomeomorphReal.symm.continuous.units_map
      rationalInfiniteAdeleRingEquivReal.symm.toMonoidHom
  apply continuous_induced_rng.mpr
  apply Continuous.prodMk
  · apply Continuous.prodMk
    · apply continuous_pi
      intro s
      rw [show (fun x : V.RealCliffordGeneralSpinGroup ×
          V.FiniteAdelicCliffordGeneralSpinGroup =>
          (V.cliffordCoordinateBaseChangeBasis RationalAdele).repr
            ((V.fullAdelicCliffordGeneralSpinRealFiniteAssembly x).cliffordUnit :
              V.cliffordCoordinateBaseChangeAlgebra RationalAdele) s) =
        fun x =>
          (rationalInfiniteAdeleRingEquivReal.symm
              ((V.cliffordCoordinateBaseChangeBasis ℝ).repr
                (x.1.cliffordUnit :
                  V.cliffordCoordinateBaseChangeAlgebra ℝ) s),
            (V.cliffordCoordinateBaseChangeBasis RationalFiniteAdele).repr
              (x.2.cliffordUnit :
                V.cliffordCoordinateBaseChangeAlgebra RationalFiniteAdele) s) by
          funext x
          exact
            V.fullAdelicCliffordGeneralSpinRealFiniteAssembly_cliffordCoordinate
              x s]
      exact
        (rationalInfiniteAdeleHomeomorphReal.symm.continuous.comp
          ((V.continuous_cliffordGeneralSpinCliffordCoordinate ℝ s).comp
            continuous_fst)).prodMk
        ((V.continuous_cliffordGeneralSpinCliffordCoordinate
          RationalFiniteAdele s).comp continuous_snd)
    · rw [show (fun x : V.RealCliffordGeneralSpinGroup ×
          V.FiniteAdelicCliffordGeneralSpinGroup =>
          (V.fullAdelicCliffordGeneralSpinRealFiniteAssembly x).similitude) =
        fun x => MulEquiv.prodUnits.symm
          (Units.map
            rationalInfiniteAdeleRingEquivReal.symm.toMonoidHom x.1.similitude,
            x.2.similitude) by
          funext x
          exact
            V.fullAdelicCliffordGeneralSpinRealFiniteAssembly_similitude x]
      exact PositiveDefiniteIntegralLattice.prodUnitsContinuousMulEquiv.symm.continuous.comp
        ((hrealUnitMap.comp
          ((V.continuous_cliffordGeneralSpinSimilitude ℝ).comp
            continuous_fst)).prodMk
          ((V.continuous_cliffordGeneralSpinSimilitude RationalFiniteAdele).comp
            continuous_snd))
  · apply Continuous.prodMk
    · rw [show (fun x : V.RealCliffordGeneralSpinGroup ×
          V.FiniteAdelicCliffordGeneralSpinGroup =>
          (V.fullAdelicCliffordGeneralSpinRealFiniteAssembly x).matrixPoint.1) =
        fun x => (soFull x).1.1.1 by
          funext x
          exact congrArg (fun g => g.1.1.1)
            (V.fullAdelicCliffordGeneralSpinRealFiniteAssembly_matrixGroup x)]
      exact hsoMatrix
    · rw [show (fun x : V.RealCliffordGeneralSpinGroup ×
          V.FiniteAdelicCliffordGeneralSpinGroup =>
          (V.fullAdelicCliffordGeneralSpinRealFiniteAssembly x).matrixGroup⁻¹.1.1.1) =
        fun x => (soFull x)⁻¹.1.1.1 by
          funext x
          exact congrArg (fun g => g⁻¹.1.1.1)
            (V.fullAdelicCliffordGeneralSpinRealFiniteAssembly_matrixGroup x)]
      exact hsoInvMatrix

theorem fullAdelicCliffordGeneralSpinToRealFiniteHom_assembly
    (x : V.RealCliffordGeneralSpinGroup ×
      V.FiniteAdelicCliffordGeneralSpinGroup) :
    V.fullAdelicCliffordGeneralSpinToRealFiniteHom
        (V.fullAdelicCliffordGeneralSpinRealFiniteAssembly x) = x := by
  apply Prod.ext
  · apply CliffordGeneralSpinIntrinsicPoint.ext_cliffordUnit V ℝ
    apply Units.ext
    change V.cliffordCoordinateBaseChangeMap
        fullAdelicCliffordGeneralSpinRealAlgHom
        ((V.fullAdelicCliffordGeneralSpinRealFiniteAssembly x).cliffordUnit :
          V.cliffordCoordinateBaseChangeAlgebra RationalAdele) =
      (x.1.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra ℝ)
    rw [V.fullAdelicCliffordGeneralSpinRealFiniteAssembly_clifford]
    exact
      V.fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate_clifford_real x
  · apply CliffordGeneralSpinIntrinsicPoint.ext_cliffordUnit V RationalFiniteAdele
    apply Units.ext
    change V.cliffordCoordinateBaseChangeMap
        fullAdelicCliffordGeneralSpinFiniteAlgHom
        ((V.fullAdelicCliffordGeneralSpinRealFiniteAssembly x).cliffordUnit :
          V.cliffordCoordinateBaseChangeAlgebra RationalAdele) =
      (x.2.cliffordUnit :
        V.cliffordCoordinateBaseChangeAlgebra RationalFiniteAdele)
    rw [V.fullAdelicCliffordGeneralSpinRealFiniteAssembly_clifford]
    exact
      V.fullAdelicCliffordGeneralSpinRealFiniteClosedCoordinate_clifford_finite x

theorem fullAdelicCliffordGeneralSpinToRealFiniteHom_injective :
    Function.Injective V.fullAdelicCliffordGeneralSpinToRealFiniteHom := by
  intro x y hxy
  apply CliffordGeneralSpinIntrinsicPoint.ext_cliffordUnit V RationalAdele
  apply Units.ext
  apply V.cliffordCoordinateBaseChange_eq_of_real_finite_maps_eq
  · have h := congrArg (fun q =>
      (q.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra ℝ))
      (congrArg Prod.fst hxy)
    simpa [fullAdelicCliffordGeneralSpinToRealFiniteHom,
      CliffordGeneralSpinIntrinsicPoint.map_cliffordUnit_coe] using h
  · have h := congrArg (fun q =>
      (q.cliffordUnit :
        V.cliffordCoordinateBaseChangeAlgebra RationalFiniteAdele))
      (congrArg Prod.snd hxy)
    simpa [fullAdelicCliffordGeneralSpinToRealFiniteHom,
      CliffordGeneralSpinIntrinsicPoint.map_cliffordUnit_coe] using h

theorem fullAdelicCliffordGeneralSpinToRealFiniteHom_bijective :
    Function.Bijective V.fullAdelicCliffordGeneralSpinToRealFiniteHom := by
  refine ⟨V.fullAdelicCliffordGeneralSpinToRealFiniteHom_injective, ?_⟩
  intro x
  exact ⟨V.fullAdelicCliffordGeneralSpinRealFiniteAssembly x,
    V.fullAdelicCliffordGeneralSpinToRealFiniteHom_assembly x⟩

/-- The intrinsic full-adelic general-Spin group is multiplicatively
equivalent to its real and finite-adelic factors. -/
def fullAdelicCliffordGeneralSpinRealFiniteEquiv :
    V.FullAdelicCliffordGeneralSpinGroup ≃*
      V.RealCliffordGeneralSpinGroup ×
        V.FiniteAdelicCliffordGeneralSpinGroup :=
  MulEquiv.ofBijective V.fullAdelicCliffordGeneralSpinToRealFiniteHom
    V.fullAdelicCliffordGeneralSpinToRealFiniteHom_bijective

@[simp]
theorem fullAdelicCliffordGeneralSpinRealFiniteEquiv_apply_real
    (x : V.FullAdelicCliffordGeneralSpinGroup) :
    (V.fullAdelicCliffordGeneralSpinRealFiniteEquiv x).1 =
      CliffordGeneralSpinIntrinsicPoint.map V
        fullAdelicCliffordGeneralSpinRealAlgHom x :=
  rfl

@[simp]
theorem fullAdelicCliffordGeneralSpinRealFiniteEquiv_apply_finite
    (x : V.FullAdelicCliffordGeneralSpinGroup) :
    (V.fullAdelicCliffordGeneralSpinRealFiniteEquiv x).2 =
      CliffordGeneralSpinIntrinsicPoint.map V
        fullAdelicCliffordGeneralSpinFiniteAlgHom x :=
  rfl

/-- The algebraic real/finite splitting is a continuous multiplicative
equivalence for the existing finite-coordinate topologies. -/
def fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv :
    V.FullAdelicCliffordGeneralSpinGroup ≃ₜ*
      V.RealCliffordGeneralSpinGroup ×
        V.FiniteAdelicCliffordGeneralSpinGroup where
  toMulEquiv := V.fullAdelicCliffordGeneralSpinRealFiniteEquiv
  continuous_toFun := by
    apply Continuous.prodMk
    · exact V.continuous_cliffordGeneralSpinMapGroupHom
        fullAdelicCliffordGeneralSpinRealAlgHom
        (rationalInfiniteAdeleHomeomorphReal.continuous.comp continuous_fst)
    · exact V.continuous_cliffordGeneralSpinMapGroupHom
        fullAdelicCliffordGeneralSpinFiniteAlgHom continuous_snd
  continuous_invFun := by
    refine V.continuous_fullAdelicCliffordGeneralSpinRealFiniteAssembly.congr ?_
    intro x
    apply V.fullAdelicCliffordGeneralSpinRealFiniteEquiv.injective
    change V.fullAdelicCliffordGeneralSpinToRealFiniteHom
        (V.fullAdelicCliffordGeneralSpinRealFiniteAssembly x) =
      V.fullAdelicCliffordGeneralSpinToRealFiniteHom
        (V.fullAdelicCliffordGeneralSpinRealFiniteEquiv.symm x)
    rw [V.fullAdelicCliffordGeneralSpinToRealFiniteHom_assembly]
    change x = V.fullAdelicCliffordGeneralSpinRealFiniteEquiv
      (V.fullAdelicCliffordGeneralSpinRealFiniteEquiv.symm x)
    exact
      (V.fullAdelicCliffordGeneralSpinRealFiniteEquiv.apply_symm_apply x).symm

/-- Units of the unique infinite rational adele factor are continuously
equivalent to real units. -/
def rationalInfiniteAdeleUnitsContinuousEquivReal :
    RationalInfiniteAdeleˣ ≃ₜ* ℝˣ :=
  Units.mapContinuousMulEquiv
    (ContinuousMulEquiv.mk' rationalInfiniteAdeleHomeomorphReal (by
      intro x y
      exact rationalInfiniteAdeleRingEquivReal.map_mul x y))

/-- Full rational-adelic units split continuously into real and finite
units, with the same literal product presentation used for `GSpin`. -/
def rationalAdeleUnitsRealFiniteContinuousEquiv :
    RationalAdeleˣ ≃ₜ* ℝˣ × RationalFiniteAdeleˣ :=
  PositiveDefiniteIntegralLattice.prodUnitsContinuousMulEquiv.trans
    (PositiveDefiniteIntegralLattice.prodContinuousMulEquiv
      rationalInfiniteAdeleUnitsContinuousEquivReal
      (ContinuousMulEquiv.refl _))

/-- The real/finite intrinsic `GSpin` splitting commutes with similitude. -/
theorem fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv_similitude
    (x : V.FullAdelicCliffordGeneralSpinGroup) :
    rationalAdeleUnitsRealFiniteContinuousEquiv
        (V.fullAdelicCliffordGeneralSpinSimilitudeHom x) =
      (V.realCliffordGeneralSpinSimilitudeHom
          (V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv x).1,
        V.finiteAdelicCliffordGeneralSpinSimilitudeHom
          (V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv x).2) := by
  apply Prod.ext <;> apply Units.ext <;> rfl

/-- The real/finite intrinsic `GSpin` splitting commutes with its projection
to the already split special-orthogonal group. -/
theorem fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv_toSO
    (x : V.FullAdelicCliffordGeneralSpinGroup) :
    V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv
        (V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom x) =
      (V.realCliffordGeneralSpinToSpecialOrthogonalHom
          (V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv x).1,
        V.finiteAdelicCliffordGeneralSpinToSpecialOrthogonalHom
          (V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv x).2) := by
  apply Prod.ext <;> apply Subtype.ext <;> apply Subtype.ext
  · ext i j
    rfl
  · apply Units.ext
    ext i j
    rfl

end RationalQuadraticSpaceMatrix

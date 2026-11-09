import SMSFormula.RationalCliffordGeneralSpinFiniteAdelicLocalEvaluation
import SMSFormula.RationalSpecialOrthogonalFiniteAdelicRestrictedFamilyCarrier

/-!
# Reverse assembly of finite-adelic intrinsic general-Spin points

A cofinally integral family of local intrinsic `GSpin` points has finitely
many coordinate families.  This file assembles its Clifford unit and inverse,
similitude and inverse, and special-orthogonal action into finite adeles.  The
intrinsic equations are detected after every height-one evaluation, where they
are exactly the equations of the supplied local points.  Hence the assembled
closed coordinates come from a unique finite-adelic intrinsic `GSpin` point.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped Matrix RestrictedProduct

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000

local instance finiteAdelicGeneralSpinRestrictedFamilyPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-! ## Scalar finite-adele assembly -/

/-- Assemble a p-adic scalar family that is integral cofinitely. -/
def finiteAdeleOfCofinitelyIntegralPadicFamily
    (a : (v : IsDedekindDomain.HeightOneSpectrum ℤ) →
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
    (ha : ∀ᶠ v in Filter.cofinite,
      a v ∈ PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1) :
    RationalFiniteAdele :=
  ⟨fun v => (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm (a v),
    ha.mono fun v hv => by
      apply (mem_adicCompletionIntegers_iff_padic v _).2
      simpa using hv⟩

@[simp]
theorem finiteAdeleOfCofinitelyIntegralPadicFamily_apply
    (a : (v : IsDedekindDomain.HeightOneSpectrum ℤ) →
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
    (ha : ∀ᶠ v in Filter.cofinite,
      a v ∈ PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    finiteAdelicCliffordGeneralSpinHeightOneAlgHom v
      (finiteAdeleOfCofinitelyIntegralPadicFamily a ha) = a v := by
  exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).apply_symm_apply _

/-! ## Assembled Clifford coordinates and similitude -/

def finiteAdelicCliffordGeneralSpinRestrictedFamilyCliffordCoordinate
    (g : V.FiniteAdelicCliffordGeneralSpinRestrictedFamily)
    (s : Finset (Fin n)) : RationalFiniteAdele :=
  finiteAdeleOfCofinitelyIntegralPadicFamily
    (fun v => (V.cliffordCoordinateBaseChangeBasis
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).repr
        ((g.1 v).cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) s)
    (g.2.mono fun _v hv => hv.1 s)

def finiteAdelicCliffordGeneralSpinRestrictedFamilyInverseCliffordCoordinate
    (g : V.FiniteAdelicCliffordGeneralSpinRestrictedFamily)
    (s : Finset (Fin n)) : RationalFiniteAdele :=
  finiteAdeleOfCofinitelyIntegralPadicFamily
    (fun v => (V.cliffordCoordinateBaseChangeBasis
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).repr
        (((g.1 v).cliffordUnit⁻¹ :
          (V.cliffordCoordinateBaseChangeAlgebra
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])ˣ) :
          V.cliffordCoordinateBaseChangeAlgebra
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) s)
    (g.2.mono fun _v hv => hv.2.1 s)

def finiteAdelicCliffordGeneralSpinRestrictedFamilySimilitude
    (g : V.FiniteAdelicCliffordGeneralSpinRestrictedFamily) :
    RationalFiniteAdele :=
  finiteAdeleOfCofinitelyIntegralPadicFamily
    (fun v => ((g.1 v).similitude :
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]))
    (g.2.mono fun _v hv =>
      (mem_padicIntegralUnitsSubgroup_iff _ _).1 hv.2.2.1 |>.1)

def finiteAdelicCliffordGeneralSpinRestrictedFamilyInverseSimilitude
    (g : V.FiniteAdelicCliffordGeneralSpinRestrictedFamily) :
    RationalFiniteAdele :=
  finiteAdeleOfCofinitelyIntegralPadicFamily
    (fun v => (((g.1 v).similitude⁻¹ :
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ) :
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]))
    (g.2.mono fun _v hv =>
      (mem_padicIntegralUnitsSubgroup_iff _ _).1 hv.2.2.1 |>.2)

@[simp]
theorem finiteAdelicCliffordGeneralSpinRestrictedFamilySimilitude_apply
    (g : V.FiniteAdelicCliffordGeneralSpinRestrictedFamily)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    finiteAdelicCliffordGeneralSpinHeightOneAlgHom v
        (V.finiteAdelicCliffordGeneralSpinRestrictedFamilySimilitude g) =
      ((g.1 v).similitude :
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) := by
  exact finiteAdeleOfCofinitelyIntegralPadicFamily_apply _ _ v

@[simp]
theorem finiteAdelicCliffordGeneralSpinRestrictedFamilyInverseSimilitude_apply
    (g : V.FiniteAdelicCliffordGeneralSpinRestrictedFamily)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    finiteAdelicCliffordGeneralSpinHeightOneAlgHom v
        (V.finiteAdelicCliffordGeneralSpinRestrictedFamilyInverseSimilitude g) =
      (((g.1 v).similitude⁻¹ :
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ) :
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) := by
  exact finiteAdeleOfCofinitelyIntegralPadicFamily_apply _ _ v

def finiteAdelicCliffordGeneralSpinRestrictedFamilySimilitudeUnit
    (g : V.FiniteAdelicCliffordGeneralSpinRestrictedFamily) :
    RationalFiniteAdeleˣ := by
  refine ⟨
    V.finiteAdelicCliffordGeneralSpinRestrictedFamilySimilitude g,
    V.finiteAdelicCliffordGeneralSpinRestrictedFamilyInverseSimilitude g,
    ?_, ?_⟩
  · ext v
    apply (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).injective
    calc
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v)
          ((V.finiteAdelicCliffordGeneralSpinRestrictedFamilySimilitude g *
            V.finiteAdelicCliffordGeneralSpinRestrictedFamilyInverseSimilitude g) v) =
          finiteAdelicCliffordGeneralSpinHeightOneAlgHom v
            (V.finiteAdelicCliffordGeneralSpinRestrictedFamilySimilitude g *
              V.finiteAdelicCliffordGeneralSpinRestrictedFamilyInverseSimilitude g) := rfl
      _ = finiteAdelicCliffordGeneralSpinHeightOneAlgHom v
            (V.finiteAdelicCliffordGeneralSpinRestrictedFamilySimilitude g) *
          finiteAdelicCliffordGeneralSpinHeightOneAlgHom v
            (V.finiteAdelicCliffordGeneralSpinRestrictedFamilyInverseSimilitude g) :=
        map_mul _ _ _
      _ = 1 := by
        rw [V.finiteAdelicCliffordGeneralSpinRestrictedFamilySimilitude_apply,
          V.finiteAdelicCliffordGeneralSpinRestrictedFamilyInverseSimilitude_apply]
        exact congrArg Units.val (mul_inv_cancel (g.1 v).similitude)
      _ = finiteAdelicCliffordGeneralSpinHeightOneAlgHom v 1 :=
        (map_one _).symm
      _ = (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v)
          ((1 : RationalFiniteAdele) v) := rfl
  · ext v
    apply (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).injective
    calc
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v)
          ((V.finiteAdelicCliffordGeneralSpinRestrictedFamilyInverseSimilitude g *
            V.finiteAdelicCliffordGeneralSpinRestrictedFamilySimilitude g) v) =
          finiteAdelicCliffordGeneralSpinHeightOneAlgHom v
            (V.finiteAdelicCliffordGeneralSpinRestrictedFamilyInverseSimilitude g *
              V.finiteAdelicCliffordGeneralSpinRestrictedFamilySimilitude g) := rfl
      _ = finiteAdelicCliffordGeneralSpinHeightOneAlgHom v
            (V.finiteAdelicCliffordGeneralSpinRestrictedFamilyInverseSimilitude g) *
          finiteAdelicCliffordGeneralSpinHeightOneAlgHom v
            (V.finiteAdelicCliffordGeneralSpinRestrictedFamilySimilitude g) :=
        map_mul _ _ _
      _ = 1 := by
        rw [V.finiteAdelicCliffordGeneralSpinRestrictedFamilyInverseSimilitude_apply,
          V.finiteAdelicCliffordGeneralSpinRestrictedFamilySimilitude_apply]
        exact congrArg Units.val (inv_mul_cancel (g.1 v).similitude)
      _ = finiteAdelicCliffordGeneralSpinHeightOneAlgHom v 1 :=
        (map_one _).symm
      _ = (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v)
          ((1 : RationalFiniteAdele) v) := rfl

/-! ## Assembled special-orthogonal coordinate -/

def finiteAdelicCliffordGeneralSpinRestrictedFamilySOFamily
    (g : V.FiniteAdelicCliffordGeneralSpinRestrictedFamily) :
    V.FiniteAdelicSpecialOrthogonalRestrictedFamily := by
  refine ⟨fun v => (g.1 v).matrixGroup, ?_⟩
  filter_upwards [g.2] with v hv
  have hp := (V.mem_padicSpecialOrthogonalIntegralSubgroup_iff
    (Rat.HeightOneSpectrum.primesEquiv v).1 (g.1 v).matrixGroup).1 hv.2.2.2
  constructor
  · intro i j
    apply (mem_adicCompletionIntegers_iff_padic v _).2
    simpa using hp.1 i j
  · intro i j
    apply (mem_adicCompletionIntegers_iff_padic v _).2
    simpa using hp.2 i j

def finiteAdelicCliffordGeneralSpinRestrictedFamilySO
    (g : V.FiniteAdelicCliffordGeneralSpinRestrictedFamily) :
    V.FiniteAdelicSpecialOrthogonalGroup :=
  V.finiteAdelicSpecialOrthogonalRestrictedFamilyAssembly
    (V.finiteAdelicCliffordGeneralSpinRestrictedFamilySOFamily g)

/-! ## Closed-coordinate assembly and local recovery -/

def finiteAdelicCliffordGeneralSpinRestrictedFamilyClosedCoordinate
    (g : V.FiniteAdelicCliffordGeneralSpinRestrictedFamily) :
    V.CliffordGeneralSpinClosedCoordinateSpace RationalFiniteAdele :=
  ((((V.finiteAdelicCliffordGeneralSpinRestrictedFamilyCliffordCoordinate g),
      V.finiteAdelicCliffordGeneralSpinRestrictedFamilyInverseCliffordCoordinate g),
    V.finiteAdelicCliffordGeneralSpinRestrictedFamilySimilitudeUnit g),
    V.finiteAdelicCliffordGeneralSpinRestrictedFamilySO g)

theorem finiteAdelicCliffordGeneralSpinRestrictedFamilyClifford_local
    (g : V.FiniteAdelicCliffordGeneralSpinRestrictedFamily)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    V.cliffordCoordinateBaseChangeMap
        (finiteAdelicCliffordGeneralSpinHeightOneAlgHom v)
        (V.cliffordGeneralSpinClosedCoordinateClifford RationalFiniteAdele
          (V.finiteAdelicCliffordGeneralSpinRestrictedFamilyClosedCoordinate g)) =
      ((g.1 v).cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) := by
  apply (V.cliffordCoordinateBaseChangeBasis
    ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).repr.injective
  ext s
  rw [V.cliffordCoordinateBaseChangeBasis_repr_map]
  simp only [cliffordGeneralSpinClosedCoordinateClifford,
    cliffordGeneralSpinCliffordOfCoordinates_repr,
    finiteAdelicCliffordGeneralSpinRestrictedFamilyClosedCoordinate]
  change finiteAdelicCliffordGeneralSpinHeightOneAlgHom v
      (V.finiteAdelicCliffordGeneralSpinRestrictedFamilyCliffordCoordinate g s) = _
  exact finiteAdeleOfCofinitelyIntegralPadicFamily_apply _ _ v

theorem finiteAdelicCliffordGeneralSpinRestrictedFamilyCliffordInv_local
    (g : V.FiniteAdelicCliffordGeneralSpinRestrictedFamily)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    V.cliffordCoordinateBaseChangeMap
        (finiteAdelicCliffordGeneralSpinHeightOneAlgHom v)
        (V.cliffordGeneralSpinClosedCoordinateCliffordInv RationalFiniteAdele
          (V.finiteAdelicCliffordGeneralSpinRestrictedFamilyClosedCoordinate g)) =
      (((g.1 v).cliffordUnit⁻¹ :
        (V.cliffordCoordinateBaseChangeAlgebra
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])ˣ) :
        V.cliffordCoordinateBaseChangeAlgebra
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) := by
  apply (V.cliffordCoordinateBaseChangeBasis
    ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).repr.injective
  ext s
  rw [V.cliffordCoordinateBaseChangeBasis_repr_map]
  simp only [cliffordGeneralSpinClosedCoordinateCliffordInv,
    cliffordGeneralSpinCliffordOfCoordinates_repr,
    finiteAdelicCliffordGeneralSpinRestrictedFamilyClosedCoordinate]
  change finiteAdelicCliffordGeneralSpinHeightOneAlgHom v
      (V.finiteAdelicCliffordGeneralSpinRestrictedFamilyInverseCliffordCoordinate g s) = _
  exact finiteAdeleOfCofinitelyIntegralPadicFamily_apply _ _ v

theorem finiteAdelicCliffordGeneralSpinRestrictedFamilySimilitude_local
    (g : V.FiniteAdelicCliffordGeneralSpinRestrictedFamily)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Units.map
        (finiteAdelicCliffordGeneralSpinHeightOneAlgHom v).toMonoidHom
        (V.finiteAdelicCliffordGeneralSpinRestrictedFamilySimilitudeUnit g) =
      (g.1 v).similitude := by
  apply Units.ext
  exact V.finiteAdelicCliffordGeneralSpinRestrictedFamilySimilitude_apply g v

theorem finiteAdelicCliffordGeneralSpinRestrictedFamilySO_local
    (g : V.FiniteAdelicCliffordGeneralSpinRestrictedFamily)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    V.finiteAdelicSpecialOrthogonalHeightOneComponent
        (V.finiteAdelicCliffordGeneralSpinRestrictedFamilySO g) v =
      (g.1 v).matrixGroup := by
  exact congrFun
    (V.finiteAdelicSpecialOrthogonalHeightOneComponents_assembly
      (V.finiteAdelicCliffordGeneralSpinRestrictedFamilySOFamily g)) v

/-! ## Detection of the intrinsic equations -/

theorem cliffordCoordinateBaseChange_eq_of_heightOne_maps_eq
    {x y : V.cliffordCoordinateBaseChangeAlgebra RationalFiniteAdele}
    (h : ∀ v,
      V.cliffordCoordinateBaseChangeMap
          (finiteAdelicCliffordGeneralSpinHeightOneAlgHom v) x =
        V.cliffordCoordinateBaseChangeMap
          (finiteAdelicCliffordGeneralSpinHeightOneAlgHom v) y) :
    x = y := by
  apply (V.cliffordCoordinateBaseChangeBasis RationalFiniteAdele).repr.injective
  ext s v
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  apply e.injective
  have hs := congrArg (fun z =>
    (V.cliffordCoordinateBaseChangeBasis
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).repr z s) (h v)
  simpa [V.cliffordCoordinateBaseChangeBasis_repr_map] using hs

theorem isCliffordGeneralSpinClosedCoordinate_restrictedFamily
    (g : V.FiniteAdelicCliffordGeneralSpinRestrictedFamily) :
    V.IsCliffordGeneralSpinClosedCoordinate RationalFiniteAdele
      (V.finiteAdelicCliffordGeneralSpinRestrictedFamilyClosedCoordinate g) := by
  let z := V.finiteAdelicCliffordGeneralSpinRestrictedFamilyClosedCoordinate g
  let x := V.cliffordGeneralSpinClosedCoordinateClifford RationalFiniteAdele z
  let y := V.cliffordGeneralSpinClosedCoordinateCliffordInv RationalFiniteAdele z
  change x * y = 1 ∧ y * x = 1 ∧
    V.cliffordCoordinateBaseChangeInvolute RationalFiniteAdele x = x ∧
    x * V.cliffordCoordinateBaseChangeReverse RationalFiniteAdele x =
      algebraMap RationalFiniteAdele
        (V.cliffordCoordinateBaseChangeAlgebra RationalFiniteAdele) z.1.2 ∧
    ∀ i, x * V.cliffordCoordinateBaseChangeVector RationalFiniteAdele i * y =
      ∑ j, z.2.1.1.1 j i •
        V.cliffordCoordinateBaseChangeVector RationalFiniteAdele j
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply V.cliffordCoordinateBaseChange_eq_of_heightOne_maps_eq
    intro v
    rw [map_mul, V.finiteAdelicCliffordGeneralSpinRestrictedFamilyClifford_local,
      V.finiteAdelicCliffordGeneralSpinRestrictedFamilyCliffordInv_local,
      map_one]
    exact congrArg Units.val (mul_inv_cancel (g.1 v).cliffordUnit)
  · apply V.cliffordCoordinateBaseChange_eq_of_heightOne_maps_eq
    intro v
    rw [map_mul, V.finiteAdelicCliffordGeneralSpinRestrictedFamilyCliffordInv_local,
      V.finiteAdelicCliffordGeneralSpinRestrictedFamilyClifford_local,
      map_one]
    exact congrArg Units.val (inv_mul_cancel (g.1 v).cliffordUnit)
  · apply V.cliffordCoordinateBaseChange_eq_of_heightOne_maps_eq
    intro v
    rw [V.cliffordCoordinateBaseChangeMap_involute,
      V.finiteAdelicCliffordGeneralSpinRestrictedFamilyClifford_local]
    exact (g.1 v).involute_eq
  · apply V.cliffordCoordinateBaseChange_eq_of_heightOne_maps_eq
    intro v
    rw [map_mul, V.cliffordCoordinateBaseChangeMap_reverse,
      V.finiteAdelicCliffordGeneralSpinRestrictedFamilyClifford_local,
      CliffordGeneralSpinIntrinsicPoint.cliffordCoordinateBaseChangeMap_algebraMap]
    have hnu := congrArg Units.val
      (V.finiteAdelicCliffordGeneralSpinRestrictedFamilySimilitude_local g v)
    change finiteAdelicCliffordGeneralSpinHeightOneAlgHom v (↑z.1.2) =
      ↑(g.1 v).similitude at hnu
    rw [hnu]
    exact (g.1 v).mul_reverse_eq
  · intro i
    change x * V.cliffordCoordinateBaseChangeVector RationalFiniteAdele i * y =
      V.cliffordCoordinateBaseChangeVectorOfCoordinates RationalFiniteAdele
        (fun j => z.2.1.1.1 j i)
    apply V.cliffordCoordinateBaseChange_eq_of_heightOne_maps_eq
    intro v
    rw [map_mul, map_mul, V.cliffordCoordinateBaseChangeMap_vector,
      V.finiteAdelicCliffordGeneralSpinRestrictedFamilyClifford_local,
      V.finiteAdelicCliffordGeneralSpinRestrictedFamilyCliffordInv_local,
      V.cliffordCoordinateBaseChangeMap_vectorOfCoordinates]
    have hso := V.finiteAdelicCliffordGeneralSpinRestrictedFamilySO_local g v
    have hentry (j : Fin n) :
        finiteAdelicCliffordGeneralSpinHeightOneAlgHom v
            ((V.finiteAdelicCliffordGeneralSpinRestrictedFamilySO g).1.1.1 j i) =
          (g.1 v).matrixGroup.1.1.1 j i := by
      calc
        finiteAdelicCliffordGeneralSpinHeightOneAlgHom v
            ((V.finiteAdelicCliffordGeneralSpinRestrictedFamilySO g).1.1.1 j i) =
            (Matrix.GeneralLinearGroup.map
              ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toRingEquiv.toRingHom.comp
                (RestrictedProduct.evalRingHom
                  (fun w : IsDedekindDomain.HeightOneSpectrum ℤ ↦
                    w.adicCompletion ℚ) v))
              (V.finiteAdelicCliffordGeneralSpinRestrictedFamilySO g).1.1).1 j i := rfl
        _ = (V.finiteAdelicSpecialOrthogonalHeightOneComponent
              (V.finiteAdelicCliffordGeneralSpinRestrictedFamilySO g) v).1.1.1 j i :=
          congrArg (fun m => m j i)
            (V.finiteAdelicSpecialOrthogonalHeightOneComponent_matrix
              (V.finiteAdelicCliffordGeneralSpinRestrictedFamilySO g) v).symm
        _ = (g.1 v).matrixGroup.1.1.1 j i :=
          congrArg (fun q => q.1.1.1 j i) hso
    calc
      ((g.1 v).cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) *
          V.cliffordCoordinateBaseChangeVector
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] i *
          (((g.1 v).cliffordUnit⁻¹ :
            (V.cliffordCoordinateBaseChangeAlgebra
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])ˣ) :
            V.cliffordCoordinateBaseChangeAlgebra
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) =
          V.cliffordCoordinateBaseChangeVectorOfCoordinates
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
            (fun j => (g.1 v).matrixGroup.1.1.1 j i) := by
        rw [(g.1 v).vectorGraph]
        rfl
      _ = V.cliffordCoordinateBaseChangeVectorOfCoordinates
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
            (fun j => finiteAdelicCliffordGeneralSpinHeightOneAlgHom v
              (z.2.1.1.1 j i)) := by
        congr 2
        funext j
        exact (hentry j).symm

/-! ## Assembly equivalence -/

def finiteAdelicCliffordGeneralSpinRestrictedFamilyAssembly
    (g : V.FiniteAdelicCliffordGeneralSpinRestrictedFamily) :
    V.FiniteAdelicCliffordGeneralSpinGroup :=
  Classical.choose
    ((Set.ext_iff.1 (V.range_cliffordGeneralSpinClosedCoordinateMap
      RationalFiniteAdele)
      (V.finiteAdelicCliffordGeneralSpinRestrictedFamilyClosedCoordinate g)).2
      (V.isCliffordGeneralSpinClosedCoordinate_restrictedFamily g))

theorem finiteAdelicCliffordGeneralSpinRestrictedFamilyAssembly_closedCoordinate
    (g : V.FiniteAdelicCliffordGeneralSpinRestrictedFamily) :
    V.cliffordGeneralSpinClosedCoordinateMap RationalFiniteAdele
      (V.finiteAdelicCliffordGeneralSpinRestrictedFamilyAssembly g) =
        V.finiteAdelicCliffordGeneralSpinRestrictedFamilyClosedCoordinate g :=
  Classical.choose_spec
    ((Set.ext_iff.1 (V.range_cliffordGeneralSpinClosedCoordinateMap
      RationalFiniteAdele)
      (V.finiteAdelicCliffordGeneralSpinRestrictedFamilyClosedCoordinate g)).2
      (V.isCliffordGeneralSpinClosedCoordinate_restrictedFamily g))

theorem finiteAdelicCliffordGeneralSpinHeightOneComponents_assembly
    (g : V.FiniteAdelicCliffordGeneralSpinRestrictedFamily) :
    V.finiteAdelicCliffordGeneralSpinHeightOneComponentsHom
      (V.finiteAdelicCliffordGeneralSpinRestrictedFamilyAssembly g) = g.1 := by
  funext v
  apply CliffordGeneralSpinIntrinsicPoint.ext_cliffordUnit V _
  apply Units.ext
  have hz := V.finiteAdelicCliffordGeneralSpinRestrictedFamilyAssembly_closedCoordinate g
  have hx0 := congrArg
    (V.cliffordGeneralSpinClosedCoordinateClifford RationalFiniteAdele) hz
  have hx :
    ((V.finiteAdelicCliffordGeneralSpinRestrictedFamilyAssembly g).cliffordUnit :
      V.cliffordCoordinateBaseChangeAlgebra RationalFiniteAdele) =
      V.cliffordGeneralSpinClosedCoordinateClifford RationalFiniteAdele
        (V.finiteAdelicCliffordGeneralSpinRestrictedFamilyClosedCoordinate g) := by
    exact (V.cliffordGeneralSpinCliffordOfCoordinates_repr_self
      RationalFiniteAdele _).symm.trans hx0
  change V.cliffordCoordinateBaseChangeMap
      (finiteAdelicCliffordGeneralSpinHeightOneAlgHom v)
      ((V.finiteAdelicCliffordGeneralSpinRestrictedFamilyAssembly g).cliffordUnit :
        V.cliffordCoordinateBaseChangeAlgebra RationalFiniteAdele) =
    ((g.1 v).cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
  rw [hx]
  exact V.finiteAdelicCliffordGeneralSpinRestrictedFamilyClifford_local g v

theorem finiteAdelicCliffordGeneralSpinRestrictedFamilyAssembly_components
    (x : V.FiniteAdelicCliffordGeneralSpinGroup) :
    V.finiteAdelicCliffordGeneralSpinRestrictedFamilyAssembly
      (V.finiteAdelicCliffordGeneralSpinRestrictedFamilyMap x) = x := by
  apply V.finiteAdelicCliffordGeneralSpinHeightOneComponentsHom_injective
  exact V.finiteAdelicCliffordGeneralSpinHeightOneComponents_assembly
    (V.finiteAdelicCliffordGeneralSpinRestrictedFamilyMap x)

def finiteAdelicCliffordGeneralSpinRestrictedFamilyEquiv :
    V.FiniteAdelicCliffordGeneralSpinGroup ≃
      V.FiniteAdelicCliffordGeneralSpinRestrictedFamily where
  toFun := V.finiteAdelicCliffordGeneralSpinRestrictedFamilyMap
  invFun := V.finiteAdelicCliffordGeneralSpinRestrictedFamilyAssembly
  left_inv := V.finiteAdelicCliffordGeneralSpinRestrictedFamilyAssembly_components
  right_inv := by
    intro g
    apply Subtype.ext
    exact V.finiteAdelicCliffordGeneralSpinHeightOneComponents_assembly g

end RationalQuadraticSpaceMatrix

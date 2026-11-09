import SMSFormula.RationalCliffordGeneralSpinFullAdelicShell
import SMSFormula.RationalCliffordGeneralSpinBlockFullAdelicStabilizerHaar
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# The full-adelic block shell as a homogeneous space

The full-adelic intrinsic `GSpin` orbit of the added nonisotropic coordinate
factors through the right-coset quotient by the certified complement
stabilizer.  The induced map is a continuous bijection onto the existing block
shell.

This is the carrier-level statement needed to construct a shell measure and
prove a Weil integral.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

local instance fullAdelicShellInfiniteT2Space : T2Space RationalInfiniteAdele :=
  rationalInfiniteAdeleHomeomorphReal.symm.t2Space

local instance fullAdelicShellFiniteT2Space : T2Space RationalFiniteAdele :=
  RestrictedProduct.instT2Space

local instance fullAdelicShellT2Space : T2Space RationalAdele := by
  change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
  infer_instance

/-- The right-coset homogeneous space of full-adelic block `GSpin` by the
literal fixed-last-vector complement stabilizer. -/
abbrev FullAdelicNonisotropicLastShellHomogeneousSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :=
  (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup ⧸
    W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      a ha RationalAdele

/-- The vector underlying the shell orbit of a product is the represented
action of the first factor on the shell orbit of the second factor. -/
theorem CliffordGeneralSpinIntrinsicPoint.coe_nonisotropicLastShellOrbitMap_mul
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (g h : (W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup) :
    (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
        W a ha RationalAdele (g * h)).1 =
      g.matrixPoint.1 *ᵥ
        (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
          W a ha RationalAdele h).1 := by
  change (g * h).matrixPoint.1 *ᵥ lastCoordinateVector =
    g.matrixPoint.1 *ᵥ (h.matrixPoint.1 *ᵥ lastCoordinateVector)
  rw [Matrix.mulVec_mulVec]
  congr 1

/-- Right multiplication by the literal complement stabilizer leaves the
full-adelic block-shell orbit unchanged. -/
theorem CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap_mul_of_mem_stabilizer
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (g h : (W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup)
    (hh : h ∈ W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      a ha RationalAdele) :
    CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
        W a ha RationalAdele (g * h) =
      CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
        W a ha RationalAdele g := by
  apply Subtype.ext
  rw [CliffordGeneralSpinIntrinsicPoint.coe_nonisotropicLastShellOrbitMap_mul]
  have hlast :=
    (CliffordGeneralSpinIntrinsicPoint.fullAdelic_nonisotropicLastShellOrbitMap_eq_last_iff
      W a ha h).2 hh
  rw [congrArg Subtype.val hlast]
  rfl

/-- Two full-adelic block `GSpin` points determine the same shell point
exactly when they represent the same right coset of the complement
stabilizer. -/
theorem CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap_leftRel_iff
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (g h : (W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup) :
    QuotientGroup.leftRel
        (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
          a ha RationalAdele) g h ↔
      CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
          W a ha RationalAdele g =
        CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
          W a ha RationalAdele h := by
  rw [QuotientGroup.leftRel_apply]
  constructor
  · intro hrel
    have hh : h = g * (g⁻¹ * h) := by group
    rw [hh]
    exact
      (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap_mul_of_mem_stabilizer
        W a ha g (g⁻¹ * h) hrel).symm
  · intro horbit
    apply
      (CliffordGeneralSpinIntrinsicPoint.fullAdelic_nonisotropicLastShellOrbitMap_eq_last_iff
        W a ha (g⁻¹ * h)).1
    apply Subtype.ext
    calc
      (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
          W a ha RationalAdele (g⁻¹ * h)).1 =
          g⁻¹.matrixPoint.1 *ᵥ
            (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
              W a ha RationalAdele h).1 :=
        CliffordGeneralSpinIntrinsicPoint.coe_nonisotropicLastShellOrbitMap_mul
          W a ha g⁻¹ h
      _ = g⁻¹.matrixPoint.1 *ᵥ
            (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
              W a ha RationalAdele g).1 := by rw [horbit]
      _ = (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
          W a ha RationalAdele (g⁻¹ * g)).1 :=
        (CliffordGeneralSpinIntrinsicPoint.coe_nonisotropicLastShellOrbitMap_mul
          W a ha g⁻¹ g).symm
      _ = lastCoordinateVector := by
        rw [inv_mul_cancel]
        exact congrArg Subtype.val
          ((CliffordGeneralSpinIntrinsicPoint.fullAdelic_nonisotropicLastShellOrbitMap_eq_last_iff
            W a ha 1).2 (Subgroup.one_mem _))

/-- The actual full-adelic shell orbit map induced on the complement
stabilizer quotient. -/
def fullAdelicNonisotropicLastShellQuotientMap
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha →
      W.nonisotropicLastQuadraticShell a ha RationalAdele :=
  Quotient.lift
    (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
      W a ha RationalAdele)
    fun g h hrel =>
      (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap_leftRel_iff
        W a ha g h).1 hrel

@[simp]
theorem fullAdelicNonisotropicLastShellQuotientMap_mk
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (g : (W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup) :
    W.fullAdelicNonisotropicLastShellQuotientMap a ha (QuotientGroup.mk g) =
      CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
        W a ha RationalAdele g :=
  rfl

/-- The induced quotient-to-shell map is injective. -/
theorem injective_fullAdelicNonisotropicLastShellQuotientMap
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    Function.Injective
      (W.fullAdelicNonisotropicLastShellQuotientMap a ha) := by
  intro q r hqr
  induction q using Quotient.inductionOn' with
  | _ g =>
      induction r using Quotient.inductionOn' with
      | _ h =>
          apply Quotient.sound'
          exact
            (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap_leftRel_iff
              W a ha g h).2 hqr

/-- The induced quotient-to-shell map is surjective in positive complement
rank. -/
theorem surjective_fullAdelicNonisotropicLastShellQuotientMap
    (W : RationalQuadraticSpaceMatrix n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0) :
    Function.Surjective
      (W.fullAdelicNonisotropicLastShellQuotientMap a ha) := by
  intro y
  obtain ⟨g, hg⟩ :=
    CliffordGeneralSpinIntrinsicPoint.fullAdelic_nonisotropicLastShellOrbitMap_surjective
      W a ha y
  exact ⟨QuotientGroup.mk g, hg⟩

/-- The equivalence from the actual full-adelic homogeneous
space to the existing nonisotropic shell. -/
def fullAdelicNonisotropicLastShellQuotientEquiv
    (W : RationalQuadraticSpaceMatrix n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0) :
    W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha ≃
      W.nonisotropicLastQuadraticShell a ha RationalAdele :=
  Equiv.ofBijective
    (W.fullAdelicNonisotropicLastShellQuotientMap a ha)
    ⟨W.injective_fullAdelicNonisotropicLastShellQuotientMap a ha,
      W.surjective_fullAdelicNonisotropicLastShellQuotientMap a ha⟩

@[simp]
theorem fullAdelicNonisotropicLastShellQuotientEquiv_mk
    (W : RationalQuadraticSpaceMatrix n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0)
    (g : (W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup) :
    W.fullAdelicNonisotropicLastShellQuotientEquiv a ha
        (QuotientGroup.mk g) =
      CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
        W a ha RationalAdele g :=
  rfl

/-- The actual full-adelic shell orbit map is continuous. -/
theorem continuous_fullAdelic_nonisotropicLastShellOrbitMap
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    Continuous
      (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
        W a ha RationalAdele) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  simpa [CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap,
    Matrix.mulVec, dotProduct, lastCoordinateVector, Pi.single_apply] using
    ((W.nonisotropicLastExtension a ha)
      |>.continuous_cliffordGeneralSpinMatrixCoordinate
        RationalAdele i (Fin.last n))

/-- The induced homogeneous-space map is continuous for Mathlib's standard
right-coset quotient topology. -/
theorem continuous_fullAdelicNonisotropicLastShellQuotientMap
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    Continuous (W.fullAdelicNonisotropicLastShellQuotientMap a ha) := by
  exact
    (W.continuous_fullAdelic_nonisotropicLastShellOrbitMap a ha).quotient_lift _

end RationalQuadraticSpaceMatrix

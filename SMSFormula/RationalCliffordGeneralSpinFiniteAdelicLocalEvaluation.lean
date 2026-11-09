import SMSFormula.RationalCliffordGeneralSpinPadicIntegralCoordinates
import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicLocalEvaluation

/-!
# Finite-adelic local evaluation for intrinsic general Spin

Finite-adelic intrinsic `GSpin` points evaluate continuously at every
height-one place.  Their Clifford unit and inverse, similitude and inverse,
and orthogonal matrix and inverse satisfy the literal compact-open integral
coordinate condition at cofinitely many places.  This supplies the forward
map into the restricted family used by the crossed integral.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped Matrix RestrictedProduct

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

local instance finiteAdelicGeneralSpinLocalEvaluationPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

abbrev HeightOnePadicCliffordGeneralSpinGroup
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :=
  V.PadicCliffordGeneralSpinGroup
    (Rat.HeightOneSpectrum.primesEquiv v).1

/-- Evaluate finite-adelic coefficients at a height-one place. -/
def finiteAdelicCliffordGeneralSpinHeightOneAlgHom
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    RationalFiniteAdele →ₐ[ℚ]
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] :=
  finiteAdelicCliffordSpinCandidateHeightOneAlgHom v

@[simp]
theorem finiteAdelicCliffordGeneralSpinHeightOneAlgHom_apply
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (a : RationalFiniteAdele) :
    finiteAdelicCliffordGeneralSpinHeightOneAlgHom v a =
      Rat.HeightOneSpectrum.adicCompletion.padicEquiv v (a v) :=
  rfl

/-- Evaluate an intrinsic finite-adelic `GSpin` point at one height-one
place. -/
def finiteAdelicCliffordGeneralSpinHeightOneComponentHom
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
  V.FiniteAdelicCliffordGeneralSpinGroup →*
      V.HeightOnePadicCliffordGeneralSpinGroup v :=
  CliffordGeneralSpinIntrinsicPoint.mapGroupHom V
    (finiteAdelicCliffordGeneralSpinHeightOneAlgHom v)

theorem continuous_finiteAdelicCliffordGeneralSpinHeightOneAlgHom
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Continuous (finiteAdelicCliffordGeneralSpinHeightOneAlgHom v) :=
  continuous_finiteAdelicCliffordSpinCandidateHeightOneAlgHom v

theorem continuous_finiteAdelicCliffordGeneralSpinHeightOneComponent
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Continuous (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v) :=
  V.continuous_cliffordGeneralSpinMapGroupHom
    (finiteAdelicCliffordGeneralSpinHeightOneAlgHom v)
    (continuous_finiteAdelicCliffordGeneralSpinHeightOneAlgHom v)

abbrev HeightOnePadicCliffordGeneralSpinGroupProduct :=
  (v : IsDedekindDomain.HeightOneSpectrum ℤ) →
    V.HeightOnePadicCliffordGeneralSpinGroup v

def finiteAdelicCliffordGeneralSpinHeightOneComponentsHom :
    V.FiniteAdelicCliffordGeneralSpinGroup →*
      V.HeightOnePadicCliffordGeneralSpinGroupProduct where
  toFun x v := V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v x
  map_one' := by
    funext v
    exact (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v).map_one
  map_mul' x y := by
    funext v
    exact (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v).map_mul x y

theorem continuous_finiteAdelicCliffordGeneralSpinHeightOneComponents :
    Continuous V.finiteAdelicCliffordGeneralSpinHeightOneComponentsHom :=
  continuous_pi fun v =>
    V.continuous_finiteAdelicCliffordGeneralSpinHeightOneComponent v

theorem finiteAdelicCliffordGeneralSpinHeightOneComponentsHom_injective :
    Function.Injective
      V.finiteAdelicCliffordGeneralSpinHeightOneComponentsHom := by
  intro x y hxy
  apply CliffordGeneralSpinIntrinsicPoint.ext_cliffordUnit V RationalFiniteAdele
  apply Units.ext
  apply (V.cliffordCoordinateBaseChangeBasis RationalFiniteAdele).repr.injective
  ext s v
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  apply e.injective
  have hv := congrFun hxy v
  have hs := congrArg (fun z =>
    (V.cliffordCoordinateBaseChangeBasis
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).repr
        (z.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) s) hv
  simpa [finiteAdelicCliffordGeneralSpinHeightOneComponentsHom,
    finiteAdelicCliffordGeneralSpinHeightOneComponentHom,
    finiteAdelicCliffordGeneralSpinHeightOneAlgHom_apply,
    V.cliffordCoordinateBaseChangeBasis_repr_map] using hs

/-- Cofinite integrality of a family of local intrinsic `GSpin` points. -/
def IsFiniteAdelicCliffordGeneralSpinRestrictedFamily
    (g : V.HeightOnePadicCliffordGeneralSpinGroupProduct) : Prop :=
  ∀ᶠ v in Filter.cofinite,
    V.PadicCliffordGeneralSpinIsIntegral
      (Rat.HeightOneSpectrum.primesEquiv v).1 (g v)

theorem finiteAdelicCliffordGeneralSpinHeightOneComponents_isRestrictedFamily
    (x : V.FiniteAdelicCliffordGeneralSpinGroup) :
    V.IsFiniteAdelicCliffordGeneralSpinRestrictedFamily
      (V.finiteAdelicCliffordGeneralSpinHeightOneComponentsHom x) := by
  have hclifford :
      ∀ᶠ v in Filter.cofinite, ∀ s,
        (V.cliffordCoordinateBaseChangeBasis RationalFiniteAdele).repr
          (x.cliffordUnit :
            V.cliffordCoordinateBaseChangeAlgebra RationalFiniteAdele) s v ∈
          v.adicCompletionIntegers ℚ := by
    rw [Filter.eventually_all]
    intro s
    exact ((V.cliffordCoordinateBaseChangeBasis RationalFiniteAdele).repr
      (x.cliffordUnit :
        V.cliffordCoordinateBaseChangeAlgebra RationalFiniteAdele) s).2
  have hcliffordInv :
      ∀ᶠ v in Filter.cofinite, ∀ s,
        (V.cliffordCoordinateBaseChangeBasis RationalFiniteAdele).repr
          (((x.cliffordUnit⁻¹ :
            (V.cliffordCoordinateBaseChangeAlgebra RationalFiniteAdele)ˣ) :
              V.cliffordCoordinateBaseChangeAlgebra RationalFiniteAdele)) s v ∈
          v.adicCompletionIntegers ℚ := by
    rw [Filter.eventually_all]
    intro s
    exact ((V.cliffordCoordinateBaseChangeBasis RationalFiniteAdele).repr
      (((x.cliffordUnit⁻¹ :
        (V.cliffordCoordinateBaseChangeAlgebra RationalFiniteAdele)ˣ) :
          V.cliffordCoordinateBaseChangeAlgebra RationalFiniteAdele)) s).2
  have hnu : ∀ᶠ v in Filter.cofinite,
      (x.similitude : RationalFiniteAdele) v ∈
        v.adicCompletionIntegers ℚ := x.similitude.1.2
  have hnuInv : ∀ᶠ v in Filter.cofinite,
      ((x.similitude⁻¹ : RationalFiniteAdeleˣ) : RationalFiniteAdele) v ∈
        v.adicCompletionIntegers ℚ := x.similitude⁻¹.1.2
  have hmatrix : ∀ᶠ v in Filter.cofinite, ∀ i j,
      x.matrixGroup.1.1.1 i j v ∈ v.adicCompletionIntegers ℚ := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    exact (x.matrixGroup.1.1.1 i j).2
  have hmatrixInv : ∀ᶠ v in Filter.cofinite, ∀ i j,
      (x.matrixGroup.1.1⁻¹).1 i j v ∈ v.adicCompletionIntegers ℚ := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    exact ((x.matrixGroup.1.1⁻¹).1 i j).2
  filter_upwards [hclifford, hcliffordInv, hnu, hnuInv,
    hmatrix, hmatrixInv] with v hcv hciv hnv hniv hmv hmiv
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  unfold PadicCliffordGeneralSpinIsIntegral
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    simpa [finiteAdelicCliffordGeneralSpinHeightOneComponentsHom,
      finiteAdelicCliffordGeneralSpinHeightOneComponentHom,
      V.cliffordCoordinateBaseChangeBasis_repr_map] using
        (mem_adicCompletionIntegers_iff_padic v _).1 (hcv s)
  · intro s
    change (V.cliffordCoordinateBaseChangeBasis
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).repr
        (((V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v x)⁻¹).cliffordUnit :
          V.cliffordCoordinateBaseChangeAlgebra
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) s ∈ PadicInt.subring _
    rw [← (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v).map_inv]
    simpa [
      finiteAdelicCliffordGeneralSpinHeightOneComponentHom,
      V.cliffordCoordinateBaseChangeBasis_repr_map] using
        (mem_adicCompletionIntegers_iff_padic v _).1 (hciv s)
  · rw [mem_padicIntegralUnitsSubgroup_iff]
    constructor
    · simpa [finiteAdelicCliffordGeneralSpinHeightOneComponentsHom,
        finiteAdelicCliffordGeneralSpinHeightOneComponentHom] using
          (mem_adicCompletionIntegers_iff_padic v _).1 hnv
    · change
        (((V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v x)⁻¹).similitude :
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) ∈ PadicInt.subring _
      rw [← (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v).map_inv]
      change finiteAdelicCliffordGeneralSpinHeightOneAlgHom v
          (((x.similitude⁻¹ : RationalFiniteAdeleˣ) : RationalFiniteAdele)) ∈
        PadicInt.subring _
      change Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
          (((x.similitude⁻¹ : RationalFiniteAdeleˣ) : RationalFiniteAdele) v) ∈
        PadicInt.subring _
      exact (mem_adicCompletionIntegers_iff_padic v _).1 hniv
  · rw [V.mem_padicSpecialOrthogonalIntegralSubgroup_iff]
    constructor
    · intro i j
      simpa [finiteAdelicCliffordGeneralSpinHeightOneComponentsHom,
        finiteAdelicCliffordGeneralSpinHeightOneComponentHom] using
          (mem_adicCompletionIntegers_iff_padic v _).1 (hmv i j)
    · intro i j
      change
        ((V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v x)⁻¹).matrixGroup.1.1.1
          i j ∈ PadicInt.subring _
      rw [← (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v).map_inv]
      change finiteAdelicCliffordGeneralSpinHeightOneAlgHom v
          ((x.matrixGroup.1.1⁻¹).1 i j) ∈ PadicInt.subring _
      simpa using
          (mem_adicCompletionIntegers_iff_padic v _).1 (hmiv i j)

abbrev FiniteAdelicCliffordGeneralSpinRestrictedFamily :=
  {g : V.HeightOnePadicCliffordGeneralSpinGroupProduct //
    V.IsFiniteAdelicCliffordGeneralSpinRestrictedFamily g}

def finiteAdelicCliffordGeneralSpinRestrictedFamilyMap
    (x : V.FiniteAdelicCliffordGeneralSpinGroup) :
    V.FiniteAdelicCliffordGeneralSpinRestrictedFamily :=
  ⟨V.finiteAdelicCliffordGeneralSpinHeightOneComponentsHom x,
    V.finiteAdelicCliffordGeneralSpinHeightOneComponents_isRestrictedFamily x⟩

theorem continuous_finiteAdelicCliffordGeneralSpinRestrictedFamilyMap :
    Continuous V.finiteAdelicCliffordGeneralSpinRestrictedFamilyMap :=
  (V.continuous_finiteAdelicCliffordGeneralSpinHeightOneComponents).subtype_mk _

theorem finiteAdelicCliffordGeneralSpinRestrictedFamilyMap_injective :
    Function.Injective
      V.finiteAdelicCliffordGeneralSpinRestrictedFamilyMap := by
  intro x y hxy
  apply V.finiteAdelicCliffordGeneralSpinHeightOneComponentsHom_injective
  exact congrArg Subtype.val hxy

end RationalQuadraticSpaceMatrix

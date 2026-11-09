import SMSFormula.RationalCliffordSpinCandidateAdelicProduct
import SMSFormula.RationalSpecialOrthogonalFiniteAdelicLocalEvaluationCarrier

/-!
# Finite-adelic local evaluation for Clifford--Spin candidate points

Finite-adelic candidate points are evaluated at every height-one prime of
`ℤ` by the corresponding finite-adele evaluation map followed by the standard
p-adic equivalence.  The resulting point maps are continuous group
homomorphisms, commute with the candidate-to-special-orthogonal morphism, and
jointly determine the original finite-adelic point.

The image satisfies the literal cofinite integrality condition on every
Clifford and matrix coordinate of both the point and its inverse.  This is the
restricted-family precursor only: no reverse assembly, topology comparison,
local compactness, or measure is constructed here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped Matrix RestrictedProduct

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

local instance finiteAdelicSpinLocalEvaluationPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-! ## One height-one component -/

/-- The Spin-candidate point group over the standard p-adic field associated
to a height-one prime of `ℤ`. -/
abbrev HeightOnePadicCliffordSpinCandidateGroup
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :=
  V.CliffordSpinCandidateGroup
    ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]

/-- The rational-algebra map evaluating a finite adele at a height-one place
and identifying its completion with the standard p-adic field. -/
def finiteAdelicCliffordSpinCandidateHeightOneAlgHom
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    RationalFiniteAdele →ₐ[ℚ]
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] :=
  let φ : RationalFiniteAdele →+*
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] :=
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toRingEquiv.toRingHom.comp
      (RestrictedProduct.evalRingHom
        (fun w : IsDedekindDomain.HeightOneSpectrum ℤ ↦
          w.adicCompletion ℚ) v)
  φ.toRatAlgHom

/-- Evaluate a finite-adelic candidate point at one height-one place. -/
def finiteAdelicCliffordSpinCandidateHeightOneComponentHom
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    V.FiniteAdelicCliffordSpinCandidateGroup →*
      V.HeightOnePadicCliffordSpinCandidateGroup v :=
  V.cliffordSpinCandidateGroupMap
    (finiteAdelicCliffordSpinCandidateHeightOneAlgHom v)

@[simp]
theorem finiteAdelicCliffordSpinCandidateHeightOneComponentHom_apply
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (x : V.FiniteAdelicCliffordSpinCandidateGroup) :
    V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v x =
      (finiteAdelicCliffordSpinCandidateHeightOneAlgHom v).comp x :=
  rfl

/-- The height-one scalar map is continuous. -/
theorem continuous_finiteAdelicCliffordSpinCandidateHeightOneAlgHom
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Continuous (finiteAdelicCliffordSpinCandidateHeightOneAlgHom v) := by
  let ev : RationalFiniteAdele →+* v.adicCompletion ℚ :=
    RestrictedProduct.evalRingHom
      (fun w : IsDedekindDomain.HeightOneSpectrum ℤ ↦
        w.adicCompletion ℚ) v
  have hev : Continuous (ev : RationalFiniteAdele → v.adicCompletion ℚ) := by
    change Continuous (fun x : RationalFiniteAdele => x v)
    exact RestrictedProduct.continuous_eval v
  exact
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).continuous.comp hev

/-- Evaluation at one height-one place is continuous. -/
theorem continuous_finiteAdelicCliffordSpinCandidateHeightOneComponent
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Continuous
      (V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v) :=
  V.continuous_cliffordSpinCandidateGroupMap
    (finiteAdelicCliffordSpinCandidateHeightOneAlgHom v)
    (continuous_finiteAdelicCliffordSpinCandidateHeightOneAlgHom v)

/-- Height-one evaluation commutes with the completed candidate-to-`SO`
homomorphism. -/
theorem finiteAdelicCliffordSpinCandidateHeightOneComponent_toSpecialOrthogonal
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (x : V.FiniteAdelicCliffordSpinCandidateGroup) :
    V.cliffordSpinCandidateGroupToSpecialOrthogonal
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
        (V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v x) =
      V.finiteAdelicSpecialOrthogonalHeightOneComponent
        (V.finiteAdelicCliffordSpinCandidateToSpecialOrthogonalHom x) v := by
  change V.cliffordSpinCandidateGroupToSpecialOrthogonal
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
      (V.cliffordSpinCandidateGroupMap
        (finiteAdelicCliffordSpinCandidateHeightOneAlgHom v) x) = _
  rw [V.cliffordSpinCandidateGroupToSpecialOrthogonal_map]
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  rw [V.finiteAdelicSpecialOrthogonalHeightOneComponent_matrix,
    V.specialOrthogonalMatrixGroupMap_apply_matrix]
  rfl

/-! ## Simultaneous evaluation -/

/-- The dependent product of all height-one p-adic candidate point groups. -/
abbrev HeightOnePadicCliffordSpinCandidateGroupProduct :=
  (v : IsDedekindDomain.HeightOneSpectrum ℤ) →
    V.HeightOnePadicCliffordSpinCandidateGroup v

/-- Simultaneous height-one evaluation as a group homomorphism. -/
def finiteAdelicCliffordSpinCandidateHeightOneComponentsHom :
    V.FiniteAdelicCliffordSpinCandidateGroup →*
      V.HeightOnePadicCliffordSpinCandidateGroupProduct where
  toFun x v :=
    V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v x
  map_one' := by
    funext v
    exact
      (V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v).map_one
  map_mul' x y := by
    funext v
    exact
      (V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v).map_mul x y

/-- Simultaneous height-one evaluation is continuous. -/
theorem continuous_finiteAdelicCliffordSpinCandidateHeightOneComponents :
    Continuous V.finiteAdelicCliffordSpinCandidateHeightOneComponentsHom :=
  continuous_pi fun v =>
    V.continuous_finiteAdelicCliffordSpinCandidateHeightOneComponent v

/-- A finite-adelic candidate point is determined by all of its height-one
p-adic components. -/
theorem finiteAdelicCliffordSpinCandidateHeightOneComponentsHom_injective :
    Function.Injective
      V.finiteAdelicCliffordSpinCandidateHeightOneComponentsHom := by
  intro x y hxy
  ext a v
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  apply e.injective
  have hv := congrFun hxy v
  change e (x a v) = e (y a v)
  exact DFunLike.congr_fun hv a

/-! ## Restricted-family image condition -/

/-- A local candidate point is integral at a height-one place when every
finite Clifford and matrix coordinate of both it and its inverse is integral
after transport back to the completion used by the finite adeles. -/
def HeightOnePadicCliffordSpinCandidateIsIntegral
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (g : V.HeightOnePadicCliffordSpinCandidateGroup v) : Prop :=
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  (∀ s, e.symm (g (V.cliffordSpinCandidateCliffordCoordinate s)) ∈
      v.adicCompletionIntegers ℚ) ∧
    (∀ i j, e.symm (g (V.cliffordSpinCandidateMatrixCoordinate i j)) ∈
      v.adicCompletionIntegers ℚ) ∧
    (∀ s, e.symm (g⁻¹ (V.cliffordSpinCandidateCliffordCoordinate s)) ∈
      v.adicCompletionIntegers ℚ) ∧
    (∀ i j, e.symm (g⁻¹ (V.cliffordSpinCandidateMatrixCoordinate i j)) ∈
      v.adicCompletionIntegers ℚ)

/-- The literal restricted-family predicate for p-adic candidate points. -/
def IsFiniteAdelicCliffordSpinCandidateRestrictedFamily
    (g : V.HeightOnePadicCliffordSpinCandidateGroupProduct) : Prop :=
  ∀ᶠ v in Filter.cofinite,
    V.HeightOnePadicCliffordSpinCandidateIsIntegral v (g v)

/-- Simultaneous evaluation of a finite-adelic candidate point satisfies the
cofinite integrality condition on the point and its inverse. -/
theorem finiteAdelicCliffordSpinCandidateHeightOneComponents_isRestrictedFamily
    (x : V.FiniteAdelicCliffordSpinCandidateGroup) :
    V.IsFiniteAdelicCliffordSpinCandidateRestrictedFamily
      (V.finiteAdelicCliffordSpinCandidateHeightOneComponentsHom x) := by
  have hclifford :
      ∀ᶠ v in Filter.cofinite,
        ∀ s, x (V.cliffordSpinCandidateCliffordCoordinate s) v ∈
          v.adicCompletionIntegers ℚ := by
    rw [Filter.eventually_all]
    intro s
    exact (x (V.cliffordSpinCandidateCliffordCoordinate s)).2
  have hmatrix :
      ∀ᶠ v in Filter.cofinite,
        ∀ i j, x (V.cliffordSpinCandidateMatrixCoordinate i j) v ∈
          v.adicCompletionIntegers ℚ := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    exact (x (V.cliffordSpinCandidateMatrixCoordinate i j)).2
  have hcliffordInv :
      ∀ᶠ v in Filter.cofinite,
        ∀ s, x⁻¹ (V.cliffordSpinCandidateCliffordCoordinate s) v ∈
          v.adicCompletionIntegers ℚ := by
    rw [Filter.eventually_all]
    intro s
    exact (x⁻¹ (V.cliffordSpinCandidateCliffordCoordinate s)).2
  have hmatrixInv :
      ∀ᶠ v in Filter.cofinite,
        ∀ i j, x⁻¹ (V.cliffordSpinCandidateMatrixCoordinate i j) v ∈
          v.adicCompletionIntegers ℚ := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    exact (x⁻¹ (V.cliffordSpinCandidateMatrixCoordinate i j)).2
  filter_upwards [hclifford, hmatrix, hcliffordInv, hmatrixInv]
      with v hcv hmv hciv hmiv
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    change e.symm
      ((V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v x)
        (V.cliffordSpinCandidateCliffordCoordinate s)) ∈
      v.adicCompletionIntegers ℚ
    rw [V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom_apply]
    change e.symm (e (x (V.cliffordSpinCandidateCliffordCoordinate s) v)) ∈
      v.adicCompletionIntegers ℚ
    simpa using hcv s
  · intro i j
    change e.symm
      ((V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v x)
        (V.cliffordSpinCandidateMatrixCoordinate i j)) ∈
      v.adicCompletionIntegers ℚ
    rw [V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom_apply]
    change e.symm (e (x (V.cliffordSpinCandidateMatrixCoordinate i j) v)) ∈
      v.adicCompletionIntegers ℚ
    simpa using hmv i j
  · intro s
    change e.symm
      ((V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v x)⁻¹
        (V.cliffordSpinCandidateCliffordCoordinate s)) ∈
      v.adicCompletionIntegers ℚ
    rw [← (V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v).map_inv]
    rw [V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom_apply]
    change e.symm (e (x⁻¹ (V.cliffordSpinCandidateCliffordCoordinate s) v)) ∈
      v.adicCompletionIntegers ℚ
    simpa using hciv s
  · intro i j
    change e.symm
      ((V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v x)⁻¹
        (V.cliffordSpinCandidateMatrixCoordinate i j)) ∈
      v.adicCompletionIntegers ℚ
    rw [← (V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v).map_inv]
    rw [V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom_apply]
    change e.symm (e (x⁻¹ (V.cliffordSpinCandidateMatrixCoordinate i j) v)) ∈
      v.adicCompletionIntegers ℚ
    simpa using hmiv i j

/-- The carrier of height-one candidate families satisfying the literal
cofinite coordinate-integrality condition. -/
abbrev FiniteAdelicCliffordSpinCandidateRestrictedFamily :=
  {g : V.HeightOnePadicCliffordSpinCandidateGroupProduct //
    V.IsFiniteAdelicCliffordSpinCandidateRestrictedFamily g}

/-- Simultaneous evaluation into the restricted-family carrier. -/
def finiteAdelicCliffordSpinCandidateRestrictedFamilyMap
    (x : V.FiniteAdelicCliffordSpinCandidateGroup) :
    V.FiniteAdelicCliffordSpinCandidateRestrictedFamily :=
  ⟨V.finiteAdelicCliffordSpinCandidateHeightOneComponentsHom x,
    V.finiteAdelicCliffordSpinCandidateHeightOneComponents_isRestrictedFamily x⟩

/-- The restricted-family evaluation map is continuous. -/
theorem continuous_finiteAdelicCliffordSpinCandidateRestrictedFamilyMap :
    Continuous V.finiteAdelicCliffordSpinCandidateRestrictedFamilyMap :=
  (V.continuous_finiteAdelicCliffordSpinCandidateHeightOneComponents).subtype_mk _

/-- Restricted-family evaluation remains injective. -/
theorem finiteAdelicCliffordSpinCandidateRestrictedFamilyMap_injective :
    Function.Injective
      V.finiteAdelicCliffordSpinCandidateRestrictedFamilyMap := by
  intro x y hxy
  apply V.finiteAdelicCliffordSpinCandidateHeightOneComponentsHom_injective
  exact congrArg Subtype.val hxy

end RationalQuadraticSpaceMatrix

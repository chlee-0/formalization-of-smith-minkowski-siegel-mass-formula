import SMSFormula.RationalCliffordGeneralSpinHorizontalCentralOrbitChartProduct
import SMSFormula.RationalCliffordGeneralSpinHorizontalCylinderHaarRestriction

/-!
# Finite-adelic central-orbit intersection with the horizontal identity chart

This file transports the already proved componentwise exceptional/tail
central-orbit intersection to the intrinsic finite-adelic `GSpin` carrier.
It records first the two literal local-evaluation compatibilities needed for
that transport.  No measure, quotient, or product decomposition is used.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

local instance horizontalFiniteCentralOrbitPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance horizontalFiniteCentralOrbitDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2400000

/-- Local evaluation commutes literally with the scalar inclusion. -/
@[simp]
theorem finiteAdelicCliffordGeneralSpinHeightOneComponent_scalarGroupHom
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (a : RationalFiniteAdeleˣ) :
    V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v
        (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
          V RationalFiniteAdele a) =
      CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
        V ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
          (finiteAdelicUnitHeightOneComponentHom v a) := by
  apply CliffordGeneralSpinIntrinsicPoint.ext_cliffordUnit
  apply Units.ext
  rfl

/-- Local evaluation of the intrinsic point assembled from an exceptional
product and integral tail recovers the displayed source coordinate. -/
theorem finiteAdelicCliffordGeneralSpinHeightOneComponent_identityChartSourceToAmbient
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : V.CliffordGeneralSpinHorizontalExceptionalProduct S ×
      V.CliffordGeneralSpinHorizontalIntegralTail S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v
        (V.cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient S x) =
      if hv : v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces then
        x.1 ⟨v, hv⟩
      else
        (x.2 ⟨v, hv⟩).1 := by
  unfold cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient
  change
    V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v
        (V.finiteAdelicCliffordGeneralSpinRestrictedFamilyAssembly
          (V.cliffordGeneralSpinHorizontalExceptionalTailToRestrictedPrincipalBlock
            S x).1) = _
  rw [show
      V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v
          (V.finiteAdelicCliffordGeneralSpinRestrictedFamilyAssembly
            (V.cliffordGeneralSpinHorizontalExceptionalTailToRestrictedPrincipalBlock
              S x).1) =
        (V.cliffordGeneralSpinHorizontalExceptionalTailToRestrictedPrincipalBlock
          S x).1.1 v by
      exact congrFun
        (V.finiteAdelicCliffordGeneralSpinHeightOneComponents_assembly
          (V.cliffordGeneralSpinHorizontalExceptionalTailToRestrictedPrincipalBlock
            S x).1) v]
  by_cases hv : v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  · rw [V.cliffordGeneralSpinHorizontalExceptionalTailToRestrictedPrincipalBlock_apply_mem
      S x v hv]
    simp [hv]
  · rw [V.cliffordGeneralSpinHorizontalExceptionalTailToRestrictedPrincipalBlock_apply_notMem
      S x v hv]
    simp [hv]

/-! ## The intrinsic finite-adelic orbit -/

/-- The intrinsic finite-adelic point obtained from fixed exceptional Spin
chart coordinates and a fixed integral good tail. -/
def cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (s : V.CliffordGeneralSpinHorizontalExceptionalSOChartSource
      (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (g : V.CliffordGeneralSpinHorizontalIntegralTail S) :
    V.FiniteAdelicCliffordGeneralSpinGroup :=
  V.cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient S
    (fun v ↦ V.cliffordSpinCandidateToCliffordGeneralSpinHom
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] (s v), g)

/-- Central translation of the fixed intrinsic finite-adelic chart point. -/
def cliffordGeneralSpinHorizontalFiniteCentralOrbit
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (s : V.CliffordGeneralSpinHorizontalExceptionalSOChartSource
      (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (g : V.CliffordGeneralSpinHorizontalIntegralTail S) :
    RationalFiniteAdeleˣ → V.FiniteAdelicCliffordGeneralSpinGroup :=
  fun a ↦
    CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
        V RationalFiniteAdele a *
      V.cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin S s g

/-- If the ambient central translate lies in the certified `GSpin` identity
carrier, then the scalar finite idele is integral outside the retained
exceptional set.  This is the genuine-block bridge needed before direct
source extraction can be applied. -/
theorem isRationalIdeleDifferentialGenuinePrincipalBlock_of_finiteCentralOrbit_mem
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (s : V.CliffordGeneralSpinHorizontalExceptionalSOChartSource
      (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (g : V.CliffordGeneralSpinHorizontalIntegralTail S)
    (a : RationalFiniteAdeleˣ)
    (ha : V.cliffordGeneralSpinHorizontalFiniteCentralOrbit S s g a ∈
      V.cliffordGeneralSpinHorizontalIdentityChartFiniteAdelicCarrier S) :
    IsRationalIdeleDifferentialGenuinePrincipalBlock
      (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) a := by
  rcases ha with ⟨y, hy, hya⟩
  intro v hv
  let vg : V.CliffordGeneralSpinHorizontalIntegralPlace S := ⟨v, hv⟩
  have hcomponent := congrArg
    (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v) hya.symm
  have horbit :
      CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
          V ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
            (finiteAdelicUnitHeightOneComponentHom v a) *
        (g vg).1 = (y.2 vg).1 := by
    simpa [cliffordGeneralSpinHorizontalFiniteCentralOrbit,
      cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin,
      V.finiteAdelicCliffordGeneralSpinHeightOneComponent_identityChartSourceToAmbient,
      hv] using hcomponent
  apply
    (V.padicCliffordGeneralSpinHorizontalIntegralCentralOrbit_isIntegral_iff
      S vg (finiteAdelicUnitHeightOneComponentHom v a) (g vg)).mp
  rw [horbit]
  exact (y.2 vg).2

/-- Local evaluation of a finite idele assembled from the retained square
chart recovers its direct exceptional/integral-tail coordinate. -/
theorem finiteAdelicUnitHeightOneComponent_squareChartToAmbient
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (q : RationalFiniteIdeleDifferentialSquareChartSource B)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    finiteAdelicUnitHeightOneComponentHom v
        (rationalFiniteIdeleDifferentialSquareChartToAmbient B q) =
      rationalIdeleDifferentialExceptionalTailLocalUnit B
        ((fun w ↦ (q.1 w :
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv w.1).1]ˣ)), q.2) v := by
  exact finiteAdelicUnitHeightOneComponent_exceptionalTailToFiniteIdele
    B ((fun w ↦ (q.1 w :
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv w.1).1]ˣ)), q.2) v

/-- The forward half of the intrinsic carrier intersection: membership of
the translated `GSpin` point in the identity carrier forces the scalar finite
idele into the genuine retained square-chart carrier. -/
theorem finiteCentralOrbit_mem_squareChart_of_mem_identityChart
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (s : V.CliffordGeneralSpinHorizontalExceptionalSOChartSource
      (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (g : V.CliffordGeneralSpinHorizontalIntegralTail S)
    (a : RationalFiniteAdeleˣ)
    (ha : V.cliffordGeneralSpinHorizontalFiniteCentralOrbit S s g a ∈
      V.cliffordGeneralSpinHorizontalIdentityChartFiniteAdelicCarrier S) :
    a ∈ rationalFiniteIdeleDifferentialSquareChartCarrier
      (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) := by
  rcases ha with ⟨y, hy, hya⟩
  let B := S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  have haBlock : IsRationalIdeleDifferentialGenuinePrincipalBlock B a :=
    V.isRationalIdeleDifferentialGenuinePrincipalBlock_of_finiteCentralOrbit_mem
      S s g a ⟨y, hy, hya⟩
  let ab : RationalIdeleDifferentialGenuinePrincipalBlock B := ⟨a, haBlock⟩
  let z :=
    (rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockHomeomorph
      B).symm ab
  have hzExceptional :
      z.1 ∈ rationalIdeleDifferentialExceptionalSquareChartCarrier B := by
    intro v _
    have hcomponent := congrArg
      (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v.1) hya.symm
    have horbit :
        CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
            V ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]
              (finiteAdelicUnitHeightOneComponentHom v.1 a) *
          V.cliffordSpinCandidateToCliffordGeneralSpinHom
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] (s v) =
        y.1 v := by
      simpa [cliffordGeneralSpinHorizontalFiniteCentralOrbit,
        cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin,
        V.finiteAdelicCliffordGeneralSpinHeightOneComponent_identityChartSourceToAmbient,
        v.2] using hcomponent
    have hlocalMem :
        CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
            V ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]
              (finiteAdelicUnitHeightOneComponentHom v.1 a) *
          V.cliffordSpinCandidateToCliffordGeneralSpinHom
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] (s v) ∈
        (V.padicCliffordGeneralSpinCentralFiberIdentityChart
          (Rat.HeightOneSpectrum.primesEquiv v.1).1).source := by
      rw [horbit]
      exact hy.1 v (Set.mem_univ v)
    have hscalar :=
      (Set.ext_iff.mp
        (V.preimage_padicCliffordGeneralSpinCentralOrbit_identityChart
          (Rat.HeightOneSpectrum.primesEquiv v.1).1 (s v) (s v).2)
        (finiteAdelicUnitHeightOneComponentHom v.1 a)).mp hlocalMem
    change finiteAdelicUnitHeightOneComponentHom v.1 a ∈
      (Rat.unitSquareIdentityChart
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).source
    exact hscalar
  let q : RationalFiniteIdeleDifferentialSquareChartSource B :=
    (fun v ↦ ⟨z.1 v, hzExceptional v (Set.mem_univ v)⟩, z.2)
  refine ⟨q, ?_⟩
  change
    (rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockHomeomorph B
      ((fun v ↦ (q.1 v :
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ)), q.2)).1 = a
  have hqz :
      ((fun v ↦ (q.1 v :
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ)), q.2) = z := by
    apply Prod.ext
    · rfl
    · rfl
  rw [hqz]
  change
    ((rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockHomeomorph B)
      ((rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockHomeomorph B).symm
        ab)).1 = a
  rw [(rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockHomeomorph B).apply_symm_apply]

/-- The reverse half of the intrinsic carrier intersection: every scalar in
the retained finite-idele square chart translates the fixed point back into
the certified `GSpin` identity carrier. -/
theorem finiteCentralOrbit_mem_identityChart_of_mem_squareChart
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (s : V.CliffordGeneralSpinHorizontalExceptionalSOChartSource
      (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (g : V.CliffordGeneralSpinHorizontalIntegralTail S)
    (a : RationalFiniteAdeleˣ)
    (ha : a ∈ rationalFiniteIdeleDifferentialSquareChartCarrier
      (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    V.cliffordGeneralSpinHorizontalFiniteCentralOrbit S s g a ∈
      V.cliffordGeneralSpinHorizontalIdentityChartFiniteAdelicCarrier S := by
  rcases ha with ⟨q, hqa⟩
  let B := S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let scalarExceptional : RationalIdeleDifferentialExceptionalProduct B :=
    fun v ↦ q.1 v
  let y : V.CliffordGeneralSpinHorizontalExceptionalProduct S ×
      V.CliffordGeneralSpinHorizontalIntegralTail S :=
    (V.cliffordGeneralSpinHorizontalExceptionalCentralOrbit S s scalarExceptional,
      fun v ↦ ⟨
        CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
            V ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] (q.2 v).1 *
          (g v).1,
        (V.padicCliffordGeneralSpinHorizontalIntegralCentralOrbit_isIntegral_iff
          S v (q.2 v).1 (g v)).mpr (q.2 v).2⟩)
  refine ⟨y, ?_, ?_⟩
  · constructor
    · intro v _
      have hlocal :=
        V.preimage_padicCliffordGeneralSpinCentralOrbit_identityChart
          (Rat.HeightOneSpectrum.primesEquiv v.1).1 (s v) (s v).2
      exact (Set.ext_iff.mp hlocal (q.1 v)).mpr (q.1 v).2
    · trivial
  · apply V.finiteAdelicCliffordGeneralSpinHeightOneComponentsHom_injective
    funext v
    change
      V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v
          (V.cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient S y) =
        V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v
          (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
              V RationalFiniteAdele a *
            V.cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin S s g)
    rw [(V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v).map_mul]
    by_cases hv : v ∈ B
    · have hqaComponent := congrArg
        (finiteAdelicUnitHeightOneComponentHom v) hqa
      have hscalar : finiteAdelicUnitHeightOneComponentHom v a = q.1 ⟨v, hv⟩ := by
        rw [← hqaComponent]
        rw [finiteAdelicUnitHeightOneComponent_squareChartToAmbient]
        simp [rationalIdeleDifferentialExceptionalTailLocalUnit, B, hv]
      simp [cliffordGeneralSpinHorizontalFiniteCentralOrbit,
        cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin,
        cliffordGeneralSpinHorizontalExceptionalCentralOrbit,
        V.finiteAdelicCliffordGeneralSpinHeightOneComponent_identityChartSourceToAmbient,
        y, scalarExceptional, B, hv, hscalar]
    · have hqaComponent := congrArg
        (finiteAdelicUnitHeightOneComponentHom v) hqa
      have hscalar : finiteAdelicUnitHeightOneComponentHom v a = (q.2 ⟨v, hv⟩).1 := by
        rw [← hqaComponent]
        rw [finiteAdelicUnitHeightOneComponent_squareChartToAmbient]
        simp [rationalIdeleDifferentialExceptionalTailLocalUnit, B, hv]
      simp [cliffordGeneralSpinHorizontalFiniteCentralOrbit,
        cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin,
        V.finiteAdelicCliffordGeneralSpinHeightOneComponent_identityChartSourceToAmbient,
        y, B, hv, hscalar]

/-- Exact finite-adelic orbit/chart intersection on the genuine intrinsic
carriers.  This is the conjugation of the local exceptional and integral-tail
equalities; it uses neither a Cartesian central extension nor injectivity of
the global `(nu,pi)` coordinate map. -/
theorem preimage_cliffordGeneralSpinHorizontalFiniteCentralOrbit_identityChart
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (s : V.CliffordGeneralSpinHorizontalExceptionalSOChartSource
      (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (g : V.CliffordGeneralSpinHorizontalIntegralTail S) :
    V.cliffordGeneralSpinHorizontalFiniteCentralOrbit S s g ⁻¹'
        V.cliffordGeneralSpinHorizontalIdentityChartFiniteAdelicCarrier S =
      rationalFiniteIdeleDifferentialSquareChartCarrier
        (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) := by
  ext a
  constructor
  · exact V.finiteCentralOrbit_mem_squareChart_of_mem_identityChart S s g a
  · exact V.finiteCentralOrbit_mem_identityChart_of_mem_squareChart S s g a

end RationalQuadraticSpaceMatrix

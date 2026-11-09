import SMSFormula.RationalQuadraticIsometrySpinCandidateGeneralEquivalence

/-!
# Native topology under arbitrary rational quadratic isometries

The algebraic `GSpin` and Spin equivalences attached to an arbitrary supplied
rational quadratic isometry are homeomorphisms for the repository's existing
finite-coordinate topologies.  Their full-adelic specializations descend to
homeomorphisms of the existing rational left quotients and are measurable for
the certified quotient structures.

Continuity is proved from finite coordinate expansions.  No topology, chart,
Haar measure, integral structure, quotient measure, raw certificate, or
Tamagawa value is transported or selected.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open Topology
open scoped Matrix

namespace RationalQuadraticSpaceMatrix

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 800000

variable {r s : ℕ}
variable (U : RationalQuadraticSpaceMatrix r)
variable (V : RationalQuadraticSpaceMatrix s)
variable (e : U.quadraticForm.IsometryEquiv V.quadraticForm)

private theorem continuous_linearMap_pi
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    {a b : ℕ} (f : (Fin a → A) →ₗ[A] (Fin b → A)) :
    Continuous f := by
  have hfun : (fun y ↦ f y) =
      fun y ↦ ∑ i, y i • f (Pi.single i (1 : A)) := by
    funext y
    calc
      f y = f (∑ i, y i • (Pi.single i (1 : A) : Fin a → A)) := by
        rw [commutativeScalarExtension_single_sum A y]
      _ = ∑ i, y i • f (Pi.single i (1 : A)) := by simp
  change Continuous (fun y ↦ f y)
  rw [hfun]
  fun_prop

/-- The scalar extension of a supplied rational isometry is continuous for
the native finite product topologies. -/
theorem continuous_rationalIsometryBaseChangeIsometryEquiv
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (rationalIsometryBaseChangeIsometryEquiv U V e A) :=
  continuous_linearMap_pi
    (rationalIsometryBaseChangeIsometryEquiv U V e A).toLinearEquiv.toLinearMap

/-- The inverse scalar-extended rational isometry is continuous for the same
native topologies. -/
theorem continuous_rationalIsometryBaseChangeIsometryEquiv_symm
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (rationalIsometryBaseChangeIsometryEquiv U V e A).symm :=
  continuous_linearMap_pi
    (rationalIsometryBaseChangeIsometryEquiv U V e A).symm.toLinearEquiv.toLinearMap

private theorem continuous_conjugatedMatrixCoordinate
    {a b : ℕ} {A X : Type*}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [TopologicalSpace X]
    (E : (Fin a → A) ≃ₗ[A] (Fin b → A))
    (hE : Continuous E)
    (M : X → Matrix (Fin a) (Fin a) A)
    (hM : ∀ i j, Continuous (fun z ↦ M z i j))
    (i j : Fin b) :
    Continuous (fun z ↦
      E (Matrix.mulVec (M z) (E.symm (Pi.single j 1))) i) := by
  apply (continuous_apply i).comp
  apply hE.comp
  apply continuous_pi
  intro k
  change Continuous (fun z ↦
    ∑ l, M z k l * E.symm (Pi.single j 1) l)
  apply continuous_finset_sum
  intro l _
  exact (hM k l).mul continuous_const

/-- Arbitrary rational-isometry transport on intrinsic `GSpin` is continuous
for every native topological rational algebra. -/
theorem continuous_rationalIsometryGeneralSpinIntrinsicPoint
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (rationalIsometryGeneralSpinIntrinsicPoint U V e A) := by
  let E := rationalIsometryBaseChangeIsometryEquiv U V e A
  let Phi := rationalIsometryCliffordBaseChangeAlgEquiv U V e A
  have hmatrix (i j : Fin s) : Continuous (fun z :
      U.CliffordGeneralSpinIntrinsicPoint A ↦
      (rationalIsometryGeneralSpinIntrinsicPoint U V e A z).matrixPoint.1 i j) := by
    let b : Fin s → A := Pi.single j 1
    let v : Fin r → A := E.symm b
    have hcont : Continuous (fun z : U.CliffordGeneralSpinIntrinsicPoint A ↦
        E (Matrix.mulVec z.matrixPoint.1 v) i) := by
      simpa only [v] using
        (continuous_conjugatedMatrixCoordinate E
          (continuous_rationalIsometryBaseChangeIsometryEquiv U V e A)
          (fun z : U.CliffordGeneralSpinIntrinsicPoint A ↦ z.matrixPoint.1)
          (fun k l ↦ U.continuous_cliffordGeneralSpinMatrixCoordinate A k l)
          i j)
    rw [show (fun z : U.CliffordGeneralSpinIntrinsicPoint A ↦
        (rationalIsometryGeneralSpinIntrinsicPoint U V e A z).matrixPoint.1 i j) =
        fun z ↦ E (Matrix.mulVec z.matrixPoint.1 v) i by
      funext z
      change (rationalIsometrySpecialOrthogonalMatrixPoint U V e A
          z.matrixPoint).1 i j = _
      have hcol :
          (rationalIsometrySpecialOrthogonalMatrixPoint U V e A
            z.matrixPoint).1 i j =
            Matrix.mulVec
              (rationalIsometrySpecialOrthogonalMatrixPoint U V e A
                z.matrixPoint).1 b i := by
        simp [b, Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [hcol, rationalIsometrySpecialOrthogonalMatrixPoint_mulVec]]
    exact hcont
  apply continuous_induced_rng.mpr
  apply Continuous.prodMk
  · apply Continuous.prodMk
    · apply continuous_pi
      intro u
      rw [show (fun z : U.CliffordGeneralSpinIntrinsicPoint A ↦
          (V.cliffordCoordinateBaseChangeBasis A).repr
            ((rationalIsometryGeneralSpinIntrinsicPoint U V e A z).cliffordUnit :
              V.cliffordCoordinateBaseChangeAlgebra A) u) =
          fun z ↦ ∑ t,
            (U.cliffordCoordinateBaseChangeBasis A).repr
                (z.cliffordUnit : U.cliffordCoordinateBaseChangeAlgebra A) t *
              (V.cliffordCoordinateBaseChangeBasis A).repr
                (Phi (U.cliffordCoordinateBaseChangeBasis A t)) u by
        funext z
        change (V.cliffordCoordinateBaseChangeBasis A).repr
            (Phi (z.cliffordUnit : U.cliffordCoordinateBaseChangeAlgebra A)) u = _
        conv_lhs =>
          rw [← (U.cliffordCoordinateBaseChangeBasis A).sum_repr
            (z.cliffordUnit : U.cliffordCoordinateBaseChangeAlgebra A)]
        simp only [map_sum, map_smul, Finsupp.coe_finset_sum,
          Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]]
      apply continuous_finset_sum
      intro t _
      exact (U.continuous_cliffordGeneralSpinCliffordCoordinate A t).mul
        continuous_const
    · simpa using U.continuous_cliffordGeneralSpinSimilitude A
  · apply Continuous.prodMk
    · apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      exact hmatrix i j
    · apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      rw [show (fun z : U.CliffordGeneralSpinIntrinsicPoint A ↦
          (rationalIsometryGeneralSpinIntrinsicPoint U V e A
            z).matrixGroup⁻¹.1.1.1 i j) =
          fun z ↦
            (rationalIsometryGeneralSpinIntrinsicPoint U V e A
              z⁻¹).matrixPoint.1 i j by
        funext z
        calc
          (rationalIsometryGeneralSpinIntrinsicPoint U V e A
              z).matrixGroup⁻¹.1.1.1 i j =
              ((rationalIsometryGeneralSpinIntrinsicPoint U V e A z)⁻¹
                ).matrixPoint.1 i j := by
                  rw [← CliffordGeneralSpinIntrinsicPoint.matrixGroup_coe,
                    CliffordGeneralSpinIntrinsicPoint.inv_matrixGroup]
          _ = (rationalIsometryGeneralSpinIntrinsicPoint U V e A
                z⁻¹).matrixPoint.1 i j := by
                  exact congrArg
                    (fun w : V.CliffordGeneralSpinIntrinsicPoint A ↦
                      w.matrixPoint.1 i j)
                    (map_inv (rationalIsometryGeneralSpinMulEquiv U V e A) z).symm]
      exact (hmatrix i j).comp
        (U.continuous_inv_cliffordGeneralSpinIntrinsicPoint A)

/-- The arbitrary rational-isometry `GSpin` equivalence is a continuous
multiplicative equivalence for the existing topologies. -/
def rationalIsometryGeneralSpinContinuousMulEquiv
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    U.CliffordGeneralSpinIntrinsicPoint A ≃ₜ*
      V.CliffordGeneralSpinIntrinsicPoint A :=
  ContinuousMulEquiv.mk'
    { toEquiv := (rationalIsometryGeneralSpinMulEquiv U V e A).toEquiv
      continuous_toFun :=
        continuous_rationalIsometryGeneralSpinIntrinsicPoint U V e A
      continuous_invFun :=
        continuous_rationalIsometryGeneralSpinIntrinsicPoint V U e.symm A }
    (rationalIsometryGeneralSpinMulEquiv U V e A).map_mul

@[simp]
theorem rationalIsometryGeneralSpinContinuousMulEquiv_toMulEquiv
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    (rationalIsometryGeneralSpinContinuousMulEquiv U V e A).toMulEquiv =
      rationalIsometryGeneralSpinMulEquiv U V e A :=
  rfl

private theorem spinCandidateEmbedding_isEmbedding
    (W : RationalQuadraticSpaceMatrix r)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    IsEmbedding (W.cliffordSpinCandidateToCliffordGeneralSpinHom A) := by
  let p :
      (((Finset (Fin r) → A) × Aˣ) ×
          (Matrix (Fin r) (Fin r) A × Matrix (Fin r) (Fin r) A)) →
        ((Finset (Fin r) → A) × Matrix (Fin r) (Fin r) A) :=
    fun z ↦ (z.1.1, z.2.1)
  have hp : Continuous p :=
    (continuous_fst.comp continuous_fst).prodMk
      (continuous_fst.comp continuous_snd)
  have hcomp :
      (p ∘ W.cliffordGeneralSpinPointCoordinateMap A) ∘
          W.cliffordSpinCandidateToCliffordGeneralSpinHom A =
        W.cliffordSpinCandidatePointCoordinateMap A := by
    funext z
    apply Prod.ext
    · ext u
      simp [p, Function.comp_def,
        cliffordSpinCandidateToCliffordGeneralSpinHom,
        CliffordGeneralSpinIntrinsicPoint.ofSpinGroupHom,
        CliffordGeneralSpinIntrinsicPoint.ofSpin]
    · ext i j
      simp [p, Function.comp_def,
        cliffordSpinCandidateToCliffordGeneralSpinHom,
        CliffordGeneralSpinIntrinsicPoint.ofSpinGroupHom,
        CliffordGeneralSpinIntrinsicPoint.ofSpin]
  apply IsEmbedding.of_comp
    (W.continuous_cliffordSpinCandidateToCliffordGeneralSpinHom A)
    (hp.comp (W.continuous_cliffordGeneralSpinPointCoordinateMap A))
  rw [hcomp]
  exact W.cliffordSpinCandidatePointCoordinateMap_isEmbedding A

/-- Spin transport through an arbitrary rational isometry is continuous. -/
theorem continuous_rationalIsometrySpinCandidateMulEquiv
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (rationalIsometrySpinCandidateMulEquiv U V e A) := by
  rw [(spinCandidateEmbedding_isEmbedding V A).continuous_iff]
  rw [show V.cliffordSpinCandidateToCliffordGeneralSpinHom A ∘
        rationalIsometrySpinCandidateMulEquiv U V e A =
      rationalIsometryGeneralSpinContinuousMulEquiv U V e A ∘
        U.cliffordSpinCandidateToCliffordGeneralSpinHom A by
    funext z
    exact
      cliffordSpinCandidateToGeneralSpin_rationalIsometrySpinCandidateMulEquiv
        U V e A z]
  exact (rationalIsometryGeneralSpinContinuousMulEquiv U V e A).continuous.comp
    (U.continuous_cliffordSpinCandidateToCliffordGeneralSpinHom A)

private theorem cliffordSpinCandidateToGeneralSpin_rationalIsometrySpinCandidateMulEquiv_symm
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (z : V.CliffordSpinCandidateGroup A) :
    U.cliffordSpinCandidateToCliffordGeneralSpinHom A
        ((rationalIsometrySpinCandidateMulEquiv U V e A).symm z) =
      (rationalIsometryGeneralSpinMulEquiv U V e A).symm
        (V.cliffordSpinCandidateToCliffordGeneralSpinHom A z) := by
  apply (rationalIsometryGeneralSpinMulEquiv U V e A).injective
  rw [← cliffordSpinCandidateToGeneralSpin_rationalIsometrySpinCandidateMulEquiv]
  simp

/-- The inverse Spin transport is continuous for the same existing
topologies. -/
theorem continuous_rationalIsometrySpinCandidateMulEquiv_symm
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (rationalIsometrySpinCandidateMulEquiv U V e A).symm := by
  rw [(spinCandidateEmbedding_isEmbedding U A).continuous_iff]
  rw [show U.cliffordSpinCandidateToCliffordGeneralSpinHom A ∘
        (rationalIsometrySpinCandidateMulEquiv U V e A).symm =
      (rationalIsometryGeneralSpinContinuousMulEquiv U V e A).symm ∘
        V.cliffordSpinCandidateToCliffordGeneralSpinHom A by
    funext z
    exact
      cliffordSpinCandidateToGeneralSpin_rationalIsometrySpinCandidateMulEquiv_symm
        U V e A z]
  exact (rationalIsometryGeneralSpinContinuousMulEquiv U V e A).symm.continuous.comp
    (V.continuous_cliffordSpinCandidateToCliffordGeneralSpinHom A)

/-- The arbitrary rational-isometry Spin equivalence is a continuous
multiplicative equivalence for the existing topologies. -/
def rationalIsometrySpinCandidateContinuousMulEquiv
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    U.CliffordSpinCandidateGroup A ≃ₜ* V.CliffordSpinCandidateGroup A :=
  ContinuousMulEquiv.mk'
    { toEquiv := (rationalIsometrySpinCandidateMulEquiv U V e A).toEquiv
      continuous_toFun :=
        continuous_rationalIsometrySpinCandidateMulEquiv U V e A
      continuous_invFun :=
        continuous_rationalIsometrySpinCandidateMulEquiv_symm U V e A }
    (rationalIsometrySpinCandidateMulEquiv U V e A).map_mul

@[simp]
theorem rationalIsometrySpinCandidateContinuousMulEquiv_toMulEquiv
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    (rationalIsometrySpinCandidateContinuousMulEquiv U V e A).toMulEquiv =
      rationalIsometrySpinCandidateMulEquiv U V e A :=
  rfl

/-! ## Full-adelic quotient homeomorphisms -/

@[simp]
theorem rationalIsometryGeneralSpinFullAdelicLeftQuotientEquiv_symm_mk
    (g : V.FullAdelicCliffordGeneralSpinGroup) :
    (rationalIsometryGeneralSpinFullAdelicLeftQuotientEquiv U V e).symm
        (V.fullAdelicCliffordGeneralSpinLeftQuotientMap g) =
      U.fullAdelicCliffordGeneralSpinLeftQuotientMap
        ((rationalIsometryGeneralSpinMulEquiv U V e RationalAdele).symm g) :=
  rfl

/-- The arbitrary-isometry `GSpin` quotient equivalence is a homeomorphism for
the existing quotient topologies. -/
def rationalIsometryGeneralSpinFullAdelicLeftQuotientHomeomorph :
    U.FullAdelicCliffordGeneralSpinLeftQuotient ≃ₜ
      V.FullAdelicCliffordGeneralSpinLeftQuotient where
  toEquiv := rationalIsometryGeneralSpinFullAdelicLeftQuotientEquiv U V e
  continuous_toFun := by
    apply Continuous.quotient_lift
    simpa only [Function.comp_apply,
      rationalIsometryGeneralSpinFullAdelicLeftQuotientEquiv_mk] using
      V.fullAdelicCliffordGeneralSpinLeftQuotientMap_isQuotientMap.continuous.comp
        (rationalIsometryGeneralSpinContinuousMulEquiv
          U V e RationalAdele).continuous
  continuous_invFun := by
    apply Continuous.quotient_lift
    simpa only [Function.comp_apply,
      rationalIsometryGeneralSpinFullAdelicLeftQuotientEquiv_symm_mk] using
      U.fullAdelicCliffordGeneralSpinLeftQuotientMap_isQuotientMap.continuous.comp
        (rationalIsometryGeneralSpinContinuousMulEquiv
          U V e RationalAdele).symm.continuous

@[simp]
theorem rationalIsometryGeneralSpinFullAdelicLeftQuotientHomeomorph_toEquiv :
    (rationalIsometryGeneralSpinFullAdelicLeftQuotientHomeomorph U V e).toEquiv =
      rationalIsometryGeneralSpinFullAdelicLeftQuotientEquiv U V e :=
  rfl

theorem measurable_rationalIsometryGeneralSpinFullAdelicLeftQuotientHomeomorph :
    Measurable
      (rationalIsometryGeneralSpinFullAdelicLeftQuotientHomeomorph U V e) :=
  (rationalIsometryGeneralSpinFullAdelicLeftQuotientHomeomorph
    U V e).continuous.measurable

theorem measurable_rationalIsometryGeneralSpinFullAdelicLeftQuotientHomeomorph_symm :
    Measurable
      (rationalIsometryGeneralSpinFullAdelicLeftQuotientHomeomorph U V e).symm :=
  (rationalIsometryGeneralSpinFullAdelicLeftQuotientHomeomorph
    U V e).symm.continuous.measurable

@[simp]
theorem rationalIsometrySpinCandidateFullAdelicLeftQuotientEquiv_symm_mk
    (g : V.FullAdelicCliffordSpinCandidateGroup) :
    (rationalIsometrySpinCandidateFullAdelicLeftQuotientEquiv U V e).symm
        (V.fullAdelicCliffordSpinCandidateLeftQuotientMap g) =
      U.fullAdelicCliffordSpinCandidateLeftQuotientMap
        ((rationalIsometrySpinCandidateMulEquiv U V e RationalAdele).symm g) :=
  rfl

/-- The arbitrary-isometry Spin quotient equivalence is a homeomorphism for
the existing quotient topologies. -/
def rationalIsometrySpinCandidateFullAdelicLeftQuotientHomeomorph :
    U.FullAdelicCliffordSpinCandidateLeftQuotient ≃ₜ
      V.FullAdelicCliffordSpinCandidateLeftQuotient where
  toEquiv := rationalIsometrySpinCandidateFullAdelicLeftQuotientEquiv U V e
  continuous_toFun := by
    apply Continuous.quotient_lift
    simpa only [Function.comp_apply,
      rationalIsometrySpinCandidateFullAdelicLeftQuotientEquiv_mk] using
      V.fullAdelicCliffordSpinCandidateLeftQuotientMap_isQuotientMap.continuous.comp
        (rationalIsometrySpinCandidateContinuousMulEquiv
          U V e RationalAdele).continuous
  continuous_invFun := by
    apply Continuous.quotient_lift
    simpa only [Function.comp_apply,
      rationalIsometrySpinCandidateFullAdelicLeftQuotientEquiv_symm_mk] using
      U.fullAdelicCliffordSpinCandidateLeftQuotientMap_isQuotientMap.continuous.comp
        (rationalIsometrySpinCandidateContinuousMulEquiv
          U V e RationalAdele).symm.continuous

theorem measurable_rationalIsometrySpinCandidateFullAdelicLeftQuotientHomeomorph :
    Measurable
      (rationalIsometrySpinCandidateFullAdelicLeftQuotientHomeomorph U V e) := by
  apply Measurable.of_le_map
  change MeasurableSpace.map V.fullAdelicCliffordSpinCandidateLeftQuotientMap
      (borel V.FullAdelicCliffordSpinCandidateGroup) ≤
    MeasurableSpace.map
      (rationalIsometrySpinCandidateFullAdelicLeftQuotientHomeomorph U V e)
      (MeasurableSpace.map
        U.fullAdelicCliffordSpinCandidateLeftQuotientMap
        (borel U.FullAdelicCliffordSpinCandidateGroup))
  have he : borel V.FullAdelicCliffordSpinCandidateGroup ≤
      MeasurableSpace.map
        (rationalIsometrySpinCandidateContinuousMulEquiv U V e RationalAdele)
        (borel U.FullAdelicCliffordSpinCandidateGroup) :=
    measurable_iff_le_map.mp
      (rationalIsometrySpinCandidateContinuousMulEquiv
        U V e RationalAdele).continuous.measurable
  calc
    _ ≤ MeasurableSpace.map V.fullAdelicCliffordSpinCandidateLeftQuotientMap
        (MeasurableSpace.map
          (rationalIsometrySpinCandidateContinuousMulEquiv U V e RationalAdele)
          (borel U.FullAdelicCliffordSpinCandidateGroup)) :=
      MeasurableSpace.map_mono he
    _ = MeasurableSpace.map
        (V.fullAdelicCliffordSpinCandidateLeftQuotientMap ∘
          rationalIsometrySpinCandidateContinuousMulEquiv U V e RationalAdele)
        (borel U.FullAdelicCliffordSpinCandidateGroup) :=
      MeasurableSpace.map_comp
    _ = MeasurableSpace.map
        (rationalIsometrySpinCandidateFullAdelicLeftQuotientHomeomorph U V e ∘
          U.fullAdelicCliffordSpinCandidateLeftQuotientMap)
        (borel U.FullAdelicCliffordSpinCandidateGroup) := by
      congr 1
    _ = _ := MeasurableSpace.map_comp.symm

theorem measurable_rationalIsometrySpinCandidateFullAdelicLeftQuotientHomeomorph_symm :
    Measurable
      (rationalIsometrySpinCandidateFullAdelicLeftQuotientHomeomorph U V e).symm := by
  apply Measurable.of_le_map
  change MeasurableSpace.map U.fullAdelicCliffordSpinCandidateLeftQuotientMap
      (borel U.FullAdelicCliffordSpinCandidateGroup) ≤
    MeasurableSpace.map
      (rationalIsometrySpinCandidateFullAdelicLeftQuotientHomeomorph U V e).symm
      (MeasurableSpace.map
        V.fullAdelicCliffordSpinCandidateLeftQuotientMap
        (borel V.FullAdelicCliffordSpinCandidateGroup))
  have he : borel U.FullAdelicCliffordSpinCandidateGroup ≤
      MeasurableSpace.map
        (rationalIsometrySpinCandidateContinuousMulEquiv U V e RationalAdele).symm
        (borel V.FullAdelicCliffordSpinCandidateGroup) :=
    measurable_iff_le_map.mp
      (rationalIsometrySpinCandidateContinuousMulEquiv
        U V e RationalAdele).symm.continuous.measurable
  calc
    _ ≤ MeasurableSpace.map U.fullAdelicCliffordSpinCandidateLeftQuotientMap
        (MeasurableSpace.map
          (rationalIsometrySpinCandidateContinuousMulEquiv
            U V e RationalAdele).symm
          (borel V.FullAdelicCliffordSpinCandidateGroup)) :=
      MeasurableSpace.map_mono he
    _ = MeasurableSpace.map
        (U.fullAdelicCliffordSpinCandidateLeftQuotientMap ∘
          (rationalIsometrySpinCandidateContinuousMulEquiv
            U V e RationalAdele).symm)
        (borel V.FullAdelicCliffordSpinCandidateGroup) :=
      MeasurableSpace.map_comp
    _ = MeasurableSpace.map
        ((rationalIsometrySpinCandidateFullAdelicLeftQuotientHomeomorph
            U V e).symm ∘
          V.fullAdelicCliffordSpinCandidateLeftQuotientMap)
        (borel V.FullAdelicCliffordSpinCandidateGroup) := by
      congr 1
    _ = _ := MeasurableSpace.map_comp.symm

/-- The topological Spin and `GSpin` quotient maps commute literally. -/
theorem rationalIsometrySpinCandidateFullAdelicLeftQuotientToGeneralSpin_homeomorph_commutes
    (q : U.FullAdelicCliffordSpinCandidateLeftQuotient) :
    V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin
        (rationalIsometrySpinCandidateFullAdelicLeftQuotientHomeomorph U V e q) =
      rationalIsometryGeneralSpinFullAdelicLeftQuotientHomeomorph U V e
        (U.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin q) :=
  rationalIsometrySpinCandidateFullAdelicLeftQuotientToGeneralSpin_commutes
    U V e q

end RationalQuadraticSpaceMatrix

end

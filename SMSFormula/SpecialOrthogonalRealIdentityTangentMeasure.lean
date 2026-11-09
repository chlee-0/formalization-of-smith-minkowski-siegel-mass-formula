import SMSFormula.SpecialOrthogonalRealIdentityTangentBasis

/-!
# Coordinate measure under the identity tangent decomposition

The identity tangent measure is the additive Haar measure normalized by the
same scalar-extended fixed rational basis used by
`Matrix.skewAdjointRealCoordinateDetMeasure`. Under the explicit tangent
decomposition, it becomes the product of the lower-rank fixed-basis Haar and
standard coordinate Haar, scaled by the reciprocal absolute comparison
determinant.

The comparison determinant remains symbolic. No sphere measure, quotient
measure, disintegration, or rank recurrence is introduced.
-/

open scoped Matrix Matrix.Norms.Operator

noncomputable section

open Matrix MeasureTheory

namespace Module.Basis

variable {ι E E' : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace E'] [BorelSpace E']
  [SecondCountableTopology E'] [SigmaCompactSpace E']

/-- Basis-Haar transport stated using the mapped source basis itself. This
avoids expanding a large specialized equivalence merely to identify its
pointwise basis family. -/
theorem map_addHaar_eq_inv_abs_det_map_smul
    (b : Basis ι ℝ E) (b' : Basis ι ℝ E') (e : E ≃L[ℝ] E') :
    Measure.map e b.addHaar =
      (Real.toNNReal |b'.det (b.map e.toLinearEquiv)|)⁻¹ • b'.addHaar := by
  simpa only [Module.Basis.coe_map] using
    map_addHaar_eq_inv_abs_det_smul b b' e

end Module.Basis

namespace PositiveDefiniteIntegralLattice

local instance identitySpecialOrthogonalTangentMeasurableSpace (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalTangent n) :=
  borel _

local instance identitySpecialOrthogonalTangentBorelSpace (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalTangent n) :=
  ⟨rfl⟩

local instance identitySpecialOrthogonalTangentProductBorelSpace (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalTangent n × (Fin n → ℝ)) :=
  @Prod.borelSpace _ _ _
    (identitySpecialOrthogonalTangentMeasurableSpace n)
    (identitySpecialOrthogonalTangentBorelSpace n) _ _ _ _

/-- The identity tangent coordinate measure normalized by the fixed rational
skew-adjoint basis after scalar extension to `ℝ`. -/
def identitySpecialOrthogonalTangentCoordinateMeasure (n : ℕ) :
    Measure (identitySpecialOrthogonalTangent n) :=
  @Module.Basis.addHaar _ _ _ _ _
    (identitySpecialOrthogonalTangentMeasurableSpace n)
    (identitySpecialOrthogonalTangentBorelSpace n)
    (identitySpecialOrthogonalFixedTangentBasis n)

/-- The independently normalized coordinate measure on the lower-rank
tangent/last-column product. -/
def identitySpecialOrthogonalTangentProductCoordinateMeasure (n : ℕ) :
    Measure (identitySpecialOrthogonalTangent n × (Fin n → ℝ)) := by
  letI : MeasurableSpace (identitySpecialOrthogonalTangent n) :=
    identitySpecialOrthogonalTangentMeasurableSpace n
  letI : BorelSpace (identitySpecialOrthogonalTangent n) :=
    identitySpecialOrthogonalTangentBorelSpace n
  letI : BorelSpace (identitySpecialOrthogonalTangent n × (Fin n → ℝ)) :=
    Prod.borelSpace
  exact @Module.Basis.addHaar _
    (identitySpecialOrthogonalTangent n × (Fin n → ℝ)) _ _ _ _
    (identitySpecialOrthogonalTangentProductBorelSpace n)
    (identitySpecialOrthogonalTangentProductBasis n)

/-- The target coordinate measure is exactly lower-rank fixed-basis Haar
times standard coordinate Haar on the nonfinal last-column entries. -/
theorem identitySpecialOrthogonalTangentProductCoordinateMeasure_eq_prod
    (n : ℕ) :
    identitySpecialOrthogonalTangentProductCoordinateMeasure n =
      (identitySpecialOrthogonalTangentCoordinateMeasure n).prod
        (Pi.basisFun ℝ (Fin n)).addHaar := by
  letI : MeasurableSpace (identitySpecialOrthogonalTangent n) :=
    identitySpecialOrthogonalTangentMeasurableSpace n
  letI : BorelSpace (identitySpecialOrthogonalTangent n) :=
    identitySpecialOrthogonalTangentBorelSpace n
  letI : BorelSpace (identitySpecialOrthogonalTangent n × (Fin n → ℝ)) :=
    Prod.borelSpace
  have reindexMeasure := @Module.Basis.addHaar_reindex _ _
    (identitySpecialOrthogonalTangent n × (Fin n → ℝ)) _ _ _ _ _
    (identitySpecialOrthogonalTangentProductBorelSpace n)
    ((identitySpecialOrthogonalFixedTangentBasis n).prod (Pi.basisFun ℝ (Fin n)))
    (identitySpecialOrthogonalTangentProductIndexEquiv n)
  have productMeasure := @Module.Basis.prod_addHaar _ _
    (identitySpecialOrthogonalTangent n) (Fin n → ℝ) _ _ _ _ _ _
    (identitySpecialOrthogonalTangentMeasurableSpace n)
    (identitySpecialOrthogonalTangentBorelSpace n) _ _ _
    (identitySpecialOrthogonalFixedTangentBasis n) (Pi.basisFun ℝ (Fin n))
  exact reindexMeasure.trans productMeasure

/-- The explicit identity tangent decomposition transports the fixed
higher-rank coordinate measure with exactly the reciprocal absolute
fixed-basis comparison determinant. -/
theorem map_identitySpecialOrthogonalTangentCoordinateMeasure_split
    (n : ℕ) :
    Measure.map (identitySpecialOrthogonalTangentContinuousLinearEquiv n)
        (identitySpecialOrthogonalTangentCoordinateMeasure (n + 1)) =
      (Real.toNNReal
        |identitySpecialOrthogonalTangentSplitDetScalar n|)⁻¹ •
        identitySpecialOrthogonalTangentProductCoordinateMeasure n := by
  letI : MeasurableSpace (identitySpecialOrthogonalTangent (n + 1)) :=
    identitySpecialOrthogonalTangentMeasurableSpace (n + 1)
  letI : MeasurableSpace (identitySpecialOrthogonalTangent n) :=
    identitySpecialOrthogonalTangentMeasurableSpace n
  letI : BorelSpace (identitySpecialOrthogonalTangent (n + 1)) :=
    identitySpecialOrthogonalTangentBorelSpace (n + 1)
  letI : BorelSpace (identitySpecialOrthogonalTangent n) :=
    identitySpecialOrthogonalTangentBorelSpace n
  letI : BorelSpace (identitySpecialOrthogonalTangent n × (Fin n → ℝ)) :=
    Prod.borelSpace
  simpa only [identitySpecialOrthogonalTangentCoordinateMeasure,
    identitySpecialOrthogonalTangentProductCoordinateMeasure,
    identitySpecialOrthogonalTangentSplitDetScalar,
    identitySpecialOrthogonalTangentSplitTransportedBasis] using
      @Module.Basis.map_addHaar_eq_inv_abs_det_map_smul _
        (identitySpecialOrthogonalTangent (n + 1))
        (identitySpecialOrthogonalTangent n × (Fin n → ℝ)) _ _ _ _ _ _
        (identitySpecialOrthogonalTangentMeasurableSpace (n + 1))
        (identitySpecialOrthogonalTangentBorelSpace (n + 1)) _
        (identitySpecialOrthogonalTangentProductBorelSpace n) _ _
        (identitySpecialOrthogonalFixedTangentBasis (n + 1))
        (identitySpecialOrthogonalTangentProductBasis n)
        (identitySpecialOrthogonalTangentContinuousLinearEquiv n)

/-- Combined form of the identity tangent measure transport, with the product
measure exposed on the target. -/
theorem map_identitySpecialOrthogonalTangentCoordinateMeasure_split_eq_prod
    (n : ℕ) :
    Measure.map (identitySpecialOrthogonalTangentContinuousLinearEquiv n)
        (identitySpecialOrthogonalTangentCoordinateMeasure (n + 1)) =
      (Real.toNNReal
        |identitySpecialOrthogonalTangentSplitDetScalar n|)⁻¹ •
        ((identitySpecialOrthogonalTangentCoordinateMeasure n).prod
          (Pi.basisFun ℝ (Fin n)).addHaar) := by
  rw [map_identitySpecialOrthogonalTangentCoordinateMeasure_split,
    identitySpecialOrthogonalTangentProductCoordinateMeasure_eq_prod]

end PositiveDefiniteIntegralLattice

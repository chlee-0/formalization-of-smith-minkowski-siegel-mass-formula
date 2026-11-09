import SMSFormula.RationalQuadraticIsometryGeneralSpinPadicCentralFiberOverlapMeasure

/-!
# Product measures on the common p-adic presentation-chart group source

The transported and ambient selected central-fiber charts identify their
genuine common group source with the two exact target-coordinate overlaps.
Pulling the already compared target product measures through these two
homeomorphisms gives two measures on one literal group-source subtype.  They
differ by the reciprocal p-adic tangent modulus.

No full chart domains are equated and no directed finite cylinder is used.
-/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)
variable (p : ℕ) [Fact (Nat.Prime p)]

/-- The transported selected chart identifies the common group source with
its exact transported-coordinate target overlap. -/
def transportedPadicCentralFiberSourceOverlapHomeomorphTarget
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    P.transportedAmbientPadicCentralFiberSourceOverlap p hx ≃ₜ
      P.transportedPadicCentralFiberTargetOverlap p hx where
  toFun g :=
    ⟨((P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p)
        |>.toHomeomorphSourceTarget ⟨g.1, g.2.1⟩).1,
      ⟨(P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).map_source
          g.2.1,
        by
          change
            (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).symm
                (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p g.1) ∈
              (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).source
          rw [(P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).left_inv
            g.2.1]
          exact g.2.2⟩⟩
  invFun y :=
    ⟨((P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p)
        |>.toHomeomorphSourceTarget.symm ⟨y.1, y.2.1⟩).1,
      ⟨(P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).symm.map_source
          y.2.1,
        y.2.2⟩⟩
  left_inv g := by
    apply Subtype.ext
    exact (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).left_inv
      g.2.1
  right_inv y := by
    apply Subtype.ext
    exact (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).right_inv
      y.2.1
  continuous_toFun := by
    apply Continuous.subtype_mk
    simpa only [Function.comp_apply] using
      (((P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p)
          |>.toHomeomorphSourceTarget.continuous.comp
            (continuous_subtype_val.subtype_mk
              (fun (g : P.transportedAmbientPadicCentralFiberSourceOverlap p hx) =>
                g.2.1))).subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    simpa only [Function.comp_apply] using
      (((P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p)
          |>.toHomeomorphSourceTarget.symm.continuous.comp
            (continuous_subtype_val.subtype_mk
              (fun (y : P.transportedPadicCentralFiberTargetOverlap p hx) =>
                y.2.1))).subtype_val)

/-- The ambient selected chart identifies the same common group source with
its exact ambient-coordinate target overlap. -/
def ambientPadicCentralFiberSourceOverlapHomeomorphTarget
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    P.transportedAmbientPadicCentralFiberSourceOverlap p hx ≃ₜ
      P.ambientPadicCentralFiberTargetOverlap p hx where
  toFun g :=
    ⟨(V.padicCliffordGeneralSpinCentralFiberIdentityChart p
        |>.toHomeomorphSourceTarget ⟨g.1, g.2.2⟩).1,
      ⟨(V.padicCliffordGeneralSpinCentralFiberIdentityChart p).map_source g.2.2,
        by
          change
            (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).symm
                (V.padicCliffordGeneralSpinCentralFiberIdentityChart p g.1) ∈
              (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).source
          rw [(V.padicCliffordGeneralSpinCentralFiberIdentityChart p).left_inv g.2.2]
          exact g.2.1⟩⟩
  invFun y :=
    ⟨(V.padicCliffordGeneralSpinCentralFiberIdentityChart p
        |>.toHomeomorphSourceTarget.symm ⟨y.1, y.2.1⟩).1,
      ⟨y.2.2,
        (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).symm.map_source
          y.2.1⟩⟩
  left_inv g := by
    apply Subtype.ext
    exact (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).left_inv g.2.2
  right_inv y := by
    apply Subtype.ext
    exact (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).right_inv y.2.1
  continuous_toFun := by
    apply Continuous.subtype_mk
    simpa only [Function.comp_apply] using
      ((V.padicCliffordGeneralSpinCentralFiberIdentityChart p
        |>.toHomeomorphSourceTarget.continuous.comp
          (continuous_subtype_val.subtype_mk
            (fun (g : P.transportedAmbientPadicCentralFiberSourceOverlap p hx) =>
              g.2.2))).subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    simpa only [Function.comp_apply] using
      ((V.padicCliffordGeneralSpinCentralFiberIdentityChart p
        |>.toHomeomorphSourceTarget.symm.continuous.comp
          (continuous_subtype_val.subtype_mk
            (fun (y : P.ambientPadicCentralFiberTargetOverlap p hx) =>
              y.2.1))).subtype_val)

/-- The target cross-chart square commutes on the exact common group source. -/
theorem transportedAmbientPadicCentralFiberSourceOverlapHomeomorph_commutes
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (g : P.transportedAmbientPadicCentralFiberSourceOverlap p hx) :
    P.transportedAmbientPadicCentralFiberTargetOverlapHomeomorph p hx
        (P.transportedPadicCentralFiberSourceOverlapHomeomorphTarget p hx g) =
      P.ambientPadicCentralFiberSourceOverlapHomeomorphTarget p hx g := by
  apply Subtype.ext
  rw [P.transportedAmbientPadicCentralFiberTargetOverlapHomeomorph_apply p hx]
  exact P.blockToAmbientTransportedPadicCentralFiberIdentityChart_eq_ambient_apply
    p hx g.1

/-- The transported fixed product measure pulled back to the genuine common
group source through the transported selected chart. -/
def transportedPadicCentralFiberSourceOverlapProductMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure (P.transportedAmbientPadicCentralFiberSourceOverlap p hx) :=
  Measure.map
    (P.transportedPadicCentralFiberSourceOverlapHomeomorphTarget p hx).symm
    (P.transportedPadicCentralFiberTargetOverlapProductMeasure p hx)

/-- The ambient fixed product measure pulled back to the same common group
source through the ambient selected chart. -/
def ambientPadicCentralFiberSourceOverlapProductMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure (P.transportedAmbientPadicCentralFiberSourceOverlap p hx) :=
  Measure.map
    (P.ambientPadicCentralFiberSourceOverlapHomeomorphTarget p hx).symm
    (P.ambientPadicCentralFiberTargetOverlapProductMeasure p hx)

/-- The transported chart sends its source-overlap product measure back to
the exact transported target product measure. -/
theorem map_transportedPadicCentralFiberSourceOverlapProductMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure.map
        (P.transportedPadicCentralFiberSourceOverlapHomeomorphTarget p hx)
        (P.transportedPadicCentralFiberSourceOverlapProductMeasure p hx) =
      P.transportedPadicCentralFiberTargetOverlapProductMeasure p hx := by
  rw [transportedPadicCentralFiberSourceOverlapProductMeasure]
  exact MeasurableEquiv.map_map_symm
    (P.transportedPadicCentralFiberSourceOverlapHomeomorphTarget p hx
      |>.toMeasurableEquiv)

/-- The ambient chart sends its source-overlap product measure back to the
exact ambient target product measure. -/
theorem map_ambientPadicCentralFiberSourceOverlapProductMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure.map
        (P.ambientPadicCentralFiberSourceOverlapHomeomorphTarget p hx)
        (P.ambientPadicCentralFiberSourceOverlapProductMeasure p hx) =
      P.ambientPadicCentralFiberTargetOverlapProductMeasure p hx := by
  rw [ambientPadicCentralFiberSourceOverlapProductMeasure]
  exact MeasurableEquiv.map_map_symm
    (P.ambientPadicCentralFiberSourceOverlapHomeomorphTarget p hx
      |>.toMeasurableEquiv)

/-- On their literal common group-source subtype, the two selected-chart
product measures differ by the reciprocal p-adic tangent modulus. -/
theorem transportedPadicCentralFiberSourceOverlapProductMeasure_eq_smul
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    P.transportedPadicCentralFiberSourceOverlapProductMeasure p hx =
      ‖algebraMap ℚ ℚ_[p]
          (P.blockToAmbientSkewAdjointDetScalar hx)‖₊⁻¹ •
        P.ambientPadicCentralFiberSourceOverlapProductMeasure p hx := by
  let a := P.transportedPadicCentralFiberSourceOverlapHomeomorphTarget p hx
  let b := P.ambientPadicCentralFiberSourceOverlapHomeomorphTarget p hx
  let e := P.transportedAmbientPadicCentralFiberTargetOverlapHomeomorph p hx
  let μ := P.transportedPadicCentralFiberSourceOverlapProductMeasure p hx
  let ν := P.ambientPadicCentralFiberSourceOverlapProductMeasure p hx
  let q : ℝ≥0 :=
    ‖algebraMap ℚ ℚ_[p] (P.blockToAmbientSkewAdjointDetScalar hx)‖₊⁻¹
  apply b.toMeasurableEquiv.measurableEmbedding.map_injective
  have hba : (fun g => b g) = (fun g => e (a g)) := by
    funext g
    exact (P.transportedAmbientPadicCentralFiberSourceOverlapHomeomorph_commutes
      p hx g).symm
  calc
    Measure.map b μ = Measure.map e (Measure.map a μ) := by
      rw [Measure.map_map e.measurable a.measurable]
      apply Measure.map_congr
      filter_upwards with g
      exact congrFun hba g
    _ = Measure.map e
        (P.transportedPadicCentralFiberTargetOverlapProductMeasure p hx) := by
      rw [P.map_transportedPadicCentralFiberSourceOverlapProductMeasure p hx]
    _ = q • P.ambientPadicCentralFiberTargetOverlapProductMeasure p hx :=
      P.map_transportedPadicCentralFiberTargetOverlapProductMeasure p hx
    _ = q • Measure.map b ν := by
      rw [P.map_ambientPadicCentralFiberSourceOverlapProductMeasure p hx]
    _ = Measure.map b (q • ν) := by
      rw [Measure.map_smul]

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

end

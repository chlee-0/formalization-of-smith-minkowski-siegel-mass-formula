import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProduct
import SMSFormula.SpecialOrthogonalRealIdentityLastColumnHomogeneousSpace
import SMSFormula.SpecialOrthogonalRealIdentityMappedGroupEquiv

/-!
# Inverse architecture for the identity north-pole product chart

This module packages the exact-domain north-pole product matrix in the
literal identity special-orthogonal group and recovers its lower-rank and
sphere coordinates.  It does not construct a local homeomorphism or compare
measures.
-/

open scoped Matrix Matrix.Norms.Operator Topology

noncomputable section

open Matrix

namespace PositiveDefiniteIntegralLattice

/-- The lower-rank literal identity-form point represented by a native
identity-chart coordinate. -/
def identitySpecialOrthogonalLowerChartRankGroup
    (n : ℕ) (X : identitySpecialOrthogonalLowerChartTargetSet n) :
    identitySpecialOrthogonalRankGroup n :=
  identitySpecialOrthogonalMappedIdentityGroupToLiteral n
    (identitySpecialOrthogonalLowerChartGroup n X)

@[simp]
theorem coe_identitySpecialOrthogonalLowerChartRankGroup
    (n : ℕ) (X : identitySpecialOrthogonalLowerChartTargetSet n) :
    (identitySpecialOrthogonalLowerChartRankGroup n X).1.1.1 =
      identitySpecialOrthogonalLowerInverseCoordinateMatrix n X.1 := by
  rw [identitySpecialOrthogonalLowerChartRankGroup,
    coe_identitySpecialOrthogonalMappedIdentityGroupToLiteral,
    coe_identitySpecialOrthogonalLowerChartGroup]

/-- The exact product-coordinate domain as a subtype. -/
abbrev identitySpecialOrthogonalNorthPoleProductDomain (n : ℕ) :=
  identitySpecialOrthogonalNorthPoleProductDomainSet n

/-- The group-valued north-pole product on its exact domain. -/
def identitySpecialOrthogonalNorthPoleProduct
    (n : ℕ) (p : identitySpecialOrthogonalNorthPoleProductDomain n) :
    identitySpecialOrthogonalGroup n :=
  identitySpecialOrthogonalNorthPoleSection n ⟨p.1.2, p.2.2⟩ *
    identitySpecialOrthogonalLastColumnFiberEmbedGroup n
      (identitySpecialOrthogonalLowerChartRankGroup n ⟨p.1.1, p.2.1⟩)

@[simp]
theorem coe_identitySpecialOrthogonalNorthPoleProduct
    (n : ℕ) (p : identitySpecialOrthogonalNorthPoleProductDomain n) :
    (identitySpecialOrthogonalNorthPoleProduct n p).1.1.1 =
      identitySpecialOrthogonalNorthPoleProductMatrix n p.1 := by
  rw [identitySpecialOrthogonalNorthPoleProduct,
    identitySpecialOrthogonalNorthPoleProductMatrix]
  change
    (identitySpecialOrthogonalNorthPoleSection n ⟨p.1.2, p.2.2⟩).1.1.1 *
        (identitySpecialOrthogonalLastColumnFiberEmbedGroup n
          (identitySpecialOrthogonalLowerChartRankGroup n
            ⟨p.1.1, p.2.1⟩)).1.1.1 =
      _
  rw [coe_identitySpecialOrthogonalNorthPoleSection,
    coe_identitySpecialOrthogonalLastColumnFiberEmbedGroup,
    coe_identitySpecialOrthogonalLowerChartRankGroup]
  rfl

theorem identitySpecialOrthogonalLastColumn_northPoleProduct
    (n : ℕ) (p : identitySpecialOrthogonalNorthPoleProductDomain n) :
    identitySpecialOrthogonalLastColumn n
        (identitySpecialOrthogonalNorthPoleProduct n p) =
      identitySpecialOrthogonalNorthPoleInverse n ⟨p.1.2, p.2.2⟩ := by
  apply Subtype.ext
  ext i
  rw [coe_identitySpecialOrthogonalLastColumn,
    coe_identitySpecialOrthogonalNorthPoleInverse,
    identitySpecialOrthogonalLastColumnVector,
    coe_identitySpecialOrthogonalNorthPoleProduct]
  exact identitySpecialOrthogonalNorthPoleProductMatrix_lastColumn
    n p.1.1 p.1.2 i

/-- The ambient identity group points whose last column lies in the positive
north-pole hemisphere. -/
def identitySpecialOrthogonalNorthPoleGroupSet (n : ℕ) :
    Set (identitySpecialOrthogonalGroup n) :=
  identitySpecialOrthogonalLastColumn n ⁻¹'
    identitySpecialOrthogonalNorthPoleHemisphere n

/-- The positive-hemisphere group domain as a subtype. -/
abbrev identitySpecialOrthogonalNorthPoleGroupDomain (n : ℕ) :=
  identitySpecialOrthogonalNorthPoleGroupSet n

theorem isOpen_identitySpecialOrthogonalNorthPoleGroupSet (n : ℕ) :
    IsOpen (identitySpecialOrthogonalNorthPoleGroupSet n) :=
  (isOpen_identitySpecialOrthogonalNorthPoleHemisphere n).preimage
    (continuous_identitySpecialOrthogonalLastColumn n)

/-- Recover the open-ball coordinate from a positive-hemisphere group point.
-/
def identitySpecialOrthogonalNorthPoleRecoveredCoordinate
    (n : ℕ) (g : identitySpecialOrthogonalNorthPoleGroupDomain n) :
    Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  ⟨identitySpecialOrthogonalNorthPoleCoordinate n
      (identitySpecialOrthogonalLastColumn n g.1),
    identitySpecialOrthogonalNorthPoleCoordinate_mem_ball n
      (identitySpecialOrthogonalLastColumn n g.1) g.2⟩

/-- A product-domain point, regarded in the positive-hemisphere group
domain. -/
def identitySpecialOrthogonalNorthPoleProductToGroupDomain
    (n : ℕ) (p : identitySpecialOrthogonalNorthPoleProductDomain n) :
    identitySpecialOrthogonalNorthPoleGroupDomain n :=
  ⟨identitySpecialOrthogonalNorthPoleProduct n p, by
    change
      identitySpecialOrthogonalLastColumn n
          (identitySpecialOrthogonalNorthPoleProduct n p) ∈
        identitySpecialOrthogonalNorthPoleHemisphere n
    rw [identitySpecialOrthogonalLastColumn_northPoleProduct]
    exact identitySpecialOrthogonalNorthPoleInverse_mem_hemisphere
      n ⟨p.1.2, p.2.2⟩⟩

@[simp]
theorem identitySpecialOrthogonalNorthPoleRecoveredCoordinate_product
    (n : ℕ) (p : identitySpecialOrthogonalNorthPoleProductDomain n) :
    identitySpecialOrthogonalNorthPoleRecoveredCoordinate n
        (identitySpecialOrthogonalNorthPoleProductToGroupDomain n p) =
      ⟨p.1.2, p.2.2⟩ := by
  apply Subtype.ext
  change
    identitySpecialOrthogonalNorthPoleCoordinate n
        (identitySpecialOrthogonalLastColumn n
          (identitySpecialOrthogonalNorthPoleProduct n p)) = p.1.2
  rw [identitySpecialOrthogonalLastColumn_northPoleProduct]
  exact identitySpecialOrthogonalNorthPoleCoordinate_inverse
    n ⟨p.1.2, p.2.2⟩

/-- Remove the canonical section from a positive-hemisphere group point. -/
def identitySpecialOrthogonalNorthPoleCorrectedGroup
    (n : ℕ) (g : identitySpecialOrthogonalNorthPoleGroupDomain n) :
    identitySpecialOrthogonalGroup n :=
  (identitySpecialOrthogonalNorthPoleSection n
      (identitySpecialOrthogonalNorthPoleRecoveredCoordinate n g))⁻¹ * g.1

theorem identitySpecialOrthogonalNorthPoleCorrectedGroup_mem_fiber
    (n : ℕ) (g : identitySpecialOrthogonalNorthPoleGroupDomain n) :
    identitySpecialOrthogonalNorthPoleCorrectedGroup n g ∈
      identitySpecialOrthogonalLastColumnFiber n := by
  let s :=
    identitySpecialOrthogonalNorthPoleSection n
      (identitySpecialOrthogonalNorthPoleRecoveredCoordinate n g)
  have hcol :
      identitySpecialOrthogonalLastColumn n s =
        identitySpecialOrthogonalLastColumn n g.1 := by
    rw [identitySpecialOrthogonalLastColumn_northPoleSection]
    apply Subtype.ext
    exact identitySpecialOrthogonalNorthPoleInverse_coordinate n
      (identitySpecialOrthogonalLastColumn n g.1) g.2
  have hrel :
      QuotientGroup.leftRel
          (identitySpecialOrthogonalLastColumnStabilizerSubgroup n) s g.1 :=
    (identitySpecialOrthogonalLastColumn_leftRel_iff n s g.1).mpr hcol
  apply
    (mem_identitySpecialOrthogonalLastColumnStabilizerSubgroup_iff
      n (s⁻¹ * g.1)).mp
  simpa only [QuotientGroup.leftRel_apply] using hrel

/-- The corrected point together with its exact north-pole fiber proof. -/
def identitySpecialOrthogonalNorthPoleCorrectedFiberPoint
    (n : ℕ) (g : identitySpecialOrthogonalNorthPoleGroupDomain n) :
    {h : identitySpecialOrthogonalGroup n //
      h ∈ identitySpecialOrthogonalLastColumnFiber n} :=
  ⟨identitySpecialOrthogonalNorthPoleCorrectedGroup n g,
    identitySpecialOrthogonalNorthPoleCorrectedGroup_mem_fiber n g⟩

/-- Extract the lower-rank literal identity-form group point after removing
the north-pole section. -/
def identitySpecialOrthogonalNorthPoleRecoveredLowerGroup
    (n : ℕ) (g : identitySpecialOrthogonalNorthPoleGroupDomain n) :
    identitySpecialOrthogonalRankGroup n :=
  identitySpecialOrthogonalLastColumnFiberExtract n
    (identitySpecialOrthogonalNorthPoleCorrectedFiberPoint n g)

@[simp]
theorem coe_identitySpecialOrthogonalNorthPoleRecoveredLowerGroup
    (n : ℕ) (g : identitySpecialOrthogonalNorthPoleGroupDomain n) :
    (identitySpecialOrthogonalNorthPoleRecoveredLowerGroup n g).1.1.1 =
      identitySpecialOrthogonalUpperLeftBlock n
        (identitySpecialOrthogonalNorthPoleCorrectedGroup n g).1.1.1 := by
  rw [identitySpecialOrthogonalNorthPoleRecoveredLowerGroup,
    coe_identitySpecialOrthogonalLastColumnFiberExtract]
  rfl

/-- The same recovered lower-rank point on the native scalar-extended
rational identity-form carrier. -/
def identitySpecialOrthogonalNorthPoleRecoveredMappedLowerGroup
    (n : ℕ) (g : identitySpecialOrthogonalNorthPoleGroupDomain n) :
    specialFormPreservingMatrixSubgroup
      ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ)) :=
  identitySpecialOrthogonalLiteralIdentityGroupToMapped n
    (identitySpecialOrthogonalNorthPoleRecoveredLowerGroup n g)

/-- Apply the native lower-rank identity chart to the recovered block. -/
def identitySpecialOrthogonalNorthPoleRecoveredLowerCoordinate
    (n : ℕ) (g : identitySpecialOrthogonalNorthPoleGroupDomain n) :
    identitySpecialOrthogonalMappedTangent n :=
  specialFormPreservingSmoothRealIdentityChart
      (1 : Matrix (Fin n) (Fin n) ℚ)
      identityRationalForm_isSymm identityRationalForm_det_ne_zero
    (identitySpecialOrthogonalNorthPoleRecoveredMappedLowerGroup n g)

@[simp]
theorem identitySpecialOrthogonalNorthPoleCorrectedGroup_product
    (n : ℕ) (p : identitySpecialOrthogonalNorthPoleProductDomain n) :
    identitySpecialOrthogonalNorthPoleCorrectedGroup n
        (identitySpecialOrthogonalNorthPoleProductToGroupDomain n p) =
      identitySpecialOrthogonalLastColumnFiberEmbedGroup n
        (identitySpecialOrthogonalLowerChartRankGroup n
          ⟨p.1.1, p.2.1⟩) := by
  rw [identitySpecialOrthogonalNorthPoleCorrectedGroup,
    identitySpecialOrthogonalNorthPoleRecoveredCoordinate_product]
  change
    (identitySpecialOrthogonalNorthPoleSection n ⟨p.1.2, p.2.2⟩)⁻¹ *
        identitySpecialOrthogonalNorthPoleProduct n p = _
  rw [identitySpecialOrthogonalNorthPoleProduct]
  group

@[simp]
theorem identitySpecialOrthogonalNorthPoleRecoveredLowerGroup_product
    (n : ℕ) (p : identitySpecialOrthogonalNorthPoleProductDomain n) :
    identitySpecialOrthogonalNorthPoleRecoveredLowerGroup n
        (identitySpecialOrthogonalNorthPoleProductToGroupDomain n p) =
      identitySpecialOrthogonalLowerChartRankGroup n
        ⟨p.1.1, p.2.1⟩ := by
  let h :=
    identitySpecialOrthogonalLowerChartRankGroup n ⟨p.1.1, p.2.1⟩
  have hfiber :
      identitySpecialOrthogonalNorthPoleCorrectedFiberPoint n
          (identitySpecialOrthogonalNorthPoleProductToGroupDomain n p) =
        identitySpecialOrthogonalLastColumnFiberEmbed n h := by
    apply Subtype.ext
    exact identitySpecialOrthogonalNorthPoleCorrectedGroup_product n p
  rw [identitySpecialOrthogonalNorthPoleRecoveredLowerGroup, hfiber]
  exact identitySpecialOrthogonalLastColumnFiberExtract_embed n h

@[simp]
theorem identitySpecialOrthogonalNorthPoleRecoveredMappedLowerGroup_product
    (n : ℕ) (p : identitySpecialOrthogonalNorthPoleProductDomain n) :
    identitySpecialOrthogonalNorthPoleRecoveredMappedLowerGroup n
        (identitySpecialOrthogonalNorthPoleProductToGroupDomain n p) =
      identitySpecialOrthogonalLowerChartGroup n ⟨p.1.1, p.2.1⟩ := by
  rw [identitySpecialOrthogonalNorthPoleRecoveredMappedLowerGroup,
    identitySpecialOrthogonalNorthPoleRecoveredLowerGroup_product,
    identitySpecialOrthogonalLowerChartRankGroup,
    identitySpecialOrthogonalMappedIdentityGroupToLiteral_leftInverse]

@[simp]
theorem identitySpecialOrthogonalNorthPoleRecoveredLowerCoordinate_product
    (n : ℕ) (p : identitySpecialOrthogonalNorthPoleProductDomain n) :
    identitySpecialOrthogonalNorthPoleRecoveredLowerCoordinate n
        (identitySpecialOrthogonalNorthPoleProductToGroupDomain n p) =
      p.1.1 := by
  rw [identitySpecialOrthogonalNorthPoleRecoveredLowerCoordinate,
    identitySpecialOrthogonalNorthPoleRecoveredMappedLowerGroup_product,
    identitySpecialOrthogonalLowerChartGroup]
  exact
    (specialFormPreservingSmoothRealIdentityChart
      (1 : Matrix (Fin n) (Fin n) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero).right_inv p.2.1

end PositiveDefiniteIntegralLattice

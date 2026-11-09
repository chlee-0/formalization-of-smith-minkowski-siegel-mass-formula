import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductInverse

/-!
# Local inverse for the identity north-pole product

This module restricts the positive-hemisphere inverse architecture to points
whose recovered lower-rank block lies in the native identity-chart source.
On that exact open domain, the north-pole product and recovered coordinates
are inverse continuous maps.

No nonlinear measure transport or density evaluation is introduced.
-/

open scoped Matrix Matrix.Norms.Operator Topology

noncomputable section

open Matrix

namespace PositiveDefiniteIntegralLattice

theorem continuous_identitySpecialOrthogonalNorthPoleSection (n : ℕ) :
    Continuous (identitySpecialOrthogonalNorthPoleSection n) := by
  have hmatrix :
      Continuous
        (fun v : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 =>
          identitySpecialOrthogonalNorthPoleSectionMatrix n v.1) :=
    (continuous_identitySpecialOrthogonalNorthPoleSectionMatrix n).comp
      continuous_subtype_val
  have hcarrier :
      Continuous
        (fun v : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 =>
          (⟨identitySpecialOrthogonalNorthPoleSectionMatrix n v.1,
            by
              constructor
              · apply (Matrix.formPreservingConstraint_eq_zero_iff _ _).mpr
                change
                  (identitySpecialOrthogonalNorthPoleSectionMatrix n v.1)ᵀ *
                      1 *
                      identitySpecialOrthogonalNorthPoleSectionMatrix n v.1 =
                    1
                simpa using
                  identitySpecialOrthogonalNorthPoleSectionMatrix_transpose_mul_self
                    n v.1 v.2
              · exact
                  identitySpecialOrthogonalNorthPoleSectionMatrix_det
                    n v.1 v.2⟩ :
            Matrix.specialOrthogonalMatrixSet
              (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))) :=
    hmatrix.subtype_mk _
  exact
    (continuous_specialOrthogonalMatrixSetToSpecialSubgroup
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)).comp hcarrier

theorem continuous_identitySpecialOrthogonalNorthPoleRecoveredCoordinate
    (n : ℕ) :
    Continuous (identitySpecialOrthogonalNorthPoleRecoveredCoordinate n) :=
  (((continuous_identitySpecialOrthogonalNorthPoleCoordinate n).comp
    ((continuous_identitySpecialOrthogonalLastColumn n).comp
      continuous_subtype_val)).subtype_mk _)

theorem continuous_identitySpecialOrthogonalNorthPoleCorrectedGroup
    (n : ℕ) :
    Continuous (identitySpecialOrthogonalNorthPoleCorrectedGroup n) := by
  exact
    (((continuous_identitySpecialOrthogonalNorthPoleSection n).comp
      (continuous_identitySpecialOrthogonalNorthPoleRecoveredCoordinate n)).inv).mul
        continuous_subtype_val

theorem continuous_identitySpecialOrthogonalNorthPoleCorrectedFiberPoint
    (n : ℕ) :
    Continuous (identitySpecialOrthogonalNorthPoleCorrectedFiberPoint n) :=
  (continuous_identitySpecialOrthogonalNorthPoleCorrectedGroup n).subtype_mk _

theorem continuous_identitySpecialOrthogonalNorthPoleRecoveredLowerGroup
    (n : ℕ) :
    Continuous (identitySpecialOrthogonalNorthPoleRecoveredLowerGroup n) :=
  (continuous_identitySpecialOrthogonalLastColumnFiberExtract n).comp
    (continuous_identitySpecialOrthogonalNorthPoleCorrectedFiberPoint n)

theorem
    continuous_identitySpecialOrthogonalNorthPoleRecoveredMappedLowerGroup
    (n : ℕ) :
    Continuous
      (identitySpecialOrthogonalNorthPoleRecoveredMappedLowerGroup n) :=
  (continuous_identitySpecialOrthogonalLiteralIdentityGroupToMapped n).comp
    (continuous_identitySpecialOrthogonalNorthPoleRecoveredLowerGroup n)

/-- Positive-hemisphere points whose recovered native lower-rank block lies
in the source of the lower identity chart. -/
def identitySpecialOrthogonalNorthPoleCommonDomainSet (n : ℕ) :
    Set (identitySpecialOrthogonalNorthPoleGroupDomain n) :=
  (identitySpecialOrthogonalNorthPoleRecoveredMappedLowerGroup n) ⁻¹'
    (specialFormPreservingSmoothRealIdentityChart
      (1 : Matrix (Fin n) (Fin n) ℚ)
      identityRationalForm_isSymm identityRationalForm_det_ne_zero).source

theorem isOpen_identitySpecialOrthogonalNorthPoleCommonDomainSet (n : ℕ) :
    IsOpen (identitySpecialOrthogonalNorthPoleCommonDomainSet n) :=
  (specialFormPreservingSmoothRealIdentityChart
    (1 : Matrix (Fin n) (Fin n) ℚ)
    identityRationalForm_isSymm
    identityRationalForm_det_ne_zero).open_source.preimage
      (continuous_identitySpecialOrthogonalNorthPoleRecoveredMappedLowerGroup n)

/-- The exact common group domain for the local inverse. -/
abbrev identitySpecialOrthogonalNorthPoleCommonDomain (n : ℕ) :=
  identitySpecialOrthogonalNorthPoleCommonDomainSet n

/-- The identity group point, regarded in the positive-hemisphere domain. -/
def identitySpecialOrthogonalNorthPoleGroupIdentity (n : ℕ) :
    identitySpecialOrthogonalNorthPoleGroupDomain n :=
  ⟨1, by
    change
      identitySpecialOrthogonalLastColumn n 1 ∈
        identitySpecialOrthogonalNorthPoleHemisphere n
    exact identitySpecialOrthogonalNorthPole_mem_hemisphere n⟩

@[simp]
theorem identitySpecialOrthogonalNorthPoleRecoveredCoordinate_identity
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleRecoveredCoordinate n
        (identitySpecialOrthogonalNorthPoleGroupIdentity n) =
      ⟨0, by simp⟩ := by
  apply Subtype.ext
  change
    identitySpecialOrthogonalNorthPoleCoordinate n
        (identitySpecialOrthogonalLastColumn n 1) = 0
  exact identitySpecialOrthogonalNorthPoleCoordinate_northPole n

@[simp]
theorem identitySpecialOrthogonalNorthPoleCorrectedGroup_identity
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleCorrectedGroup n
        (identitySpecialOrthogonalNorthPoleGroupIdentity n) = 1 := by
  change
    (identitySpecialOrthogonalNorthPoleSection n
      (identitySpecialOrthogonalNorthPoleRecoveredCoordinate n
        (identitySpecialOrthogonalNorthPoleGroupIdentity n)))⁻¹ * 1 = 1
  rw [
    identitySpecialOrthogonalNorthPoleRecoveredCoordinate_identity,
    identitySpecialOrthogonalNorthPoleSection_zero]
  simp

@[simp]
theorem identitySpecialOrthogonalNorthPoleRecoveredLowerGroup_identity
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleRecoveredLowerGroup n
        (identitySpecialOrthogonalNorthPoleGroupIdentity n) = 1 := by
  have hfiber :
      identitySpecialOrthogonalNorthPoleCorrectedFiberPoint n
          (identitySpecialOrthogonalNorthPoleGroupIdentity n) =
        identitySpecialOrthogonalLastColumnFiberEmbed n 1 := by
    apply Subtype.ext
    change
      identitySpecialOrthogonalNorthPoleCorrectedGroup n
          (identitySpecialOrthogonalNorthPoleGroupIdentity n) =
        identitySpecialOrthogonalLastColumnFiberEmbedGroup n 1
    rw [identitySpecialOrthogonalNorthPoleCorrectedGroup_identity]
    exact
      (identitySpecialOrthogonalLastColumnFiberEmbedHom n).map_one.symm
  rw [identitySpecialOrthogonalNorthPoleRecoveredLowerGroup, hfiber]
  exact identitySpecialOrthogonalLastColumnFiberExtract_embed n 1

@[simp]
theorem identitySpecialOrthogonalLiteralIdentityGroupToMapped_one
    (n : ℕ) :
    identitySpecialOrthogonalLiteralIdentityGroupToMapped n 1 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  rfl

@[simp]
theorem identitySpecialOrthogonalNorthPoleRecoveredMappedLowerGroup_identity
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleRecoveredMappedLowerGroup n
        (identitySpecialOrthogonalNorthPoleGroupIdentity n) = 1 := by
  rw [identitySpecialOrthogonalNorthPoleRecoveredMappedLowerGroup,
    identitySpecialOrthogonalNorthPoleRecoveredLowerGroup_identity,
    identitySpecialOrthogonalLiteralIdentityGroupToMapped_one]

theorem identitySpecialOrthogonalNorthPoleGroupIdentity_mem_common
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleGroupIdentity n ∈
      identitySpecialOrthogonalNorthPoleCommonDomainSet n := by
  change
    identitySpecialOrthogonalNorthPoleRecoveredMappedLowerGroup n
        (identitySpecialOrthogonalNorthPoleGroupIdentity n) ∈
      (specialFormPreservingSmoothRealIdentityChart
        (1 : Matrix (Fin n) (Fin n) ℚ)
        identityRationalForm_isSymm
        identityRationalForm_det_ne_zero).source
  rw [identitySpecialOrthogonalNorthPoleRecoveredMappedLowerGroup_identity]
  exact self_mem_specialFormPreservingSmoothRealChart_source
    (1 : Matrix (Fin n) (Fin n) ℚ)
    identityRationalForm_isSymm identityRationalForm_det_ne_zero 1

/-- The identity point in the exact common group domain. -/
def identitySpecialOrthogonalNorthPoleCommonIdentity (n : ℕ) :
    identitySpecialOrthogonalNorthPoleCommonDomain n :=
  ⟨identitySpecialOrthogonalNorthPoleGroupIdentity n,
    identitySpecialOrthogonalNorthPoleGroupIdentity_mem_common n⟩

theorem continuous_identitySpecialOrthogonalNorthPoleCommonLowerCoordinate
    (n : ℕ) :
    Continuous
      (fun g : identitySpecialOrthogonalNorthPoleCommonDomain n =>
        identitySpecialOrthogonalNorthPoleRecoveredLowerCoordinate n g.1) := by
  let A :=
    specialFormPreservingSmoothRealIdentityChart
      (1 : Matrix (Fin n) (Fin n) ℚ)
      identityRationalForm_isSymm identityRationalForm_det_ne_zero
  exact
    A.continuousOn.comp_continuous
      ((continuous_identitySpecialOrthogonalNorthPoleRecoveredMappedLowerGroup
        n).comp continuous_subtype_val)
      (fun g => g.2)

theorem continuous_identitySpecialOrthogonalNorthPoleCommonBallCoordinate
    (n : ℕ) :
    Continuous
      (fun g : identitySpecialOrthogonalNorthPoleCommonDomain n =>
        identitySpecialOrthogonalNorthPoleRecoveredCoordinate n g.1) :=
  (continuous_identitySpecialOrthogonalNorthPoleRecoveredCoordinate n).comp
    continuous_subtype_val

/-- The recovered lower and ball coordinates on the exact common group
domain, valued in the exact product domain. -/
def identitySpecialOrthogonalNorthPoleCommonToProduct
    (n : ℕ) (g : identitySpecialOrthogonalNorthPoleCommonDomain n) :
    identitySpecialOrthogonalNorthPoleProductDomain n :=
  ⟨(identitySpecialOrthogonalNorthPoleRecoveredLowerCoordinate n g.1,
      (identitySpecialOrthogonalNorthPoleRecoveredCoordinate n g.1).1),
    ⟨(specialFormPreservingSmoothRealIdentityChart
        (1 : Matrix (Fin n) (Fin n) ℚ)
        identityRationalForm_isSymm
        identityRationalForm_det_ne_zero).map_source g.2,
      (identitySpecialOrthogonalNorthPoleRecoveredCoordinate n g.1).2⟩⟩

theorem continuous_identitySpecialOrthogonalNorthPoleCommonToProduct
    (n : ℕ) :
    Continuous (identitySpecialOrthogonalNorthPoleCommonToProduct n) := by
  exact
    ((continuous_identitySpecialOrthogonalNorthPoleCommonLowerCoordinate n).prodMk
      (continuous_subtype_val.comp
        (continuous_identitySpecialOrthogonalNorthPoleCommonBallCoordinate
          n))).subtype_mk _

theorem continuous_identitySpecialOrthogonalLowerChartGroup (n : ℕ) :
    Continuous (identitySpecialOrthogonalLowerChartGroup n) := by
  exact continuousOn_iff_continuous_restrict.mp
    (specialFormPreservingSmoothRealIdentityChart
      (1 : Matrix (Fin n) (Fin n) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero).symm.continuousOn

theorem continuous_identitySpecialOrthogonalLowerChartRankGroup (n : ℕ) :
    Continuous (identitySpecialOrthogonalLowerChartRankGroup n) :=
  (continuous_identitySpecialOrthogonalMappedIdentityGroupToLiteral n).comp
    (continuous_identitySpecialOrthogonalLowerChartGroup n)

theorem continuous_identitySpecialOrthogonalNorthPoleProduct (n : ℕ) :
    Continuous (identitySpecialOrthogonalNorthPoleProduct n) := by
  have hball :
      Continuous
        (fun p : identitySpecialOrthogonalNorthPoleProductDomain n =>
          (⟨p.1.2, p.2.2⟩ :
            Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) :=
    (continuous_snd.comp continuous_subtype_val).subtype_mk _
  have hlower :
      Continuous
        (fun p : identitySpecialOrthogonalNorthPoleProductDomain n =>
          identitySpecialOrthogonalLowerChartRankGroup n
            ⟨p.1.1, p.2.1⟩) :=
    (continuous_identitySpecialOrthogonalLowerChartRankGroup n).comp
      ((continuous_fst.comp continuous_subtype_val).subtype_mk _)
  exact
    ((continuous_identitySpecialOrthogonalNorthPoleSection n).comp hball).mul
      ((continuous_identitySpecialOrthogonalLastColumnFiberEmbedGroup n).comp
        hlower)

/-- Every exact product point lands in the common group domain. -/
def identitySpecialOrthogonalNorthPoleProductToCommon
    (n : ℕ) (p : identitySpecialOrthogonalNorthPoleProductDomain n) :
    identitySpecialOrthogonalNorthPoleCommonDomain n :=
  ⟨identitySpecialOrthogonalNorthPoleProductToGroupDomain n p, by
    change
      identitySpecialOrthogonalNorthPoleRecoveredMappedLowerGroup n
          (identitySpecialOrthogonalNorthPoleProductToGroupDomain n p) ∈
        (specialFormPreservingSmoothRealIdentityChart
          (1 : Matrix (Fin n) (Fin n) ℚ)
          identityRationalForm_isSymm
          identityRationalForm_det_ne_zero).source
    rw [identitySpecialOrthogonalNorthPoleRecoveredMappedLowerGroup_product]
    exact
      (specialFormPreservingSmoothRealIdentityChart
        (1 : Matrix (Fin n) (Fin n) ℚ)
        identityRationalForm_isSymm
        identityRationalForm_det_ne_zero).symm.map_source p.2.1⟩

theorem continuous_identitySpecialOrthogonalNorthPoleProductToCommon
    (n : ℕ) :
    Continuous (identitySpecialOrthogonalNorthPoleProductToCommon n) :=
  (((continuous_identitySpecialOrthogonalNorthPoleProduct n).subtype_mk _).subtype_mk _)

/-- Reattaching the canonical section to the extracted corrected fiber point
recovers every positive-hemisphere group point. -/
theorem identitySpecialOrthogonalNorthPoleSection_mul_recoveredLowerGroup
    (n : ℕ) (g : identitySpecialOrthogonalNorthPoleGroupDomain n) :
    identitySpecialOrthogonalNorthPoleSection n
          (identitySpecialOrthogonalNorthPoleRecoveredCoordinate n g) *
        identitySpecialOrthogonalLastColumnFiberEmbedGroup n
          (identitySpecialOrthogonalNorthPoleRecoveredLowerGroup n g) =
      g.1 := by
  have hfiber := congrArg Subtype.val
    (identitySpecialOrthogonalLastColumnFiberEmbed_extract n
      (identitySpecialOrthogonalNorthPoleCorrectedFiberPoint n g))
  change
    identitySpecialOrthogonalLastColumnFiberEmbedGroup n
        (identitySpecialOrthogonalNorthPoleRecoveredLowerGroup n g) =
      identitySpecialOrthogonalNorthPoleCorrectedGroup n g at hfiber
  rw [hfiber, identitySpecialOrthogonalNorthPoleCorrectedGroup]
  group

/-- On the common source, applying the lower chart and then its inverse
recovers the extracted literal lower-rank group. -/
theorem identitySpecialOrthogonalLowerChartRankGroup_recovered
    (n : ℕ) (g : identitySpecialOrthogonalNorthPoleCommonDomain n) :
    identitySpecialOrthogonalLowerChartRankGroup n
        ⟨identitySpecialOrthogonalNorthPoleRecoveredLowerCoordinate n g.1,
          (specialFormPreservingSmoothRealIdentityChart
            (1 : Matrix (Fin n) (Fin n) ℚ)
            identityRationalForm_isSymm
            identityRationalForm_det_ne_zero).map_source g.2⟩ =
      identitySpecialOrthogonalNorthPoleRecoveredLowerGroup n g.1 := by
  let A :=
    specialFormPreservingSmoothRealIdentityChart
      (1 : Matrix (Fin n) (Fin n) ℚ)
      identityRationalForm_isSymm identityRationalForm_det_ne_zero
  have hchart :
      A.symm
          (identitySpecialOrthogonalNorthPoleRecoveredLowerCoordinate n g.1) =
        identitySpecialOrthogonalNorthPoleRecoveredMappedLowerGroup n g.1 :=
    A.left_inv g.2
  rw [identitySpecialOrthogonalLowerChartRankGroup,
    identitySpecialOrthogonalLowerChartGroup, hchart,
    identitySpecialOrthogonalNorthPoleRecoveredMappedLowerGroup,
    identitySpecialOrthogonalMappedIdentityGroupToLiteral_rightInverse]

@[simp]
theorem identitySpecialOrthogonalNorthPoleCommonToProduct_productToCommon
    (n : ℕ) (p : identitySpecialOrthogonalNorthPoleProductDomain n) :
    identitySpecialOrthogonalNorthPoleCommonToProduct n
        (identitySpecialOrthogonalNorthPoleProductToCommon n p) = p := by
  apply Subtype.ext
  apply Prod.ext
  · exact
      identitySpecialOrthogonalNorthPoleRecoveredLowerCoordinate_product n p
  · exact congrArg Subtype.val
      (identitySpecialOrthogonalNorthPoleRecoveredCoordinate_product n p)

@[simp]
theorem identitySpecialOrthogonalNorthPoleProductToCommon_commonToProduct
    (n : ℕ) (g : identitySpecialOrthogonalNorthPoleCommonDomain n) :
    identitySpecialOrthogonalNorthPoleProductToCommon n
        (identitySpecialOrthogonalNorthPoleCommonToProduct n g) = g := by
  apply Subtype.ext
  apply Subtype.ext
  change
    identitySpecialOrthogonalNorthPoleProduct n
        (identitySpecialOrthogonalNorthPoleCommonToProduct n g) = g.1.1
  rw [identitySpecialOrthogonalNorthPoleProduct]
  change
    identitySpecialOrthogonalNorthPoleSection n
          (identitySpecialOrthogonalNorthPoleRecoveredCoordinate n g.1) *
        identitySpecialOrthogonalLastColumnFiberEmbedGroup n
          (identitySpecialOrthogonalLowerChartRankGroup n
            ⟨identitySpecialOrthogonalNorthPoleRecoveredLowerCoordinate n g.1,
              _⟩) =
      g.1.1
  rw [identitySpecialOrthogonalLowerChartRankGroup_recovered]
  exact identitySpecialOrthogonalNorthPoleSection_mul_recoveredLowerGroup n g.1

/-- The north-pole product is a homeomorphism from its exact product domain
onto the exact positive-hemisphere common source. -/
def identitySpecialOrthogonalNorthPoleProductHomeomorph
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleProductDomain n ≃ₜ
      identitySpecialOrthogonalNorthPoleCommonDomain n where
  toFun := identitySpecialOrthogonalNorthPoleProductToCommon n
  invFun := identitySpecialOrthogonalNorthPoleCommonToProduct n
  left_inv :=
    identitySpecialOrthogonalNorthPoleCommonToProduct_productToCommon n
  right_inv :=
    identitySpecialOrthogonalNorthPoleProductToCommon_commonToProduct n
  continuous_toFun :=
    continuous_identitySpecialOrthogonalNorthPoleProductToCommon n
  continuous_invFun :=
    continuous_identitySpecialOrthogonalNorthPoleCommonToProduct n

end PositiveDefiniteIntegralLattice

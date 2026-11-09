import SMSFormula.SpecialOrthogonalRealIdentityLastColumnStabilizerTopology
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# The identity last-column homogeneous space

The last-column map on `SO(n + 1)` is constant on right multiplication by
the block stabilizer. Mathlib's standard quotient `G ⧸ H` uses the
relation `g⁻¹ * k ∈ H`, so it has exactly this orientation.

This module factors the last-column map through that quotient and proves that
the induced map is a continuous bijection, packaged as an `Equiv` with the
unit sphere in rank at least two. Inverse continuity, quotient measure,
differential disintegration, volume recurrence, and compact-group volume are
not asserted.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable (n : ℕ)

/-- The right-coset homogeneous space for the identity last-column
stabilizer. Mathlib presents it using `QuotientGroup.leftRel`. -/
abbrev identitySpecialOrthogonalLastColumnHomogeneousSpace :=
  identitySpecialOrthogonalGroup n ⧸
    identitySpecialOrthogonalLastColumnStabilizerSubgroup n

/-- Right multiplication by the stabilizer does not change the last
column. -/
theorem identitySpecialOrthogonalLastColumn_mul_of_mem_stabilizer
    (g h : identitySpecialOrthogonalGroup n)
    (hh : h ∈ identitySpecialOrthogonalLastColumnStabilizerSubgroup n) :
    identitySpecialOrthogonalLastColumn n (g * h) =
      identitySpecialOrthogonalLastColumn n g := by
  have hh' :
      h ∈ identitySpecialOrthogonalLastColumnFiber n :=
    (mem_identitySpecialOrthogonalLastColumnStabilizerSubgroup_iff n h).mp hh
  have hcol :=
    (mem_identitySpecialOrthogonalLastColumnFiber_iff n h).mp hh'
  apply Subtype.ext
  rw [coe_identitySpecialOrthogonalLastColumn,
    coe_identitySpecialOrthogonalLastColumn,
    identitySpecialOrthogonalLastColumnVector_mul]
  ext i
  simp [identitySpecialOrthogonalMatrixActionVector, Matrix.mulVec,
    dotProduct, hcol, Matrix.one_apply]

/-- Two identity special-orthogonal matrices have the same last column
exactly when they represent the same right coset of the stabilizer. -/
theorem identitySpecialOrthogonalLastColumn_leftRel_iff
    (g h : identitySpecialOrthogonalGroup n) :
    QuotientGroup.leftRel
        (identitySpecialOrthogonalLastColumnStabilizerSubgroup n) g h ↔
      identitySpecialOrthogonalLastColumn n g =
        identitySpecialOrthogonalLastColumn n h := by
  rw [QuotientGroup.leftRel_apply]
  constructor
  · intro hrel
    have hh : h = g * (g⁻¹ * h) := by group
    rw [hh]
    exact
      identitySpecialOrthogonalLastColumn_mul_of_mem_stabilizer n
        g (g⁻¹ * h) hrel |>.symm
  · intro hcol
    have hvec :
        identitySpecialOrthogonalLastColumnVector n g =
          identitySpecialOrthogonalLastColumnVector n h :=
      congrArg Subtype.val hcol
    have hmoved := congrArg
      (identitySpecialOrthogonalMatrixActionVector n g⁻¹) hvec
    rw [← identitySpecialOrthogonalLastColumnVector_mul,
      ← identitySpecialOrthogonalLastColumnVector_mul] at hmoved
    have hfiber :
        identitySpecialOrthogonalLastColumn n (g⁻¹ * h) =
          identitySpecialOrthogonalNorthPole n := by
      apply Subtype.ext
      simpa [identitySpecialOrthogonalNorthPole] using hmoved.symm
    exact
      (mem_identitySpecialOrthogonalLastColumnStabilizerSubgroup_iff
        n (g⁻¹ * h)).mpr hfiber

/-- The last-column map induced on the stabilizer quotient. -/
def identitySpecialOrthogonalLastColumnQuotientMap :
    identitySpecialOrthogonalLastColumnHomogeneousSpace n →
      identitySpecialOrthogonalLastColumnSphere n :=
  Quotient.lift (identitySpecialOrthogonalLastColumn n) fun g h hrel =>
    (identitySpecialOrthogonalLastColumn_leftRel_iff n g h).mp hrel

@[simp]
theorem identitySpecialOrthogonalLastColumnQuotientMap_mk
    (g : identitySpecialOrthogonalGroup n) :
    identitySpecialOrthogonalLastColumnQuotientMap n
        (QuotientGroup.mk g) =
      identitySpecialOrthogonalLastColumn n g :=
  rfl

/-- The quotient last-column map is injective. -/
theorem injective_identitySpecialOrthogonalLastColumnQuotientMap :
    Function.Injective
      (identitySpecialOrthogonalLastColumnQuotientMap n) := by
  intro q r hqr
  induction q using Quotient.inductionOn' with
  | _ g =>
      induction r using Quotient.inductionOn' with
      | _ h =>
          apply Quotient.sound'
          exact
            (identitySpecialOrthogonalLastColumn_leftRel_iff n g h).mpr hqr

/-- In rank at least two, the quotient last-column map is surjective. -/
theorem surjective_identitySpecialOrthogonalLastColumnQuotientMap
    (hn : 0 < n) :
    Function.Surjective
      (identitySpecialOrthogonalLastColumnQuotientMap n) := by
  intro y
  obtain ⟨g, hg⟩ :=
    surjective_identitySpecialOrthogonalLastColumn n hn y
  exact ⟨QuotientGroup.mk g, hg⟩

/-- The homogeneous-space equivalence between the stabilizer
quotient and the unit sphere. -/
def identitySpecialOrthogonalLastColumnQuotientEquiv
    (hn : 0 < n) :
    identitySpecialOrthogonalLastColumnHomogeneousSpace n ≃
      identitySpecialOrthogonalLastColumnSphere n :=
  Equiv.ofBijective
    (identitySpecialOrthogonalLastColumnQuotientMap n)
    ⟨injective_identitySpecialOrthogonalLastColumnQuotientMap n,
      surjective_identitySpecialOrthogonalLastColumnQuotientMap n hn⟩

@[simp]
theorem identitySpecialOrthogonalLastColumnQuotientEquiv_mk
    (hn : 0 < n) (g : identitySpecialOrthogonalGroup n) :
    identitySpecialOrthogonalLastColumnQuotientEquiv n hn
        (QuotientGroup.mk g) =
      identitySpecialOrthogonalLastColumn n g :=
  rfl

/-- The induced quotient last-column map is continuous for the standard
quotient topology. -/
theorem continuous_identitySpecialOrthogonalLastColumnQuotientMap :
    Continuous (identitySpecialOrthogonalLastColumnQuotientMap n) := by
  exact (continuous_identitySpecialOrthogonalLastColumn n).quotient_lift _

/-- The forward map of the homogeneous-space equivalence is continuous. -/
theorem continuous_identitySpecialOrthogonalLastColumnQuotientEquiv
    (hn : 0 < n) :
    Continuous (identitySpecialOrthogonalLastColumnQuotientEquiv n hn) :=
  continuous_identitySpecialOrthogonalLastColumnQuotientMap n

end PositiveDefiniteIntegralLattice

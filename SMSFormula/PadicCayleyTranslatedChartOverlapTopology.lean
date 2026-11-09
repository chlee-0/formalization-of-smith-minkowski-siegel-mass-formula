import SMSFormula.PadicCayleyTranslatedChartTopology

/-!
# Overlap topology for translated p-adic Cayley charts

For two special-orthogonal centers, this module defines the exact intersection
of their translated Cayley targets and the corresponding open source-coordinate
overlaps.  Each source overlap is identified homeomorphically with the common
target overlap, and the resulting change of Cayley coordinates is packaged as
a homeomorphism between the two source-overlap subtypes.

All commutation and coordinate formulas are stated pointwise.
-/

noncomputable section

open scoped Matrix

namespace PositiveDefiniteIntegralLattice

open Matrix

variable {n : ℕ}

/-- The exact intersection of the translated p-adic Cayley targets centered
at `c` and `d`. -/
def padicCayleySpecialOrthogonalTranslatedTargetOverlapSet
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Set (specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :=
  padicCayleySpecialOrthogonalTranslatedTarget F p c ∩
    padicCayleySpecialOrthogonalTranslatedTarget F p d

/-- The exact common-target overlap subtype for two translated p-adic Cayley
charts. -/
abbrev padicCayleySpecialOrthogonalTranslatedTargetOverlap
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :=
  {g // g ∈
    padicCayleySpecialOrthogonalTranslatedTargetOverlapSet F p c d}

/-- Membership in the common target overlap is membership in both translated
Cayley targets. -/
theorem mem_padicCayleySpecialOrthogonalTranslatedTargetOverlapSet_iff
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (c d g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    g ∈ padicCayleySpecialOrthogonalTranslatedTargetOverlapSet F p c d ↔
      g ∈ padicCayleySpecialOrthogonalTranslatedTarget F p c ∧
      g ∈ padicCayleySpecialOrthogonalTranslatedTarget F p d :=
  Iff.rfl

/-- The exact common target overlap is open in the p-adic
special-orthogonal subgroup. -/
theorem isOpen_padicCayleySpecialOrthogonalTranslatedTargetOverlapSet
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    IsOpen
      (padicCayleySpecialOrthogonalTranslatedTargetOverlapSet F p c d) :=
  (isOpen_padicCayleySpecialOrthogonalTranslatedTarget F p c).inter
    (isOpen_padicCayleySpecialOrthogonalTranslatedTarget F p d)

/-- Swapping the two centers gives the same common target points. -/
def padicCayleySpecialOrthogonalTranslatedTargetOverlapSwapHomeomorph
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    padicCayleySpecialOrthogonalTranslatedTargetOverlap F p c d ≃ₜ
      padicCayleySpecialOrthogonalTranslatedTargetOverlap F p d c where
  toFun g := ⟨g.1, ⟨g.2.2, g.2.1⟩⟩
  invFun g := ⟨g.1, ⟨g.2.2, g.2.1⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

@[simp]
theorem coe_padicCayleySpecialOrthogonalTranslatedTargetOverlapSwapHomeomorph_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (g : padicCayleySpecialOrthogonalTranslatedTargetOverlap F p c d) :
    (padicCayleySpecialOrthogonalTranslatedTargetOverlapSwapHomeomorph
      F p c d g).1 = g.1 :=
  rfl

@[simp]
theorem coe_padicCayleySpecialOrthogonalTranslatedTargetOverlapSwapHomeomorph_symm_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (g : padicCayleySpecialOrthogonalTranslatedTargetOverlap F p d c) :
    ((padicCayleySpecialOrthogonalTranslatedTargetOverlapSwapHomeomorph
      F p c d).symm g).1 = g.1 :=
  rfl

/-- The source-coordinate overlap for the chart centered at `c`: its Cayley
image must also lie in the target centered at `d`. -/
def skewAdjointPadicCayleyTranslatedSourceOverlapSet
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Set (Matrix.skewAdjointPadicCayleySource F p) :=
  (fun X =>
      (skewAdjointPadicCayleyTranslatedHomeomorph F p hF c X).1) ⁻¹'
    padicCayleySpecialOrthogonalTranslatedTarget F p d

/-- The exact open source-coordinate overlap for the chart centered at `c`
with the chart centered at `d`. -/
abbrev skewAdjointPadicCayleyTranslatedSourceOverlap
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :=
  {X // X ∈
    skewAdjointPadicCayleyTranslatedSourceOverlapSet F p hF c d}

/-- Membership in a source-coordinate overlap is exactly target membership
after applying the centered translated Cayley chart. -/
theorem mem_skewAdjointPadicCayleyTranslatedSourceOverlapSet_iff
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : Matrix.skewAdjointPadicCayleySource F p) :
    X ∈ skewAdjointPadicCayleyTranslatedSourceOverlapSet F p hF c d ↔
      (skewAdjointPadicCayleyTranslatedHomeomorph F p hF c X).1 ∈
        padicCayleySpecialOrthogonalTranslatedTarget F p d :=
  Iff.rfl

/-- Every translated source-coordinate overlap is open in the common
skew-adjoint Cayley source. -/
theorem isOpen_skewAdjointPadicCayleyTranslatedSourceOverlapSet
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    IsOpen
      (skewAdjointPadicCayleyTranslatedSourceOverlapSet F p hF c d) :=
  (isOpen_padicCayleySpecialOrthogonalTranslatedTarget F p d).preimage
    (continuous_subtype_val.comp
      (skewAdjointPadicCayleyTranslatedHomeomorph F p hF c).continuous)

/-- The centered Cayley chart identifies its source-coordinate overlap with
the exact common target overlap. -/
def skewAdjointPadicCayleyTranslatedSourceTargetOverlapHomeomorph
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d ≃ₜ
      padicCayleySpecialOrthogonalTranslatedTargetOverlap F p c d where
  toFun X :=
    ⟨(skewAdjointPadicCayleyTranslatedHomeomorph F p hF c X.1).1,
      ⟨(skewAdjointPadicCayleyTranslatedHomeomorph F p hF c X.1).2,
        X.2⟩⟩
  invFun g :=
    ⟨(skewAdjointPadicCayleyTranslatedHomeomorph F p hF c).symm
        ⟨g.1, g.2.1⟩,
      by
        change
          (skewAdjointPadicCayleyTranslatedHomeomorph F p hF c
            ((skewAdjointPadicCayleyTranslatedHomeomorph
              F p hF c).symm ⟨g.1, g.2.1⟩)).1 ∈
            padicCayleySpecialOrthogonalTranslatedTarget F p d
        simpa using g.2.2⟩
  left_inv X := by
    apply Subtype.ext
    exact
      (skewAdjointPadicCayleyTranslatedHomeomorph
        F p hF c).symm_apply_apply X.1
  right_inv g := by
    apply Subtype.ext
    change
      (skewAdjointPadicCayleyTranslatedHomeomorph F p hF c
        ((skewAdjointPadicCayleyTranslatedHomeomorph
          F p hF c).symm ⟨g.1, g.2.1⟩)).1 = g.1
    exact congrArg Subtype.val
      ((skewAdjointPadicCayleyTranslatedHomeomorph
        F p hF c).apply_symm_apply ⟨g.1, g.2.1⟩)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp
      ((skewAdjointPadicCayleyTranslatedHomeomorph
        F p hF c).continuous.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact
      (skewAdjointPadicCayleyTranslatedHomeomorph
        F p hF c).symm.continuous.comp
          (continuous_subtype_val.subtype_mk (fun g => g.2.1))

@[simp]
theorem coe_skewAdjointPadicCayleyTranslatedSourceTargetOverlapHomeomorph_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    (skewAdjointPadicCayleyTranslatedSourceTargetOverlapHomeomorph
      F p hF c d X).1 =
      (skewAdjointPadicCayleyTranslatedHomeomorph F p hF c X.1).1 :=
  rfl

@[simp]
theorem coe_skewAdjointPadicCayleyTranslatedSourceTargetOverlapHomeomorph_symm_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (g : padicCayleySpecialOrthogonalTranslatedTargetOverlap F p c d) :
    ((skewAdjointPadicCayleyTranslatedSourceTargetOverlapHomeomorph
      F p hF c d).symm g).1 =
      (skewAdjointPadicCayleyTranslatedHomeomorph F p hF c).symm
        ⟨g.1, g.2.1⟩ :=
  rfl

/-- The exact change of source coordinates from the chart centered at `c` to
the chart centered at `d` on their common target overlap. -/
def skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d ≃ₜ
      skewAdjointPadicCayleyTranslatedSourceOverlap F p hF d c :=
  (skewAdjointPadicCayleyTranslatedSourceTargetOverlapHomeomorph
      F p hF c d).trans
    ((padicCayleySpecialOrthogonalTranslatedTargetOverlapSwapHomeomorph
      F p c d).trans
      (skewAdjointPadicCayleyTranslatedSourceTargetOverlapHomeomorph
        F p hF d c).symm)

/-- Pointwise, the forward coordinate transition applies inverse Cayley
coordinates for `d` to the target point produced by the chart at `c`. -/
@[simp]
theorem coe_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
      F p hF c d X).1 =
      (skewAdjointPadicCayleyTranslatedHomeomorph F p hF d).symm
        ⟨(skewAdjointPadicCayleyTranslatedHomeomorph
          F p hF c X.1).1, X.2⟩ :=
  rfl

/-- Pointwise, the inverse coordinate transition applies inverse Cayley
coordinates for `c` to the target point produced by the chart at `d`. -/
@[simp]
theorem coe_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph_symm_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF d c) :
    ((skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
      F p hF c d).symm X).1 =
      (skewAdjointPadicCayleyTranslatedHomeomorph F p hF c).symm
        ⟨(skewAdjointPadicCayleyTranslatedHomeomorph
          F p hF d X.1).1, X.2⟩ :=
  rfl

/-- The forward transition preserves the represented target point,
pointwise. -/
theorem skewAdjointPadicCayleyTranslatedSourceOverlapTransition_target
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    (skewAdjointPadicCayleyTranslatedHomeomorph F p hF d
      (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
        F p hF c d X).1).1 =
      (skewAdjointPadicCayleyTranslatedHomeomorph F p hF c X.1).1 := by
  exact congrArg Subtype.val
    ((skewAdjointPadicCayleyTranslatedHomeomorph
      F p hF d).apply_symm_apply
        ⟨(skewAdjointPadicCayleyTranslatedHomeomorph
          F p hF c X.1).1, X.2⟩)

/-- The inverse transition preserves the represented target point,
pointwise. -/
theorem skewAdjointPadicCayleyTranslatedSourceOverlapTransition_symm_target
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF d c) :
    (skewAdjointPadicCayleyTranslatedHomeomorph F p hF c
      ((skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
        F p hF c d).symm X).1).1 =
      (skewAdjointPadicCayleyTranslatedHomeomorph F p hF d X.1).1 := by
  exact congrArg Subtype.val
    ((skewAdjointPadicCayleyTranslatedHomeomorph
      F p hF c).apply_symm_apply
        ⟨(skewAdjointPadicCayleyTranslatedHomeomorph
          F p hF d X.1).1, X.2⟩)

/-- The forward source-coordinate transition has the explicit ambient
inverse-Cayley matrix formula centered at `d`. -/
theorem coe_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph_apply_matrix
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    ((skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
        F p hF c d X).1.1 :
        Matrix (Fin n) (Fin n) ℚ_[p]) =
      ((((d⁻¹ *
          (skewAdjointPadicCayleyTranslatedHomeomorph
            F p hF c X.1).1).1.1.1 :
            Matrix (Fin n) (Fin n) ℚ_[p]) + 1)⁻¹ *
        (((d⁻¹ *
          (skewAdjointPadicCayleyTranslatedHomeomorph
            F p hF c X.1).1).1.1.1 :
            Matrix (Fin n) (Fin n) ℚ_[p]) - 1)) := by
  change
    (((skewAdjointPadicCayleyTranslatedHomeomorph
      F p hF d).symm
        ⟨(skewAdjointPadicCayleyTranslatedHomeomorph
          F p hF c X.1).1, X.2⟩).1 :
          Matrix (Fin n) (Fin n) ℚ_[p]) = _
  exact
    coe_skewAdjointPadicCayleyTranslatedHomeomorph_symm_apply
      F p hF d
        ⟨(skewAdjointPadicCayleyTranslatedHomeomorph
          F p hF c X.1).1, X.2⟩

/-- The inverse source-coordinate transition has the explicit ambient
inverse-Cayley matrix formula centered at `c`. -/
theorem coe_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph_symm_apply_matrix
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF d c) :
    (((skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
        F p hF c d).symm X).1.1 :
        Matrix (Fin n) (Fin n) ℚ_[p]) =
      ((((c⁻¹ *
          (skewAdjointPadicCayleyTranslatedHomeomorph
            F p hF d X.1).1).1.1.1 :
            Matrix (Fin n) (Fin n) ℚ_[p]) + 1)⁻¹ *
        (((c⁻¹ *
          (skewAdjointPadicCayleyTranslatedHomeomorph
            F p hF d X.1).1).1.1.1 :
            Matrix (Fin n) (Fin n) ℚ_[p]) - 1)) := by
  change
    (((skewAdjointPadicCayleyTranslatedHomeomorph
      F p hF c).symm
        ⟨(skewAdjointPadicCayleyTranslatedHomeomorph
          F p hF d X.1).1, X.2⟩).1 :
          Matrix (Fin n) (Fin n) ℚ_[p]) = _
  exact
    coe_skewAdjointPadicCayleyTranslatedHomeomorph_symm_apply
      F p hF c
        ⟨(skewAdjointPadicCayleyTranslatedHomeomorph
          F p hF d X.1).1, X.2⟩

end PositiveDefiniteIntegralLattice

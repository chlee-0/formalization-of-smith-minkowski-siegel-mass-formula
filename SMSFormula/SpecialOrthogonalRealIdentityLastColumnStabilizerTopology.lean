import SMSFormula.SpecialOrthogonalRealIdentityLastColumnStabilizer

/-!
# Topology of the identity last-column stabilizer

The block embedding and upper-left extraction from the algebraic stabilizer
module are continuous in the inherited finite-matrix topologies. Consequently
the algebraic fiber equivalence is a homeomorphism, and the
lower-rank group is continuously multiplicatively equivalent to the
stabilizer subgroup.
-/

open scoped Matrix

noncomputable section

open Matrix

namespace PositiveDefiniteIntegralLattice

variable (n : ℕ)

theorem continuous_identitySpecialOrthogonalUpperLeftBlock :
    Continuous
      (identitySpecialOrthogonalUpperLeftBlock n :
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ →
          Matrix (Fin n) (Fin n) ℝ) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (continuous_apply j.castSucc).comp
    (continuous_apply i.castSucc)

theorem continuous_identitySpecialOrthogonalLastBlockMatrix :
    Continuous
      (identitySpecialOrthogonalLastBlockMatrix n :
        Matrix (Fin n) (Fin n) ℝ →
          Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  cases i using Fin.lastCases with
  | last =>
      cases j using Fin.lastCases with
      | last => simpa using continuous_const
      | cast j => simpa using continuous_const
  | cast i =>
      cases j using Fin.lastCases with
      | last => simpa using continuous_const
      | cast j =>
          simpa using
            ((continuous_apply j).comp (continuous_apply i))

theorem continuous_identitySpecialOrthogonalLastColumnFiberEmbedGroup :
    Continuous
      (identitySpecialOrthogonalLastColumnFiberEmbedGroup n) := by
  have hsource :
      Continuous
        (fun h : identitySpecialOrthogonalRankGroup n => h.1.1.1) :=
    Units.continuous_val.comp
      (continuous_subtype_val.comp continuous_subtype_val)
  have hmatrix :
      Continuous
        (fun h : identitySpecialOrthogonalRankGroup n =>
          identitySpecialOrthogonalLastBlockMatrix n h.1.1.1) :=
    (continuous_identitySpecialOrthogonalLastBlockMatrix n).comp hsource
  have hsl :
      Continuous
        (fun h : identitySpecialOrthogonalRankGroup n =>
          (⟨identitySpecialOrthogonalLastBlockMatrix n h.1.1.1,
            by
              rw [identitySpecialOrthogonalLastBlockMatrix_det]
              exact
                (mem_specialFormPreservingMatrixSubgroup_iff _ h.1).mp h.2⟩ :
            Matrix.SpecialLinearGroup (Fin (n + 1)) ℝ)) :=
    hmatrix.subtype_mk _
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact Matrix.SpecialLinearGroup.continuous_toGL.comp hsl

theorem continuous_identitySpecialOrthogonalLastColumnFiberEmbed :
    Continuous
      (identitySpecialOrthogonalLastColumnFiberEmbed n) :=
  (continuous_identitySpecialOrthogonalLastColumnFiberEmbedGroup n).subtype_mk _

theorem continuous_identitySpecialOrthogonalLastColumnFiberExtract :
    Continuous
      (identitySpecialOrthogonalLastColumnFiberExtract n) := by
  have hsource :
      Continuous
        (fun g : {g : identitySpecialOrthogonalGroup n //
            g ∈ identitySpecialOrthogonalLastColumnFiber n} =>
          g.1.1.1.1) :=
    Units.continuous_val.comp
      (continuous_subtype_val.comp
        (continuous_subtype_val.comp continuous_subtype_val))
  have hmatrix :
      Continuous
        (fun g : {g : identitySpecialOrthogonalGroup n //
            g ∈ identitySpecialOrthogonalLastColumnFiber n} =>
          identitySpecialOrthogonalUpperLeftBlock n g.1.1.1.1) :=
    (continuous_identitySpecialOrthogonalUpperLeftBlock n).comp hsource
  have hsl :
      Continuous
        (fun g : {g : identitySpecialOrthogonalGroup n //
            g ∈ identitySpecialOrthogonalLastColumnFiber n} =>
          (⟨identitySpecialOrthogonalUpperLeftBlock n g.1.1.1.1,
            identitySpecialOrthogonalUpperLeftBlock_det n g.1 g.2⟩ :
            Matrix.SpecialLinearGroup (Fin n) ℝ)) :=
    hmatrix.subtype_mk _
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact Matrix.SpecialLinearGroup.continuous_toGL.comp hsl

def identitySpecialOrthogonalLastColumnFiberHomeomorph :
    identitySpecialOrthogonalRankGroup n ≃ₜ
      {g : identitySpecialOrthogonalGroup n //
        g ∈ identitySpecialOrthogonalLastColumnFiber n} where
  toEquiv := identitySpecialOrthogonalLastColumnFiberEquiv n
  continuous_toFun :=
    continuous_identitySpecialOrthogonalLastColumnFiberEmbed n
  continuous_invFun :=
    continuous_identitySpecialOrthogonalLastColumnFiberExtract n

def identitySpecialOrthogonalFiberHomeomorphStabilizer :
    {g : identitySpecialOrthogonalGroup n //
        g ∈ identitySpecialOrthogonalLastColumnFiber n} ≃ₜ
      identitySpecialOrthogonalLastColumnStabilizerSubgroup n where
  toFun g := ⟨g.1,
    (mem_identitySpecialOrthogonalLastColumnStabilizerSubgroup_iff n g.1).mpr g.2⟩
  invFun g := ⟨g.1,
    (mem_identitySpecialOrthogonalLastColumnStabilizerSubgroup_iff n g.1).mp g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def identitySpecialOrthogonalLastColumnStabilizerHomeomorph :
    identitySpecialOrthogonalRankGroup n ≃ₜ
      identitySpecialOrthogonalLastColumnStabilizerSubgroup n :=
  (identitySpecialOrthogonalLastColumnFiberHomeomorph n).trans
    (identitySpecialOrthogonalFiberHomeomorphStabilizer n)

def identitySpecialOrthogonalLastColumnStabilizerContinuousMulEquiv :
    identitySpecialOrthogonalRankGroup n ≃ₜ*
      identitySpecialOrthogonalLastColumnStabilizerSubgroup n :=
  ContinuousMulEquiv.mk'
    (identitySpecialOrthogonalLastColumnStabilizerHomeomorph n) (by
      intro g h
      apply Subtype.ext
      exact (identitySpecialOrthogonalLastColumnFiberEmbedHom n).map_mul g h)

@[simp]
theorem coe_identitySpecialOrthogonalLastColumnStabilizerContinuousMulEquiv_apply
    (g : identitySpecialOrthogonalRankGroup n) :
    (identitySpecialOrthogonalLastColumnStabilizerContinuousMulEquiv n g).1 =
      identitySpecialOrthogonalLastColumnFiberEmbedGroup n g :=
  rfl

theorem identitySpecialOrthogonalLastColumnStabilizerContinuousMulEquiv_toMulEquiv :
    (identitySpecialOrthogonalLastColumnStabilizerContinuousMulEquiv n).toMulEquiv =
      identitySpecialOrthogonalLastColumnStabilizerMulEquiv n := by
  ext g
  rfl

end PositiveDefiniteIntegralLattice

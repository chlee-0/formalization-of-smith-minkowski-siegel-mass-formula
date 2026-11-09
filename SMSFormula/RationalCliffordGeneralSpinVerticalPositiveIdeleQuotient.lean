import SMSFormula.RationalCliffordGeneralSpinVerticalRationalDiagonalReindexing
import SMSFormula.RationalCliffordGeneralSpinLatticeAdelicSimilitudeExactness

/-!
# Positive-idèle quotient for the vertical GSpin disintegration

For a positive-definite lattice of rank at least three, rational `GSpin`
similitudes are exactly the positive rational units and full adelic `GSpin`
similitudes are exactly the idèles positive at the real place.  This file
identifies the corresponding rational diagonal quotient and proves that the
positive-idèle quotient by the positive rational diagonal is the ordinary
rational idèle-class group.

Thus the coset coordinate in the rational-diagonal reindexing is matched with
the rational subgroup acting on the retained positive idèle branch.  No
positive representative of an idèle class is selected, no measure is
transported, and no Weil or normalization coefficient is asserted.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1800000

/-- The positive rational diagonal inside the idèles positive at the real
place. -/
def positiveRationalUnitFullAdelicDiagonalHom :
    positiveRationalUnitsSubgroup →* positiveRationalAdeleUnitsSubgroup where
  toFun q :=
    ⟨rationalUnitFullAdelicDiagonalHom q,
      (rationalUnitFullAdelicDiagonal_mem_positive_iff q).2 q.2⟩
  map_one' := by
    apply Subtype.ext
    exact rationalUnitFullAdelicDiagonalHom.map_one
  map_mul' q r := by
    apply Subtype.ext
    exact rationalUnitFullAdelicDiagonalHom.map_mul q r

/-- The literal positive rational diagonal subgroup. -/
def positiveRationalIdeleDiagonalSubgroup :
    Subgroup positiveRationalAdeleUnitsSubgroup :=
  positiveRationalUnitFullAdelicDiagonalHom.range

theorem positiveRationalUnitFullAdelicDiagonalHom_injective :
    Function.Injective positiveRationalUnitFullAdelicDiagonalHom := by
  intro q r hqr
  apply Subtype.ext
  apply Units.ext
  apply NumberField.AdeleRing.algebraMap_injective ℤ ℚ
  exact congrArg (fun a : positiveRationalAdeleUnitsSubgroup =>
    (((a : RationalAdeleˣ) : RationalAdele))) hqr

/-- Positive rational units are equivalent to their literal diagonal inside
the positive idèles. -/
def positiveRationalUnitsEquivPositiveRationalIdeleDiagonal :
    positiveRationalUnitsSubgroup ≃*
      positiveRationalIdeleDiagonalSubgroup :=
  MulEquiv.ofBijective
    (positiveRationalUnitFullAdelicDiagonalHom.codRestrict
      positiveRationalIdeleDiagonalSubgroup (fun q => ⟨q, rfl⟩))
    ⟨fun q r h => positiveRationalUnitFullAdelicDiagonalHom_injective
        (congrArg Subtype.val h), by
      intro a
      rcases a.2 with ⟨q, hq⟩
      exact ⟨q, Subtype.ext hq⟩⟩

/-- Inclusion of positive idèles followed by the ordinary rational
idèle-class quotient. -/
def positiveRationalIdeleToIdeleClassHom :
    positiveRationalAdeleUnitsSubgroup →* RationalIdeleClassGroup :=
  (QuotientGroup.mk' rationalIdeleDiagonalSubgroup).comp
    positiveRationalAdeleUnitsSubgroup.subtype

@[simp]
theorem positiveRationalIdeleToIdeleClassHom_apply
    (a : positiveRationalAdeleUnitsSubgroup) :
    positiveRationalIdeleToIdeleClassHom a =
      QuotientGroup.mk' rationalIdeleDiagonalSubgroup (a : RationalAdeleˣ) :=
  rfl

/-- Every rational idèle class has a representative positive at the real
place. -/
theorem positiveRationalIdeleToIdeleClassHom_surjective :
    Function.Surjective positiveRationalIdeleToIdeleClassHom := by
  intro c
  let a : RationalAdeleˣ := Quotient.out c
  have ha : QuotientGroup.mk' rationalIdeleDiagonalSubgroup a = c :=
    Quotient.out_eq c
  obtain ⟨q, b, hb, hab⟩ :=
    exists_rationalUnit_mul_positiveRationalAdeleUnit a
  refine ⟨⟨b, hb⟩, ?_⟩
  change QuotientGroup.mk' rationalIdeleDiagonalSubgroup b = c
  rw [← ha, hab, map_mul]
  rw [show QuotientGroup.mk' rationalIdeleDiagonalSubgroup
      (rationalUnitFullAdelicDiagonalHom q) = 1 by
    exact (QuotientGroup.eq_one_iff _).2 ⟨q, rfl⟩]
  exact (@one_mul RationalIdeleClassGroup _ _).symm

/-- Exactness of the positive rational diagonal inside positive idèles. -/
theorem range_positiveRationalUnitFullAdelicDiagonalHom_eq_ker :
    positiveRationalIdeleDiagonalSubgroup =
      positiveRationalIdeleToIdeleClassHom.ker := by
  ext a
  constructor
  · rintro ⟨q, rfl⟩
    change QuotientGroup.mk' rationalIdeleDiagonalSubgroup
        (rationalUnitFullAdelicDiagonalHom q) = 1
    exact (QuotientGroup.eq_one_iff _).2 ⟨q, rfl⟩
  · intro ha
    change QuotientGroup.mk' rationalIdeleDiagonalSubgroup
        (a : RationalAdeleˣ) = 1 at ha
    have hdiag : (a : RationalAdeleˣ) ∈ rationalIdeleDiagonalSubgroup :=
      (QuotientGroup.eq_one_iff _).1 ha
    rcases hdiag with ⟨q, hq⟩
    have hqpos : q ∈ positiveRationalUnitsSubgroup :=
      (rationalUnitFullAdelicDiagonal_mem_positive_iff q).1 (by
        rw [hq]
        exact a.2)
    refine ⟨⟨q, hqpos⟩, ?_⟩
    apply Subtype.ext
    exact hq

/-- The range of the positive-idèle class map is the whole idèle-class
group. -/
def positiveRationalIdeleClassRangeEquiv :
    positiveRationalIdeleToIdeleClassHom.range ≃* RationalIdeleClassGroup :=
  MulEquiv.ofBijective positiveRationalIdeleToIdeleClassHom.range.subtype
    ⟨fun x y h => Subtype.ext h, by
      intro c
      obtain ⟨a, ha⟩ := positiveRationalIdeleToIdeleClassHom_surjective c
      exact ⟨⟨c, ⟨a, ha⟩⟩, rfl⟩⟩

/-- The quotient of positive idèles by the positive rational diagonal is the
ordinary rational idèle-class group. -/
def positiveRationalIdeleQuotientEquivIdeleClass :
    positiveRationalAdeleUnitsSubgroup ⧸
        positiveRationalIdeleDiagonalSubgroup ≃*
      RationalIdeleClassGroup :=
  (QuotientGroup.quotientMulEquivOfEq
      range_positiveRationalUnitFullAdelicDiagonalHom_eq_ker).trans
    ((QuotientGroup.quotientKerEquivRange
      positiveRationalIdeleToIdeleClassHom).trans
        positiveRationalIdeleClassRangeEquiv)

@[simp]
theorem positiveRationalIdeleQuotientEquivIdeleClass_mk
    (a : positiveRationalAdeleUnitsSubgroup) :
    positiveRationalIdeleQuotientEquivIdeleClass
        (QuotientGroup.mk' positiveRationalIdeleDiagonalSubgroup a) =
      positiveRationalIdeleToIdeleClassHom a :=
  rfl

variable {n : ℕ}

/-- On the rational diagonal of a rank-at-least-three positive-definite
lattice `GSpin`, the transported similitude range is exactly the positive
rational units. -/
theorem range_rationalCliffordGeneralSpinDiagonalSimilitudeHom_eq_positive
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n) :
    L.rationalQuadraticSpaceMatrix.rationalCliffordGeneralSpinDiagonalSimilitudeHom.range =
      positiveRationalUnitsSubgroup := by
  let V := L.rationalQuadraticSpaceMatrix
  ext q
  constructor
  · rintro ⟨gamma, hgamma⟩
    have hmem : q ∈
        (CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom V ℚ).range := by
      refine ⟨V.rationalCliffordGeneralSpinGroupEquivDiagonal.symm gamma, ?_⟩
      exact hgamma
    rw [CliffordGeneralSpinIntrinsicPoint.range_rationalCliffordGeneralSpinSimilitudeHom_eq_positive
      L hn] at hmem
    exact hmem
  · intro hq
    have hmem : q ∈
        (CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom V ℚ).range := by
      rw [CliffordGeneralSpinIntrinsicPoint.range_rationalCliffordGeneralSpinSimilitudeHom_eq_positive
        L hn]
      exact hq
    rcases hmem with ⟨g, hg⟩
    refine ⟨V.rationalCliffordGeneralSpinGroupEquivDiagonal g, ?_⟩
    change CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom V ℚ
      (V.rationalCliffordGeneralSpinGroupEquivDiagonal.symm
        (V.rationalCliffordGeneralSpinGroupEquivDiagonal g)) = q
    rw [MulEquiv.symm_apply_apply]
    exact hg

local instance verticalPositiveIdeleDiagonalImageNormal
    (L : PositiveDefiniteIntegralLattice n) :
    (L.rationalQuadraticSpaceMatrix.rationalCliffordSpinCandidateDiagonalImageInGeneralSpin).Normal := by
  rw [L.rationalQuadraticSpaceMatrix.range_rationalCliffordSpinCandidateDiagonalToGeneralSpin_eq_ker]
  infer_instance

/-- For a rank-at-least-three positive-definite lattice, the rational
`GSpin`-diagonal quotient by Spin is literally the positive rational
similitude group. -/
def rationalGeneralSpinDiagonalQuotientEquivPositiveRationalUnits
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n) :
    L.rationalQuadraticSpaceMatrix.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup ⧸
        L.rationalQuadraticSpaceMatrix.rationalCliffordSpinCandidateDiagonalImageInGeneralSpin ≃*
      positiveRationalUnitsSubgroup :=
  L.rationalQuadraticSpaceMatrix.rationalGeneralSpinDiagonalQuotientEquivSimilitudeRange.trans
    (MulEquiv.subgroupCongr
      (range_rationalCliffordGeneralSpinDiagonalSimilitudeHom_eq_positive L hn))

/-- The rational `GSpin`-by-Spin coset coordinate is exactly the positive
rational diagonal acting on the positive idèle branch. -/
def rationalGeneralSpinDiagonalQuotientEquivPositiveRationalIdeleDiagonal
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n) :
    L.rationalQuadraticSpaceMatrix.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup ⧸
        L.rationalQuadraticSpaceMatrix.rationalCliffordSpinCandidateDiagonalImageInGeneralSpin ≃*
      positiveRationalIdeleDiagonalSubgroup :=
  (rationalGeneralSpinDiagonalQuotientEquivPositiveRationalUnits L hn).trans
    positiveRationalUnitsEquivPositiveRationalIdeleDiagonal

/-- Reindex the rational `GSpin` diagonal first by the literal positive
rational idèle diagonal and then by the rational Spin diagonal. -/
theorem tsum_rationalCliffordGeneralSpinDiagonal_eq_positiveIdele_spin
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (F : L.rationalQuadraticSpaceMatrix.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup →
      ℝ≥0∞) :
    let V := L.rationalQuadraticSpaceMatrix
    (∑' gamma, F gamma) =
      ∑' eta : positiveRationalIdeleDiagonalSubgroup,
        ∑' sigma : V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup,
          F ((Subgroup.groupEquivQuotientProdSubgroup
                (s := V.rationalCliffordSpinCandidateDiagonalImageInGeneralSpin)).symm
              ((rationalGeneralSpinDiagonalQuotientEquivPositiveRationalIdeleDiagonal
                  L hn).symm eta,
                V.rationalCliffordSpinCandidateDiagonalEquivImageInGeneralSpin sigma)) := by
  let V := L.rationalQuadraticSpaceMatrix
  let e := rationalGeneralSpinDiagonalQuotientEquivPositiveRationalIdeleDiagonal L hn
  let G := fun xi :
      V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup ⧸
        V.rationalCliffordSpinCandidateDiagonalImageInGeneralSpin =>
    ∑' sigma : V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup,
      F ((Subgroup.groupEquivQuotientProdSubgroup
            (s := V.rationalCliffordSpinCandidateDiagonalImageInGeneralSpin)).symm
          (xi, V.rationalCliffordSpinCandidateDiagonalEquivImageInGeneralSpin sigma))
  dsimp only [V]
  calc
    (∑' gamma, F gamma) = ∑' xi, G xi :=
      V.tsum_rationalCliffordGeneralSpinDiagonal_eq_coset_spin F
    _ = ∑' eta, G (e.symm eta) := (e.symm.tsum_eq G).symm
    _ = _ := rfl

/-- Ambient-function form of the positive-idèle/Spin rational-diagonal
reindexing. -/
theorem leftPreperiodize_rationalCliffordGeneralSpinDiagonal_eq_positiveIdele_spin
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (f : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup → ℝ≥0∞)
    (x : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) :
    let V := L.rationalQuadraticSpaceMatrix
    leftPreperiodize
        V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup f x =
      ∑' eta : positiveRationalIdeleDiagonalSubgroup,
        ∑' sigma : V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup,
          f (((Subgroup.groupEquivQuotientProdSubgroup
                  (s := V.rationalCliffordSpinCandidateDiagonalImageInGeneralSpin)).symm
                ((rationalGeneralSpinDiagonalQuotientEquivPositiveRationalIdeleDiagonal
                    L hn).symm eta,
                  V.rationalCliffordSpinCandidateDiagonalEquivImageInGeneralSpin sigma) :
              V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) * x) := by
  exact tsum_rationalCliffordGeneralSpinDiagonal_eq_positiveIdele_spin L hn
    (fun gamma => f ((gamma :
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) * x))

end RationalQuadraticSpaceMatrix

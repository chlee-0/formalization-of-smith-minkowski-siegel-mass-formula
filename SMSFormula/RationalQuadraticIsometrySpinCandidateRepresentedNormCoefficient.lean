import SMSFormula.RationalQuadraticIsometrySpinCandidateCrossWitnessCoefficient
import SMSFormula.RationalCliffordGeneralSpinAllRationalShellTonelli
import SMSFormula.RationalCliffordSpinCandidateOnoRelativeTamagawaData

/-!
# Section-free represented-norm Spin coefficients

A represented nonzero rational norm does not itself contain the lattice-backed
complement presentation required by the exact one-shell theorem.  This file
states that existence input as a proposition: every norm may be
supplied with a merely nonempty type of local complement-lattice witnesses.
The certified raw datum is then produced by the rank-at-
least-three construction, and cross-witness covariance proves that all such
witnesses realize one unique coefficient.

Only that unique scalar is selected.  No witness, complement lattice, rational
vector, raw datum, or global presentation family is selected.  The resulting
coefficient function gives the exact nonnegative weighted Tonelli expansion
over the section-free represented-norm index.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- Every rank-at-least-three integral lattice carries certified raw Spin data
by the completed inverse-volume-product construction. -/
theorem nonempty_cliffordSpinCandidateRawOnoTamagawaData_of_rankAtLeastThree
    {m : ℕ} (L : PositiveDefiniteIntegralLattice m) (hm : 3 ≤ m) :
    Nonempty
      (L.rationalQuadraticSpaceMatrix
        |>.CliffordSpinCandidateRawOnoTamagawaData) := by
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 3 := ⟨m - 3, by omega⟩
  letI : Nonempty (Fin (r + 3)) :=
    Fin.pos_iff_nonempty.mp (by omega)
  exact nonempty_cliffordSpinCandidateRawOnoTamagawaData
    L inferInstance

namespace RepresentedNonzeroRationalNorm

/-- The precise remaining local existence datum at one represented nonzero
norm: an integral lattice of rank at least three whose rational quadratic space
is isometric to the orthogonal complement of a vector in the literal fiber.
No raw Spin datum is included, since it exists on every such
lattice. -/
structure OneShellComplementLatticeWitness
    (V : RationalQuadraticSpaceMatrix n)
    (a : V.RepresentedNonzeroRationalNorm) where
  lowerRank : ℕ
  lowerLattice : PositiveDefiniteIntegralLattice lowerRank
  lowerRank_atLeastThree : 3 ≤ lowerRank
  vector : a.rationalVectorFiber V
  complementIsometry :
    lowerLattice.rationalQuadraticSpaceMatrix.quadraticForm.IsometryEquiv
      (V.nativeRationalQuadraticForm.orthogonalRestriction vector.1)

/-- Local lattice-backed data realizing the one-shell Spin coefficient at one
represented nonzero norm.  Its raw datum is certified data rather than a new
source assumption. -/
structure OneShellSpinCoefficientWitness
    (V : RationalQuadraticSpaceMatrix n)
    (a : V.RepresentedNonzeroRationalNorm) where
  lowerRank : ℕ
  lowerLattice : PositiveDefiniteIntegralLattice lowerRank
  lowerRank_atLeastThree : 3 ≤ lowerRank
  vector : a.rationalVectorFiber V
  complementIsometry :
    lowerLattice.rationalQuadraticSpaceMatrix.quadraticForm.IsometryEquiv
      (V.nativeRationalQuadraticForm.orthogonalRestriction vector.1)
  lowerRawData :
    lowerLattice.rationalQuadraticSpaceMatrix
      |>.CliffordSpinCandidateRawOnoTamagawaData

namespace OneShellComplementLatticeWitness

variable {V : RationalQuadraticSpaceMatrix n}
variable {a : V.RepresentedNonzeroRationalNorm}

/-- Add an explicitly supplied certified raw datum to a complement-lattice
witness. -/
def withRawData
    (w : a.OneShellComplementLatticeWitness V)
    (D : w.lowerLattice.rationalQuadraticSpaceMatrix
      |>.CliffordSpinCandidateRawOnoTamagawaData) :
    a.OneShellSpinCoefficientWitness V where
  lowerRank := w.lowerRank
  lowerLattice := w.lowerLattice
  lowerRank_atLeastThree := w.lowerRank_atLeastThree
  vector := w.vector
  complementIsometry := w.complementIsometry
  lowerRawData := D

end OneShellComplementLatticeWitness

namespace OneShellSpinCoefficientWitness

variable {V : RationalQuadraticSpaceMatrix n}
variable {a : V.RepresentedNonzeroRationalNorm}

/-- Forget the raw datum, retaining exactly the complement-lattice existence
content of a coefficient witness. -/
def toComplementLatticeWitness (w : a.OneShellSpinCoefficientWitness V) :
    a.OneShellComplementLatticeWitness V where
  lowerRank := w.lowerRank
  lowerLattice := w.lowerLattice
  lowerRank_atLeastThree := w.lowerRank_atLeastThree
  vector := w.vector
  complementIsometry := w.complementIsometry

/-- The supplied complement presentation underlying a local witness. -/
def presentation (w : a.OneShellSpinCoefficientWitness V) :
    V.AnisotropicComplementPresentation w.vector.1 w.lowerRank :=
  integralLatticeAnisotropicComplementPresentation
    w.lowerLattice V w.vector.1 w.complementIsometry

/-- The normalized coefficient realized by one local witness. -/
def coefficient
    (w : a.OneShellSpinCoefficientWitness V)
    (DAmbient : V.CliffordSpinCandidateRawOnoTamagawaData) : ℝ≥0∞ :=
  w.presentation.oneShellSpinTamagawaCoefficient
    w.lowerRawData DAmbient

/-- The rational vector carried by a local witness is anisotropic. -/
theorem vector_anisotropic (w : a.OneShellSpinCoefficientWitness V) :
    V.nativeRationalQuadraticForm w.vector.1 ≠ 0 := by
  rw [w.vector.property]
  exact a.property.1

/-- Any two local witnesses for one represented norm realize the same
normalized coefficient, even when their lower coordinate types differ. -/
theorem coefficient_eq
    (w : a.OneShellSpinCoefficientWitness V)
    (u : a.OneShellSpinCoefficientWitness V)
    (DAmbient : V.CliffordSpinCandidateRawOnoTamagawaData) :
    w.coefficient DAmbient = u.coefficient DAmbient := by
  exact integralLattice_oneShellSpinTamagawaCoefficient_eq_of_equalNorm
    w.lowerLattice u.lowerLattice V w.vector.1 u.vector.1
      (by
        have h := w.lowerRank_atLeastThree
        omega) w.vector_anisotropic
      (u.vector.property.trans w.vector.property.symm)
      w.complementIsometry u.complementIsometry
      w.lowerRawData u.lowerRawData DAmbient

end OneShellSpinCoefficientWitness

/-- Every rank-at-least-three integral lattice carries certified raw Spin data
by the completed inverse-volume-product construction. -/
theorem nonempty_rawOnoData_of_complementLatticeWitness
    {V : RationalQuadraticSpaceMatrix n}
    {a : V.RepresentedNonzeroRationalNorm}
    (w : a.OneShellComplementLatticeWitness V) :
    Nonempty
      (w.lowerLattice.rationalQuadraticSpaceMatrix
        |>.CliffordSpinCandidateRawOnoTamagawaData) :=
  nonempty_cliffordSpinCandidateRawOnoTamagawaData_of_rankAtLeastThree
    w.lowerLattice w.lowerRank_atLeastThree

/-- Adding certified raw data does not strengthen the local existence seam:
coefficient witnesses are merely inhabited exactly when complement-lattice
witnesses are.  Both eliminations remain in `Prop`. -/
theorem nonempty_oneShellSpinCoefficientWitness_iff
    {V : RationalQuadraticSpaceMatrix n}
    (a : V.RepresentedNonzeroRationalNorm) :
    Nonempty (a.OneShellSpinCoefficientWitness V) ↔
      Nonempty (a.OneShellComplementLatticeWitness V) := by
  constructor
  · rintro ⟨w⟩
    exact ⟨w.toComplementLatticeWitness⟩
  · rintro ⟨w⟩
    exact nonempty_rawOnoData_of_complementLatticeWitness w |>.elim fun D ↦
      ⟨w.withRawData D⟩

/-- A scalar is the one-shell Spin coefficient of `a` when some local witness
realizes it.  This is a proposition and exposes no witness choice. -/
def IsOneShellSpinTamagawaCoefficient
    {V : RationalQuadraticSpaceMatrix n}
    (a : V.RepresentedNonzeroRationalNorm)
    (DAmbient : V.CliffordSpinCandidateRawOnoTamagawaData)
    (c : ℝ≥0∞) : Prop :=
  ∃ w : a.OneShellSpinCoefficientWitness V,
    c = w.coefficient DAmbient

/-- The local coefficient relation is subsingleton by cross-witness
covariance. -/
theorem isOneShellSpinTamagawaCoefficient_eq
    {V : RationalQuadraticSpaceMatrix n}
    (a : V.RepresentedNonzeroRationalNorm)
    (DAmbient : V.CliffordSpinCandidateRawOnoTamagawaData)
    {c d : ℝ≥0∞}
    (hc : a.IsOneShellSpinTamagawaCoefficient DAmbient c)
    (hd : a.IsOneShellSpinTamagawaCoefficient DAmbient d) :
    c = d := by
  rcases hc with ⟨w, rfl⟩
  rcases hd with ⟨u, rfl⟩
  exact w.coefficient_eq u DAmbient

/-- Mere local complement-lattice existence gives a unique coefficient
scalar.  Certified raw data is introduced only under `Prop` elimination, so
this theorem chooses neither a complement witness nor a raw datum. -/
theorem existsUnique_isOneShellSpinTamagawaCoefficient
    {V : RationalQuadraticSpaceMatrix n}
    (a : V.RepresentedNonzeroRationalNorm)
    (DAmbient : V.CliffordSpinCandidateRawOnoTamagawaData)
    (h : Nonempty (a.OneShellComplementLatticeWitness V)) :
    ∃! c : ℝ≥0∞, a.IsOneShellSpinTamagawaCoefficient DAmbient c := by
  have hCoefficient : Nonempty (a.OneShellSpinCoefficientWitness V) :=
    a.nonempty_oneShellSpinCoefficientWitness_iff.mpr h
  exact hCoefficient.elim fun w ↦ by
    refine ⟨w.coefficient DAmbient, ⟨w, rfl⟩, ?_⟩
    intro c hc
    exact a.isOneShellSpinTamagawaCoefficient_eq
      DAmbient hc ⟨w, rfl⟩

/-- Unique coefficient existence is equivalent to mere local complement-
lattice existence.  Certified raw data contributes no source assumption. -/
theorem existsUnique_isOneShellSpinTamagawaCoefficient_iff_nonempty
    {V : RationalQuadraticSpaceMatrix n}
    (a : V.RepresentedNonzeroRationalNorm)
    (DAmbient : V.CliffordSpinCandidateRawOnoTamagawaData) :
    (∃! c : ℝ≥0∞, a.IsOneShellSpinTamagawaCoefficient DAmbient c) ↔
      Nonempty (a.OneShellComplementLatticeWitness V) := by
  constructor
  · rintro ⟨c, ⟨w, hw⟩, _⟩
    exact ⟨w.toComplementLatticeWitness⟩
  · exact a.existsUnique_isOneShellSpinTamagawaCoefficient DAmbient

/-- The unique scalar attached to a locally inhabited witness type.  This
chooses the coefficient scalar, not a lattice-backed witness. -/
def oneShellSpinTamagawaCoefficient
    {V : RationalQuadraticSpaceMatrix n}
    (a : V.RepresentedNonzeroRationalNorm)
    (DAmbient : V.CliffordSpinCandidateRawOnoTamagawaData)
    (h : Nonempty (a.OneShellComplementLatticeWitness V)) : ℝ≥0∞ :=
  Classical.choose
    (a.existsUnique_isOneShellSpinTamagawaCoefficient DAmbient h).exists

/-- The unique scalar satisfies the local witness relation. -/
theorem oneShellSpinTamagawaCoefficient_spec
    {V : RationalQuadraticSpaceMatrix n}
    (a : V.RepresentedNonzeroRationalNorm)
    (DAmbient : V.CliffordSpinCandidateRawOnoTamagawaData)
    (h : Nonempty (a.OneShellComplementLatticeWitness V)) :
    a.IsOneShellSpinTamagawaCoefficient DAmbient
      (a.oneShellSpinTamagawaCoefficient DAmbient h) :=
  Classical.choose_spec
    (a.existsUnique_isOneShellSpinTamagawaCoefficient DAmbient h).exists

/-- The unique scalar is equal to the coefficient realized by every supplied
local witness. -/
theorem oneShellSpinTamagawaCoefficient_eq_witness
    {V : RationalQuadraticSpaceMatrix n}
    (a : V.RepresentedNonzeroRationalNorm)
    (DAmbient : V.CliffordSpinCandidateRawOnoTamagawaData)
    (h : Nonempty (a.OneShellComplementLatticeWitness V))
    (w : a.OneShellSpinCoefficientWitness V) :
    a.oneShellSpinTamagawaCoefficient DAmbient h =
      w.coefficient DAmbient :=
  a.isOneShellSpinTamagawaCoefficient_eq DAmbient
    (a.oneShellSpinTamagawaCoefficient_spec DAmbient h) ⟨w, rfl⟩

end RepresentedNonzeroRationalNorm

/-- Section-free local complement-lattice existence input for all represented
nonzero norms.  Each fiber is merely asserted nonempty; no dependent family of
complement lattices, vectors, presentations, or raw data is supplied. -/
def OneShellSpinCoefficientLocallyNonempty
    (V : RationalQuadraticSpaceMatrix n) : Prop :=
  ∀ a : V.RepresentedNonzeroRationalNorm,
    Nonempty (a.OneShellComplementLatticeWitness V)

/-- The local complement-lattice premise produces mere coefficient-witness
inhabitation without selecting a witness. -/
theorem OneShellSpinCoefficientLocallyNonempty.coefficientWitness
    {V : RationalQuadraticSpaceMatrix n}
    (hLocal : V.OneShellSpinCoefficientLocallyNonempty)
    (a : V.RepresentedNonzeroRationalNorm) :
    Nonempty (a.OneShellSpinCoefficientWitness V) :=
  a.nonempty_oneShellSpinCoefficientWitness_iff.mpr (hLocal a)

/-- The coefficient function obtained by choosing only the unique scalar at
each norm.  It never chooses a local witness. -/
def representedNormOneShellSpinTamagawaCoefficient
    (V : RationalQuadraticSpaceMatrix n)
    (DAmbient : V.CliffordSpinCandidateRawOnoTamagawaData)
    (hLocal : V.OneShellSpinCoefficientLocallyNonempty) :
    V.RepresentedNonzeroRationalNorm → ℝ≥0∞ :=
  fun a ↦ a.oneShellSpinTamagawaCoefficient DAmbient (hLocal a)

/-- The outer represented-norm coefficient agrees with every supplied local
witness realizing that norm. -/
theorem representedNormOneShellSpinTamagawaCoefficient_eq_witness
    (V : RationalQuadraticSpaceMatrix n)
    (DAmbient : V.CliffordSpinCandidateRawOnoTamagawaData)
    (hLocal : V.OneShellSpinCoefficientLocallyNonempty)
    (a : V.RepresentedNonzeroRationalNorm)
    (w : a.OneShellSpinCoefficientWitness V) :
    V.representedNormOneShellSpinTamagawaCoefficient
        DAmbient hLocal a =
      w.coefficient DAmbient :=
  a.oneShellSpinTamagawaCoefficient_eq_witness
    DAmbient (hLocal a) w

/-- The all-vector weight is one at the zero fiber and is the unique
represented-norm coefficient at every nonzero rational vector. -/
def rationalVectorOneShellSpinTamagawaWeight
    (V : RationalQuadraticSpaceMatrix n)
    (DAmbient : V.CliffordSpinCandidateRawOnoTamagawaData)
    (hLocal : V.OneShellSpinCoefficientLocallyNonempty)
    (x : Fin n → ℚ) : ℝ≥0∞ :=
  if hx : V.nativeRationalQuadraticForm x ≠ 0 then
    V.representedNormOneShellSpinTamagawaCoefficient DAmbient hLocal
      (representedNonzeroRationalNormOfVector V x hx)
  else 1

/-- On a literal represented-norm fiber, the all-vector weight is exactly its
unique coefficient. -/
theorem rationalVectorOneShellSpinTamagawaWeight_eq_of_mem_fiber
    (V : RationalQuadraticSpaceMatrix n)
    (DAmbient : V.CliffordSpinCandidateRawOnoTamagawaData)
    (hLocal : V.OneShellSpinCoefficientLocallyNonempty)
    (a : V.RepresentedNonzeroRationalNorm)
    (x : a.rationalVectorFiber V) :
    V.rationalVectorOneShellSpinTamagawaWeight DAmbient hLocal x.1 =
      V.representedNormOneShellSpinTamagawaCoefficient
        DAmbient hLocal a := by
  have hx : V.nativeRationalQuadraticForm x.1 ≠ 0 := by
    rw [x.property]
    exact a.property.1
  rw [rationalVectorOneShellSpinTamagawaWeight, dif_pos hx]
  congr 1
  exact Subtype.ext x.property

/-- At the zero vector the all-vector weight is one. -/
@[simp]
theorem rationalVectorOneShellSpinTamagawaWeight_zero
    (V : RationalQuadraticSpaceMatrix n)
    (DAmbient : V.CliffordSpinCandidateRawOnoTamagawaData)
    (hLocal : V.OneShellSpinCoefficientLocallyNonempty) :
    V.rationalVectorOneShellSpinTamagawaWeight DAmbient hLocal 0 = 1 := by
  simp [rationalVectorOneShellSpinTamagawaWeight]

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

open RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- Exact weighted zero/nonzero Tonelli expansion.  Its outer coefficient is
the unique scalar realized by local lattice-backed witnesses, while neither a
representative nor a witness family appears in the statement. -/
theorem tsum_rationalVector_oneShellSpinTamagawaWeight_mul
    (L : PositiveDefiniteIntegralLattice n)
    (DAmbient : L.rationalQuadraticSpaceMatrix
      |>.CliffordSpinCandidateRawOnoTamagawaData)
    (hLocal : L.rationalQuadraticSpaceMatrix
      |>.OneShellSpinCoefficientLocallyNonempty)
    (F : (Fin n → ℚ) → ℝ≥0∞) :
    (∑' x,
        (L.rationalQuadraticSpaceMatrix
          |>.rationalVectorOneShellSpinTamagawaWeight
            DAmbient hLocal x) * F x) =
      F 0 +
        ∑' a : L.rationalQuadraticSpaceMatrix
            |>.RepresentedNonzeroRationalNorm,
          (L.rationalQuadraticSpaceMatrix
              |>.representedNormOneShellSpinTamagawaCoefficient
                DAmbient hLocal a) *
            ∑' x : a.rationalVectorFiber L.rationalQuadraticSpaceMatrix,
              F x.1 := by
  let V := L.rationalQuadraticSpaceMatrix
  calc
    (∑' x, V.rationalVectorOneShellSpinTamagawaWeight
        DAmbient hLocal x * F x) =
        V.rationalVectorOneShellSpinTamagawaWeight
            DAmbient hLocal 0 * F 0 +
          ∑' a : V.RepresentedNonzeroRationalNorm,
            ∑' x : a.rationalVectorFiber V,
              V.rationalVectorOneShellSpinTamagawaWeight
                DAmbient hLocal x.1 * F x.1 :=
      L.tsum_rationalVector_eq_zero_add_representedNorm_fibers
        (fun x ↦ V.rationalVectorOneShellSpinTamagawaWeight
          DAmbient hLocal x * F x)
    _ = F 0 +
        ∑' a : V.RepresentedNonzeroRationalNorm,
          V.representedNormOneShellSpinTamagawaCoefficient
              DAmbient hLocal a *
            ∑' x : a.rationalVectorFiber V, F x.1 := by
      rw [V.rationalVectorOneShellSpinTamagawaWeight_zero, one_mul]
      congr 1
      apply tsum_congr
      intro a
      calc
        (∑' x : a.rationalVectorFiber V,
            V.rationalVectorOneShellSpinTamagawaWeight
              DAmbient hLocal x.1 * F x.1) =
            ∑' x : a.rationalVectorFiber V,
              V.representedNormOneShellSpinTamagawaCoefficient
                DAmbient hLocal a * F x.1 := by
          apply tsum_congr
          intro x
          rw [V.rationalVectorOneShellSpinTamagawaWeight_eq_of_mem_fiber
            DAmbient hLocal a x]
        _ = V.representedNormOneShellSpinTamagawaCoefficient
              DAmbient hLocal a *
            ∑' x : a.rationalVectorFiber V, F x.1 :=
          ENNReal.tsum_mul_left

end PositiveDefiniteIntegralLattice

end

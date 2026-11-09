import SMSFormula.AdelicFinitePresentation
import SMSFormula.RealShellCompactness
import SMSFormula.ShiftedGaussianQuadratic
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.Algebra.Indicator
import Mathlib.Topology.Separation.Profinite
import SMSFormula.RationalFiniteAdeleStandardCompactFamily
import SMSFormula.RationalAdeleFiniteLocalTruncation
import SMSFormula.FiniteAdelicEntryMap

/-!
# A compact-open exhaustion replaces the concentration hypothesis

The determining criterion holds on `shell x Y` with `Y` compact, and the integral finite adelic
vectors supply such a `Y`.  That criterion also needs concentration: an adelic measure lives on the whole finite factor, and saying that it gives the complement of the
compact carrier measure zero is a real statement about the measure, not a topological fact.

Concentration is not needed.  The finite factor is exhausted by compact open sets -- the `c`-divided
lattices, every finite adelic vector having a natural denominator -- so the two measures may be
compared piece by piece and Mathlib's restriction extensionality assembles the pieces.  On each
piece the restricted measures are concentrated on a compact set, by the trivial reason that a
restriction lives on its own set, which is exactly the hypothesis `RealShell.eq_of_concentrated`
consumes.

And the piece costs nothing in the hypothesis.  Restricting a generator `Gamma_u TENSOR 1_S` to the
piece `univ x T` multiplies it by `1_T`, giving `Gamma_u TENSOR 1_(S cap T)` -- again a generator,
because the pieces are clopen.  So the per-piece hypothesis follows from the same indexed family the
compact criterion already used: no new test, no new index.

Negative scope.  This is still the determining criterion: it compares two measures that are given and
constructs neither.  The exhaustion must be countable and by compact open sets, and both are real
conditions -- the archimedean line has no such exhaustion by clopen sets at all, which is why the
archimedean factor still enters through the compact shell.  Regularity is what makes each piece
finite, and it stays explicit.
-/

namespace SMSFormula.Exhaustion

open MeasureTheory Set SMSFormula.ShiftedGaussian

/-! ## A restriction is concentrated on its own set -/

section Abstract

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

omit [TopologicalSpace X] [BorelSpace X] in
/-- The trivial concentration: a restriction gives the complement of its own set measure zero. -/
theorem restrict_compl_eq_zero (μ : Measure X) {K : Set X} (hK : MeasurableSet K) :
    (μ.restrict K) Kᶜ = 0 := by
  rw [Measure.restrict_apply hK.compl, Set.compl_inter_self]
  exact measure_empty

omit [TopologicalSpace X] [BorelSpace X] in
/-- And it is finite as soon as the set has finite measure. -/
theorem isFiniteMeasure_restrict {μ : Measure X} {K : Set X} (h : μ K ≠ ⊤) :
    IsFiniteMeasure (μ.restrict K) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact h.lt_top⟩

/-- The exhaustion criterion, with no concentration hypothesis: two regular measures agreeing
against a point-separating subalgebra on each piece of a countable compact exhaustion are equal.
Regularity supplies finiteness of each piece; the restriction supplies its own concentration. -/
theorem eq_of_compact_exhaustion [T2Space X] [LocallyCompactSpace X]
    {μ ν : Measure X} [μ.Regular] [ν.Regular]
    {ι : Type*} [Countable ι] {K : ι → Set X}
    (hKc : ∀ j, IsCompact (K j)) (hKm : ∀ j, MeasurableSet (K j)) (hcover : ⋃ j, K j = univ)
    (A : Subalgebra ℝ C(X, ℝ)) (hA : A.SeparatesPoints)
    (hagree : ∀ j, ∀ g : A, ∫ x, (g : C(X, ℝ)) x ∂(μ.restrict (K j)) =
      ∫ x, (g : C(X, ℝ)) x ∂(ν.restrict (K j))) :
    μ = ν := by
  refine Measure.ext_of_iUnion_eq_univ hcover fun j ↦ ?_
  have hμt : μ (K j) ≠ ⊤ := (hKc j).measure_lt_top.ne
  have hνt : ν (K j) ≠ ⊤ := (hKc j).measure_lt_top.ne
  haveI := isFiniteMeasure_restrict hμt
  haveI := isFiniteMeasure_restrict hνt
  haveI : (μ.restrict (K j)).Regular := Measure.Regular.restrict_of_measure_ne_top hμt
  haveI : (ν.restrict (K j)).Regular := Measure.Regular.restrict_of_measure_ne_top hνt
  exact SMSFormula.RealShell.eq_of_concentrated (hKc j)
    (restrict_compl_eq_zero μ (hKm j)) (restrict_compl_eq_zero ν (hKm j)) A hA (hagree j)

end Abstract

/-! ## The product: a clopen exhaustion of the second factor -/

section Product

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

end Product

end SMSFormula.Exhaustion

/-! ## The repository's own finite factor, with no compactness and no concentration -/

namespace PositiveDefiniteIntegralLattice

open MeasureTheory Set RationalQuadraticSpaceMatrix SMSFormula.Exhaustion
open SMSFormula.ShiftedGaussian

/-- Every finite adelic vector has a natural denominator: the repository's own one-coordinate
statement, assembled over the finitely many coordinates by the product of the denominators.  No
`lcm` is needed -- the product clears every coordinate because the other factors are integral. -/
theorem exists_natScale_mem_standardDividedLattice (n : ℕ) (x : Fin n → RationalFiniteAdele) :
    ∃ c : ℕ, c ≠ 0 ∧ x ∈ standardDividedLattice n c := by
  choose N hN hmem using fun i : Fin n ↦ exists_natScale_mem_integral (x i)
  refine ⟨∏ i, N i, Finset.prod_ne_zero_iff.2 fun i _ ↦ hN i, fun i ↦ ?_⟩
  have hsplit : (((∏ j, N j : ℕ)) : RationalFiniteAdele) * x i =
      (((∏ j ∈ Finset.univ.erase i, N j : ℕ)) : RationalFiniteAdele) *
        (((N i : ℕ)) : RationalFiniteAdele) * x i := by
    rw [← Nat.cast_mul, Finset.prod_erase_mul Finset.univ N (Finset.mem_univ i)]
  have hmul : (((∏ j, N j : ℕ)) : RationalFiniteAdele) * x i ∈ integralFiniteAdeleSubring := by
    rw [hsplit, mul_assoc]
    exact Subring.mul_mem _ (natCast_mem _ _) (hmem i)
  show ((∏ j, N j) • x) i ∈ integralFiniteAdeleSubring
  rw [Pi.smul_apply, nsmul_eq_mul]
  exact hmul

/-- The divided lattices are clopen and compact, so they are an admissible exhaustion. -/
theorem isClopen_standardDividedLattice {n c : ℕ} (hc : c ≠ 0) :
    IsClopen (standardDividedLattice n c) := by
  haveI := t2Space_rationalFiniteAdele
  exact ⟨(isCompact_standardDividedLattice hc).isClosed, isOpen_standardDividedLattice n c⟩

end PositiveDefiniteIntegralLattice

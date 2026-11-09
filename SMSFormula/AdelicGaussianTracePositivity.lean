import SMSFormula.AdelicSignedValueDensity
import SMSFormula.ShellFiniteSumMajorant

/-!
# Trace positivity on the actual fixed-width adelic Gaussian core

The auxiliary test is a finite sum of paired shifted Gaussians times the
indicator of a divided carrier. Compactness is proved inside that carrier;
the strict negative set vanishes outside it. All tests use the existing width,
real/finite splitting and signed Fourier density.
-/

noncomputable section
open MeasureTheory PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix
open SMSFormula.ShiftedGaussian SMSFormula.ShellFixedWidth

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
variable {n : ℕ}

/-- A real notation for the existing polar Gaussian, not a new test family. -/
abbrev realShiftedGaussian (L : PositiveDefiniteIntegralLattice n) (b : ℝ) (u x : Fin n → ℝ) : ℝ :=
  (polarRealGaussian L (b : ℂ) (x - u)).re

theorem realShiftedGaussian_eq (L : PositiveDefiniteIntegralLattice n) (b : ℝ) (u x : Fin n → ℝ) :
    realShiftedGaussian L b u x =
      quadraticShiftedGaussian L.polarQuadraticForm L.continuous_polarQuadraticForm
        (Real.pi * b) (ContinuousMap.id _) u x := by
  rw [realShiftedGaussian, polarRealGaussian_eq_quadraticShiftedGaussian]
  change Real.exp _ = Real.exp _
  congr 1
  simp

theorem realShiftedGaussian_pos (L : PositiveDefiniteIntegralLattice n) (b : ℝ) (u x : Fin n → ℝ) :
    0 < realShiftedGaussian L b u x := by
  rw [realShiftedGaussian_eq, quadraticShiftedGaussian_apply]
  exact Real.exp_pos _

theorem continuous_realShiftedGaussian (L : PositiveDefiniteIntegralLattice n) (b : ℝ) (u : Fin n → ℝ) :
    Continuous (realShiftedGaussian L b u) := by
  convert (quadraticShiftedGaussian L.polarQuadraticForm L.continuous_polarQuadraticForm
    (Real.pi * b) (ContinuousMap.id _) u).continuous using 1
  funext x
  exact realShiftedGaussian_eq L b u x

/-- The indicator of a divided carrier has period one: that carrier is
stable under addition of integral vectors. No new cutoff is introduced. -/
theorem dividedIndicator_standard (c : ℕ) :
    IsStandardCarried c (fun y : Fin n → RationalFiniteAdele ↦
      (((standardDividedLattice n c).indicator (fun _ ↦ (1 : ℝ)) y : ℝ) : ℂ)) ∧
    IsStandardPeriodic 1 (fun y : Fin n → RationalFiniteAdele ↦
      (((standardDividedLattice n c).indicator (fun _ ↦ (1 : ℝ)) y : ℝ) : ℂ)) := by
  classical
  refine ⟨fun y hy ↦ by simp [Set.indicator_of_notMem hy], ?_⟩
  intro y z hz
  have heq : y + 1 • z ∈ standardDividedLattice n c ↔ y ∈ standardDividedLattice n c := by
    change c • (y + 1 • z) ∈ integralFiniteAdeleVectors n ↔ _
    simp only [one_smul, smul_add]
    constructor
    · intro h i
      have hsub := (integralFiniteAdeleSubring).sub_mem (h i)
        ((nsmul_mem_integralFiniteAdeleVectors hz (m := c)) i)
      simpa using hsub
    · intro h i
      exact (integralFiniteAdeleSubring).add_mem (h i)
        ((nsmul_mem_integralFiniteAdeleVectors hz (m := c)) i)
  simp only [Set.indicator_apply, heq]

/-- Continuity of the inverse of the existing canonical coordinate split. -/
theorem continuous_realFiniteEquiv_symm :
    Continuous (rationalAdeleVectorRealFiniteEquiv n).symm := by
  change Continuous (fun p : (Fin n → ℝ) × (Fin n → RationalFiniteAdele) ↦
    fun i ↦ (rationalInfiniteAdeleContinuousAddEquivReal.symm (p.1 i), p.2 i))
  fun_prop

/-- Compact bad sets for a finite Gaussian domination on a compact finite
carrier. The auxiliary's analytic admissibility is supplied separately below. -/
theorem exists_compact_badSets_on_carrier (L : PositiveDefiniteIntegralLattice n) {b : ℝ} (hb : 0 < b)
    {ι : Type*} [Fintype ι] [Nonempty ι] {c : ℕ} (hc : c ≠ 0)
    (u : ι → Fin n → ℝ) (v : Fin n → Fin n → ℝ)
    (hspan : Submodule.span ℝ (Set.range v) = ⊤) [Nonempty (Fin n)]
    {f h : (Fin n → RationalAdele) → ℝ} (hf : Continuous f) (hh : Continuous h)
    (hoff : ∀ x, rationalAdeleVectorFinitePart n x ∉ standardDividedLattice n c →
      f x = 0 ∧ h x = 0)
    {M : ι → ℝ} (hM : ∀ j, 0 ≤ M j)
    (hdom : ∀ x, |f x| ≤ ∑ j, M j * realShiftedGaussian L b (u j)
      (rationalAdeleVectorRealPart n x))
    (hmaj : ∀ j k x, rationalAdeleVectorFinitePart n x ∈ standardDividedLattice n c →
      realShiftedGaussian L b (u j + v k) (rationalAdeleVectorRealPart n x) +
      realShiftedGaussian L b (u j - v k) (rationalAdeleVectorRealPart n x) ≤ h x)
    (a : RationalAdele)
    (htrace : ∀ x, L.rationalQuadraticSpaceMatrix.fullAdelicQuadraticFormValue x = a → 0 ≤ f x) :
    ∀ ε : ℝ, 0 < ε → ∃ C : Set (Fin n → RationalAdele), IsCompact C ∧
      Disjoint C (L.rationalQuadraticSpaceMatrix.fullAdelicQuadraticFormValue ⁻¹' {a}) ∧
      {x | f x + ε * h x < 0} ⊆ C := by
  classical
  let K := standardDividedLattice n c
  letI : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_standardDividedLattice hc)
  let e : (Fin n → ℝ) × K → (Fin n → RationalAdele) :=
    fun p ↦ (rationalAdeleVectorRealFiniteEquiv n).symm (p.1, p.2.val)
  have he : Continuous e := continuous_realFiniteEquiv_symm.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have heReal : ∀ p, rationalAdeleVectorRealPart n (e p) = p.1 := fun p ↦
    congrArg Prod.fst ((rationalAdeleVectorRealFiniteEquiv n).apply_symm_apply (p.1, p.2.val))
  have heFin : ∀ p, rationalAdeleVectorFinitePart n (e p) = p.2.val := fun p ↦
    congrArg Prod.snd ((rationalAdeleVectorRealFiniteEquiv n).apply_symm_apply (p.1, p.2.val))
  intro ε hε
  have hcompact : IsCompact {p : (Fin n → ℝ) × K | f (e p) + ε * h (e p) ≤ 0} := by
    apply isCompact_badSet_of_finiteSumMajorant L.polarQuadraticForm
      L.continuous_polarQuadraticForm L.posDef_polarQuadraticForm
      (mul_pos Real.pi_pos hb) hspan u (hf.comp he) (hh.comp he) hε hM
    · intro p
      simpa only [heReal, realShiftedGaussian_eq, quadraticShiftedGaussian_apply,
        ContinuousMap.fst_apply, ContinuousMap.id_apply] using hdom (e p)
    · intro j k p
      have hp : rationalAdeleVectorFinitePart n (e p) ∈ standardDividedLattice n c :=
        (heFin p).symm ▸ p.2.property
      simpa only [heReal, realShiftedGaussian_eq, quadraticShiftedGaussian_apply,
        ContinuousMap.fst_apply, ContinuousMap.id_apply] using hmaj j k (e p) hp
  refine ⟨e '' {p | f (e p) + ε * h (e p) ≤ 0}, hcompact.image he, ?_, ?_⟩
  · rw [Set.disjoint_left]
    rintro x ⟨p, hp, rfl⟩ hpa
    have hfp := htrace (e p) hpa
    have hpK : rationalAdeleVectorFinitePart n (e p) ∈ standardDividedLattice n c :=
      (heFin p).symm ▸ p.2.property
    have hhp : 0 < h (e p) := lt_of_lt_of_le
      (add_pos (realShiftedGaussian_pos L b _ _) (realShiftedGaussian_pos L b _ _))
      (hmaj (Classical.arbitrary ι) (Classical.arbitrary (Fin n)) (e p) hpK)
    have := mul_pos hε hhp
    dsimp only [Set.mem_setOf_eq] at hp
    linarith
  · intro x hx
    have hxK : rationalAdeleVectorFinitePart n x ∈ K := by
      by_contra hn
      obtain ⟨hf0, hh0⟩ := hoff x hn
      simp [hf0, hh0] at hx
    let p : (Fin n → ℝ) × K :=
      (rationalAdeleVectorRealPart n x, ⟨rationalAdeleVectorFinitePart n x, hxK⟩)
    have hep : e p = x := (rationalAdeleVectorRealFiniteEquiv n).symm_apply_apply x
    refine ⟨p, ?_, hep⟩
    change f x + ε * h x < 0 at hx
    change f (e p) + ε * h (e p) ≤ 0
    simpa only [hep] using hx.le

/-- Finite sums retain the signed density law, with Bochner integrability on
both sides. The zero case is obtained by scalar multiplication of a supplied test. -/
theorem signedDensity_sum {ι : Type*} [Fintype ι] [Nonempty ι]
    {V : RationalQuadraticSpaceMatrix n} {f : ι → (Fin n → RationalAdele) → ℝ}
    (hf : ∀ j, V.HasSignedValueDensity (f j)) :
    V.HasSignedValueDensity (fun x ↦ ∑ j, f j x) := by
  classical
  have hzero : V.HasSignedValueDensity 0 := by
    simpa using (hf (Classical.arbitrary ι)).smul 0
  have hs : ∀ s : Finset ι, V.HasSignedValueDensity (∑ j ∈ s, f j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | @insert j s hj ih => simpa [Finset.sum_insert hj] using (hf j).add ih
  convert hs Finset.univ using 1
  ext x
  simp

/-- For a finite sum on one divided carrier, trace nonnegativity implies
pointwise nonnegativity of the actual value density. The paired-centre auxiliary
and its admissibility are constructed, not assumed. -/
theorem realValueDensity_nonneg_of_finite_gaussian_sum (L : PositiveDefiniteIntegralLattice n)
    (hn : 4 < n) {b : ℝ} (hb : 0 < b) {ι : Type*} [Fintype ι] [Nonempty ι]
    {c : ℕ} (hc : c ≠ 0) (u : ι → Fin n → ℝ)
    (g : ι → (Fin n → RationalFiniteAdele) → ℝ) (d : ι → ℕ)
    (hd : ∀ j, d j ≠ 0)
    (hcar : ∀ j, IsStandardCarried c (fun y ↦ (g j y : ℂ)))
    (hper : ∀ j, IsStandardPeriodic (d j) (fun y ↦ (g j y : ℂ)))
    (a : RationalAdele)
    (htrace : ∀ x, L.rationalQuadraticSpaceMatrix.fullAdelicQuadraticFormValue x = a →
      0 ≤ ∑ j, realShiftedGaussian L b (u j) (rationalAdeleVectorRealPart n x) *
        g j (rationalAdeleVectorFinitePart n x)) :
    0 ≤ L.rationalQuadraticSpaceMatrix.realValueDensity
      (fun x ↦ ∑ j, realShiftedGaussian L b (u j) (rationalAdeleVectorRealPart n x) *
        g j (rationalAdeleVectorFinitePart n x)) a := by
  classical
  letI : NeZero n := ⟨by omega⟩
  let I : (Fin n → RationalFiniteAdele) → ℝ :=
    (standardDividedLattice n c).indicator (fun _ ↦ 1)
  let v : Fin n → Fin n → ℝ := Pi.basisFun ℝ (Fin n)
  let F : (Fin n → RationalAdele) → ℝ := fun x ↦
    ∑ j, realShiftedGaussian L b (u j) (rationalAdeleVectorRealPart n x) *
      g j (rationalAdeleVectorFinitePart n x)
  let H : (Fin n → RationalAdele) → ℝ := fun x ↦ ∑ j, ∑ k : Fin n,
    (realShiftedGaussian L b (u j + v k) (rationalAdeleVectorRealPart n x) +
      realShiftedGaussian L b (u j - v k) (rationalAdeleVectorRealPart n x)) *
        I (rationalAdeleVectorFinitePart n x)
  have hR : Continuous (rationalAdeleVectorRealPart n) := by
    unfold rationalAdeleVectorRealPart; fun_prop
  have hS : Continuous (rationalAdeleVectorFinitePart n) := by
    unfold rationalAdeleVectorFinitePart; fun_prop
  have hgcont : ∀ j, Continuous (g j) := fun j ↦ by
    simpa using Complex.continuous_re.comp ((hper j).continuous (hd j))
  have hIcont : Continuous I := by
    have hIC : Continuous (fun y ↦ (I y : ℂ)) :=
      (dividedIndicator_standard (n := n) c).2.continuous one_ne_zero
    simpa only [Function.comp_def, Complex.ofReal_re] using Complex.continuous_re.comp hIC
  have hFcont : Continuous F := by
    exact continuous_finset_sum _ fun j _ ↦
      ((continuous_realShiftedGaussian L b (u j)).comp hR).mul ((hgcont j).comp hS)
  have hHcont : Continuous H := by
    exact continuous_finset_sum _ fun j _ ↦ continuous_finset_sum _ fun k _ ↦
      (((continuous_realShiftedGaussian L b (u j + v k)).comp hR).add
        ((continuous_realShiftedGaussian L b (u j - v k)).comp hR)).mul (hIcont.comp hS)
  have hFsigned : L.rationalQuadraticSpaceMatrix.HasSignedValueDensity F :=
    signedDensity_sum fun j ↦ hasSignedValueDensity_shiftedGaussian L hn hb (u j) hc
      (hd j) (hcar j) (hper j)
  have hHsigned : L.rationalQuadraticSpaceMatrix.HasSignedValueDensity H := by
    apply signedDensity_sum
    intro j
    apply signedDensity_sum
    intro k
    have hplus := hasSignedValueDensity_shiftedGaussian L hn hb (u j + v k) hc
      one_ne_zero (g := I) (dividedIndicator_standard (n := n) c).1 (dividedIndicator_standard (n := n) c).2
    have hminus := hasSignedValueDensity_shiftedGaussian L hn hb (u j - v k) hc
      one_ne_zero (g := I) (dividedIndicator_standard (n := n) c).1 (dividedIndicator_standard (n := n) c).2
    simpa only [Pi.add_apply, add_mul] using hplus.add hminus
  have hHnonneg : ∀ x, 0 ≤ H x := by
    intro x
    apply Finset.sum_nonneg
    intro j _
    apply Finset.sum_nonneg
    intro k _
    exact mul_nonneg (add_nonneg (realShiftedGaussian_pos L b _ _).le
      (realShiftedGaussian_pos L b _ _).le) (Set.indicator_apply_nonneg (fun _ ↦ zero_le_one))
  have hbounded : ∀ j, ∃ M : ℝ, 0 ≤ M ∧ ∀ y, |g j y| ≤ M := by
    intro j
    obtain ⟨M, hM⟩ := ((hcar j).hasCompactSupport hc).exists_bound_of_continuous
      ((hper j).continuous (hd j))
    refine ⟨max M 0, le_max_right _ _, fun y ↦ ?_⟩
    exact le_trans (by simpa using hM y) (le_max_left _ _)
  choose M hM hbound using hbounded
  have hdom : ∀ x, |F x| ≤ ∑ j, M j * realShiftedGaussian L b (u j)
      (rationalAdeleVectorRealPart n x) := by
    intro x
    calc |F x| ≤ ∑ j, |realShiftedGaussian L b (u j) (rationalAdeleVectorRealPart n x) *
          g j (rationalAdeleVectorFinitePart n x)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, M j * realShiftedGaussian L b (u j) (rationalAdeleVectorRealPart n x) := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, abs_of_pos (realShiftedGaussian_pos L b _ _), mul_comm]
        exact mul_le_mul_of_nonneg_right (hbound j _) (realShiftedGaussian_pos L b _ _).le
  have hmaj : ∀ j k x, rationalAdeleVectorFinitePart n x ∈ standardDividedLattice n c →
      realShiftedGaussian L b (u j + v k) (rationalAdeleVectorRealPart n x) +
      realShiftedGaussian L b (u j - v k) (rationalAdeleVectorRealPart n x) ≤ H x := by
    intro j k x hx
    have hI : I (rationalAdeleVectorFinitePart n x) = 1 := Set.indicator_of_mem hx _
    dsimp only [H]
    simp only [hI, mul_one]
    let P : ι → Fin n → ℝ := fun j' l ↦
      realShiftedGaussian L b (u j' + v l) (rationalAdeleVectorRealPart n x) +
      realShiftedGaussian L b (u j' - v l) (rationalAdeleVectorRealPart n x)
    have hP : ∀ j' l, 0 ≤ P j' l := fun j' l ↦
      add_nonneg (realShiftedGaussian_pos L b _ _).le (realShiftedGaussian_pos L b _ _).le
    change P j k ≤ ∑ j', ∑ l, P j' l
    exact le_trans (Finset.single_le_sum (f := P j) (fun l _ ↦ hP j l) (Finset.mem_univ k))
      (Finset.single_le_sum (f := fun j' ↦ ∑ l, P j' l)
        (fun j' _ ↦ Finset.sum_nonneg fun l _ ↦ hP j' l) (Finset.mem_univ j))
  apply L.rationalQuadraticSpaceMatrix.realValueDensity_nonneg_of_compact_bad_sets
    hFsigned hHsigned hHnonneg a
  apply exists_compact_badSets_on_carrier L hb hc u v (Pi.basisFun ℝ (Fin n)).span_eq
    hFcont hHcont _ hM hdom hmaj a htrace
  intro x hx
  have hI : I (rationalAdeleVectorFinitePart n x) = 0 := Set.indicator_of_notMem hx _
  have hgzero : ∀ j, g j (rationalAdeleVectorFinitePart n x) = 0 := fun j ↦
    Complex.ofReal_eq_zero.mp (hcar j _ hx)
  simp [F, H, hgzero, hI]

/-- A name for exactly the real span in `AdelicSignedValueDensity`; the generator
set is unchanged. This is the ambient test core, before taking any trace. -/
abbrev realGaussianCore (L : PositiveDefiniteIntegralLattice n) (b : ℝ) :
    Submodule ℝ ((Fin n → RationalAdele) → ℝ) :=
  Submodule.span ℝ {f | ∃ (u : Fin n → ℝ) (c d : ℕ)
    (g : (Fin n → RationalFiniteAdele) → ℝ), c ≠ 0 ∧ d ≠ 0 ∧
    IsStandardCarried c (fun y ↦ (g y : ℂ)) ∧ IsStandardPeriodic d (fun y ↦ (g y : ℂ)) ∧
    f = fun x ↦ realShiftedGaussian L b u (rationalAdeleVectorRealPart n x) *
      g (rationalAdeleVectorFinitePart n x)}

/-- Trace positivity for every member of the old real Gaussian core. The finite
support of a span expression supplies one common carrier (the product of
its nonzero scales), while all signed scalar coefficients are absorbed in the
finite factors. No rational point, fiber representative or extension is selected. -/
theorem realValueDensity_nonneg_of_trace_nonneg (L : PositiveDefiniteIntegralLattice n)
    (hn : 4 < n) {b : ℝ} (hb : 0 < b) {f : (Fin n → RationalAdele) → ℝ}
    (hf : f ∈ realGaussianCore L b) (a : RationalAdele)
    (htrace : ∀ x, L.rationalQuadraticSpaceMatrix.fullAdelicQuadraticFormValue x = a → 0 ≤ f x) :
    0 ≤ L.rationalQuadraticSpaceMatrix.realValueDensity f a := by
  classical
  obtain ⟨w, t, hts, _, hrep⟩ := Submodule.mem_span_iff_exists_finset_subset.mp hf
  by_cases ht : t.Nonempty
  · letI : Nonempty ↥t := ht.to_subtype
    have hgen : ∀ j : ↥t, ∃ (u : Fin n → ℝ) (c d : ℕ)
        (g : (Fin n → RationalFiniteAdele) → ℝ), c ≠ 0 ∧ d ≠ 0 ∧
        IsStandardCarried c (fun y ↦ (g y : ℂ)) ∧ IsStandardPeriodic d (fun y ↦ (g y : ℂ)) ∧
        j.val = fun x ↦ realShiftedGaussian L b u (rationalAdeleVectorRealPart n x) *
          g (rationalAdeleVectorFinitePart n x) := fun j ↦ hts j.property
    choose u c d g hc hd hcar hper heq using hgen
    let C := ∏ j : ↥t, c j
    have hC : C ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ ↦ hc j)
    let g' : ↥t → (Fin n → RationalFiniteAdele) → ℝ := fun j y ↦ w j.val * g j y
    have hcar' : ∀ j, IsStandardCarried C (fun y ↦ (g' j y : ℂ)) := by
      intro j
      have h := ((hcar j).const_mul (w j.val : ℂ)).mono
        (Finset.dvd_prod_of_mem c (Finset.mem_univ j))
      simpa only [g', Complex.ofReal_mul] using h
    have hper' : ∀ j, IsStandardPeriodic (d j) (fun y ↦ (g' j y : ℂ)) := by
      intro j
      simpa only [g', Complex.ofReal_mul] using (hper j).const_mul (w j.val : ℂ)
    have hF : f = fun x ↦ ∑ j : ↥t,
        realShiftedGaussian L b (u j) (rationalAdeleVectorRealPart n x) *
          g' j (rationalAdeleVectorFinitePart n x) := by
      rw [← hrep]
      funext x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [← Finset.sum_coe_sort]
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [g']
      rw [heq j]
      ring
    rw [hF] at htrace ⊢
    exact realValueDensity_nonneg_of_finite_gaussian_sum L hn hb hC u g' d hd hcar' hper' a htrace
  · have ht0 : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    have hf0 : f = 0 := by simpa [ht0] using hrep.symm
    rw [hf0]
    have hzero := L.rationalQuadraticSpaceMatrix.realValueDensity_smul 0 (0 : (Fin n → RationalAdele) → ℝ)
    have hd0 : L.rationalQuadraticSpaceMatrix.realValueDensity 0 = 0 := by simpa using hzero
    rw [hd0]
    exact le_rfl

/-- The actual density annihilates trace-zero tests; both signs stay in the
same fixed-width real core. This is pointwise at every adelic value. -/
theorem realValueDensity_eq_zero_of_trace_zero (L : PositiveDefiniteIntegralLattice n)
    (hn : 4 < n) {b : ℝ} (hb : 0 < b) {f : (Fin n → RationalAdele) → ℝ}
    (hf : f ∈ realGaussianCore L b) (a : RationalAdele)
    (htrace : ∀ x, L.rationalQuadraticSpaceMatrix.fullAdelicQuadraticFormValue x = a → f x = 0) :
    L.rationalQuadraticSpaceMatrix.realValueDensity f a = 0 := by
  have hp := realValueDensity_nonneg_of_trace_nonneg L hn hb hf a
    (fun x hx ↦ (htrace x hx).ge)
  have hm := realValueDensity_nonneg_of_trace_nonneg L hn hb
    ((realGaussianCore L b).smul_mem (-1) hf) a
    (fun x hx ↦ by simp [htrace x hx])
  rw [L.rationalQuadraticSpaceMatrix.realValueDensity_smul] at hm
  change 0 ≤ -1 * L.rationalQuadraticSpaceMatrix.realValueDensity f a at hm
  linarith

/-- Hence the density depends only on the restriction to the actual adelic
fiber, not on which core test presents that restriction. -/
theorem realValueDensity_eq_of_trace_eq (L : PositiveDefiniteIntegralLattice n)
    (hn : 4 < n) {b : ℝ} (hb : 0 < b) {f g : (Fin n → RationalAdele) → ℝ}
    (hf : f ∈ realGaussianCore L b) (hg : g ∈ realGaussianCore L b) (a : RationalAdele)
    (htrace : ∀ x, L.rationalQuadraticSpaceMatrix.fullAdelicQuadraticFormValue x = a → f x = g x) :
    L.rationalQuadraticSpaceMatrix.realValueDensity f a =
      L.rationalQuadraticSpaceMatrix.realValueDensity g a := by
  have hz := realValueDensity_eq_zero_of_trace_zero L hn hb
    ((realGaussianCore L b).sub_mem hf hg) a (fun x hx ↦ sub_eq_zero.mpr (htrace x hx))
  have hfs := hasSignedValueDensity_of_mem_real_span L hn hb hf
  have hgs := hasSignedValueDensity_of_mem_real_span L hn hb hg
  have heq : f - g = f + (-1 : ℝ) • g := by ext x; simp [sub_eq_add_neg]
  rw [heq, L.rationalQuadraticSpaceMatrix.realValueDensity_add hfs.1 (hgs.smul (-1)).1,
    L.rationalQuadraticSpaceMatrix.realValueDensity_smul] at hz
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hz
  linarith

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

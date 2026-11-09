import SMSFormula.RationalFiniteAdeleStandardCompactFamily
import SMSFormula.RationalAdeleVectorPolarPoissonReduction

/-!
# The standard compact family on the rational diagonal

Poisson summation for the enlarged orbit needs to know what a finite test in
the standard compact locally constant family does on the rational diagonal
`q : Q^n`.  This file proves the exact answer, using only the existing standard
lattice, the existing rational-integrality criterion for finite adeles, and the
family conditions already closed.

* A `c`-carried test vanishes at the diagonal of `q` unless `c * q` is an
  integral rational vector, so the diagonal restriction is supported on the
  literal `c`-divided rational lattice `(1/c) Z^n`.
* A `d`-periodic test is invariant under the diagonal of every `d * Z^n` shift.
* Every member with nonzero scales is globally bounded, since it is continuous
  with compact support.

Consequently the rational-diagonal sum of `g * f` collapses to a sum over
`Z^n` reindexed by `m |-> m / c`, and it converges as soon as the other factor
is absolutely summable along that scaled lattice.

No Poisson summation, theta transformation, Euclidean lattice identity, or
Gaussian summability statement is asserted here; the real factor stays an
arbitrary supplied `g` with an explicit summability hypothesis.  No new lattice,
representative, section, chart or Haar normalization is chosen.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory Matrix
open scoped BigOperators

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-! ## The finite diagonal -/

/-- The finite component of the rational diagonal. -/
def rationalFiniteAdeleVectorDiagonal (n : ℕ) (q : Fin n → ℚ) :
    Fin n → RationalFiniteAdele :=
  fun i => algebraMap ℚ RationalFiniteAdele (q i)

@[simp]
theorem rationalAdeleVectorFinitePart_diagonal (n : ℕ) (q : Fin n → ℚ) :
    rationalAdeleVectorFinitePart n (rationalAdeleVectorDiagonal n q) =
      rationalFiniteAdeleVectorDiagonal n q :=
  rationalAdeleVectorFinitePart_rationalDiagonal n q

theorem nsmul_rationalFiniteAdeleVectorDiagonal (c : ℕ) (q : Fin n → ℚ) :
    c • rationalFiniteAdeleVectorDiagonal n q =
      rationalFiniteAdeleVectorDiagonal n (fun i => (c : ℚ) * q i) := by
  funext i
  show c • algebraMap ℚ RationalFiniteAdele (q i) =
    algebraMap ℚ RationalFiniteAdele ((c : ℚ) * q i)
  rw [nsmul_eq_mul, map_mul]
  norm_num

/-! ## The `c`-divided rational lattice -/

/-- Rational vectors whose `c`-multiple is integral. -/
def rationalDividedIntegralVectors (n c : ℕ) : Set (Fin n → ℚ) :=
  {q | ∀ i, (c : ℚ) * q i ∈ Set.range (algebraMap ℤ ℚ)}

@[simp]
theorem rationalDividedIntegralVectors_one :
    rationalDividedIntegralVectors n 1 = rationalIntegralVectors n := by
  ext q
  simp [rationalDividedIntegralVectors, rationalIntegralVectors]

/-- The carrier condition on the rational diagonal is exactly the literal
`c`-divided rational integrality condition. -/
theorem mem_standardDividedLattice_rationalDiagonal_iff (c : ℕ) (q : Fin n → ℚ) :
    rationalFiniteAdeleVectorDiagonal n q ∈ standardDividedLattice n c ↔
      q ∈ rationalDividedIntegralVectors n c := by
  rw [mem_standardDividedLattice_iff, nsmul_rationalFiniteAdeleVectorDiagonal]
  constructor
  · intro h i
    exact (rational_mem_integralFiniteAdeleSubring_iff ((c : ℚ) * q i)).mp (h i)
  · intro h i
    exact (rational_mem_integralFiniteAdeleSubring_iff ((c : ℚ) * q i)).mpr (h i)

/-- The scaled integer lattice parametrization of the `c`-divided rational
lattice.  No representative is chosen: this is the literal division map. -/
def rationalScaledIntegerVector (c : ℕ) (m : Fin n → ℤ) : Fin n → ℚ :=
  fun i => (m i : ℚ) / (c : ℚ)

theorem injective_rationalScaledIntegerVector {c : ℕ} (hc : c ≠ 0) :
    Function.Injective (rationalScaledIntegerVector (n := n) c) := by
  have hq : ((c : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hc
  intro m m' h
  funext i
  have hi : ((m i : ℚ)) / (c : ℚ) = ((m' i : ℚ)) / (c : ℚ) := congrFun h i
  field_simp at hi
  exact_mod_cast hi

theorem rationalDividedIntegralVectors_eq_range {c : ℕ} (hc : c ≠ 0) :
    rationalDividedIntegralVectors n c =
      Set.range (rationalScaledIntegerVector (n := n) c) := by
  classical
  have hq : ((c : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hc
  ext q
  constructor
  · intro hqmem
    refine ⟨fun i => (hqmem i).choose, ?_⟩
    funext i
    have hi : algebraMap ℤ ℚ ((hqmem i).choose) = (c : ℚ) * q i := (hqmem i).choose_spec
    show ((hqmem i).choose : ℚ) / (c : ℚ) = q i
    rw [show (((hqmem i).choose : ℤ) : ℚ) = (c : ℚ) * q i from hi]
    field_simp
  · rintro ⟨m, rfl⟩ i
    refine ⟨m i, ?_⟩
    show ((m i : ℤ) : ℚ) = (c : ℚ) * ((m i : ℚ) / (c : ℚ))
    field_simp

/-! ## Diagonal behaviour of the family -/

/-- A carried test vanishes on the rational diagonal off the `c`-divided
rational lattice. -/
theorem IsStandardCarried.rationalDiagonal_eq_zero {c : ℕ}
    {f : (Fin n → RationalFiniteAdele) → ℂ} (hf : IsStandardCarried c f)
    {q : Fin n → ℚ} (hq : q ∉ rationalDividedIntegralVectors n c) :
    f (rationalFiniteAdeleVectorDiagonal n q) = 0 :=
  hf _ fun hmem => hq ((mem_standardDividedLattice_rationalDiagonal_iff c q).mp hmem)

/-- A periodic test is invariant under every rational-diagonal shift by the
`d`-dilated standard rational lattice. -/
theorem IsStandardPeriodic.rationalDiagonal_add {d : ℕ}
    {f : (Fin n → RationalFiniteAdele) → ℂ} (hf : IsStandardPeriodic d f)
    (q : Fin n → ℚ) (m : Fin n → ℤ) :
    f (rationalFiniteAdeleVectorDiagonal n (fun i => q i + (d : ℚ) * (m i : ℚ))) =
      f (rationalFiniteAdeleVectorDiagonal n q) := by
  have hmem : rationalFiniteAdeleVectorDiagonal n (fun i => (m i : ℚ)) ∈
      integralFiniteAdeleVectors n := by
    intro i
    exact (rational_mem_integralFiniteAdeleSubring_iff ((m i : ℚ))).mpr ⟨m i, rfl⟩
  have hsplit : rationalFiniteAdeleVectorDiagonal n (fun i => q i + (d : ℚ) * (m i : ℚ)) =
      rationalFiniteAdeleVectorDiagonal n q +
        d • rationalFiniteAdeleVectorDiagonal n (fun i => (m i : ℚ)) := by
    rw [nsmul_rationalFiniteAdeleVectorDiagonal]
    funext i
    show algebraMap ℚ RationalFiniteAdele (q i + (d : ℚ) * (m i : ℚ)) =
      algebraMap ℚ RationalFiniteAdele (q i) +
        algebraMap ℚ RationalFiniteAdele ((d : ℚ) * (m i : ℚ))
    rw [map_add]
  rw [hsplit]
  exact hf _ _ hmem

/-- Every member of the family with nonzero scales is globally bounded. -/
theorem exists_bound_of_isStandardCarried_isStandardPeriodic
    {c d : ℕ} (hc : c ≠ 0) (hd : d ≠ 0)
    {f : (Fin n → RationalFiniteAdele) → ℂ}
    (hcarried : IsStandardCarried c f) (hperiodic : IsStandardPeriodic d f) :
    ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C :=
  (hcarried.hasCompactSupport hc).exists_bound_of_continuous (hperiodic.continuous hd)

/-! ## Collapse of the rational-diagonal sum -/

theorem support_rationalDiagonal_mul_subset {c : ℕ} (hc : c ≠ 0)
    {f : (Fin n → RationalFiniteAdele) → ℂ} (hf : IsStandardCarried c f)
    (g : (Fin n → ℚ) → ℂ) :
    Function.support (fun q : Fin n → ℚ => g q * f (rationalFiniteAdeleVectorDiagonal n q)) ⊆
      Set.range (rationalScaledIntegerVector (n := n) c) := by
  rw [← rationalDividedIntegralVectors_eq_range hc]
  intro q hq
  by_contra hnot
  refine hq ?_
  show g q * f (rationalFiniteAdeleVectorDiagonal n q) = 0
  rw [hf.rationalDiagonal_eq_zero hnot, mul_zero]

/-- The rational-diagonal sum of a supplied factor against a carried test
converges as soon as the supplied factor is absolutely summable along the
literal `c`-divided lattice.  No Gaussian, theta or Poisson input is used. -/
theorem summable_rationalDiagonal_mul {c d : ℕ} (hc : c ≠ 0) (hd : d ≠ 0)
    {f : (Fin n → RationalFiniteAdele) → ℂ}
    (hcarried : IsStandardCarried c f) (hperiodic : IsStandardPeriodic d f)
    {g : (Fin n → ℚ) → ℂ}
    (hg : Summable fun m : Fin n → ℤ => ‖g (rationalScaledIntegerVector c m)‖) :
    Summable fun q : Fin n → ℚ => g q * f (rationalFiniteAdeleVectorDiagonal n q) := by
  obtain ⟨C, hC⟩ :=
    exists_bound_of_isStandardCarried_isStandardPeriodic hc hd hcarried hperiodic
  refine ((injective_rationalScaledIntegerVector hc).summable_iff ?_).mp ?_
  · intro q hq
    show g q * f (rationalFiniteAdeleVectorDiagonal n q) = 0
    rw [hcarried.rationalDiagonal_eq_zero
      (by rw [rationalDividedIntegralVectors_eq_range hc]; exact hq), mul_zero]
  · refine Summable.of_norm_bounded (hg.mul_right C) ?_
    intro m
    rw [Function.comp_apply, norm_mul]
    exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)

/-- The rational-diagonal sum is literally the scaled-lattice sum. -/
theorem tsum_rationalDiagonal_mul {c : ℕ} (hc : c ≠ 0)
    {f : (Fin n → RationalFiniteAdele) → ℂ} (hcarried : IsStandardCarried c f)
    (g : (Fin n → ℚ) → ℂ) :
    (∑' q : Fin n → ℚ, g q * f (rationalFiniteAdeleVectorDiagonal n q)) =
      ∑' m : Fin n → ℤ, g (rationalScaledIntegerVector c m) *
        f (rationalFiniteAdeleVectorDiagonal n (rationalScaledIntegerVector c m)) :=
  ((injective_rationalScaledIntegerVector hc).tsum_eq
    (support_rationalDiagonal_mul_subset hc hcarried g)).symm

/-! ## The adelic tensor theta sum -/

/-- For the actual real--finite tensor with a family finite factor, the theta
sum over the rational diagonal converges and collapses to the literal
`c`-divided lattice sum.  The real factor stays supplied. -/
theorem summable_rationalAdeleVectorDiagonal_realFiniteTensor
    {c d : ℕ} (hc : c ≠ 0) (hd : d ≠ 0)
    {f : (Fin n → RationalFiniteAdele) → ℂ}
    (hcarried : IsStandardCarried c f) (hperiodic : IsStandardPeriodic d f)
    {realTest : (Fin n → ℝ) → ℂ}
    (hreal : Summable fun m : Fin n → ℤ =>
      ‖realTest (rationalRealVector n (rationalScaledIntegerVector c m))‖) :
    Summable fun q : Fin n → ℚ =>
      realTest (rationalAdeleVectorRealPart n (rationalAdeleVectorDiagonal n q)) *
        f (rationalAdeleVectorFinitePart n (rationalAdeleVectorDiagonal n q)) := by
  simp only [rationalAdeleVectorRealPart_rationalDiagonal,
    rationalAdeleVectorFinitePart_diagonal]
  exact summable_rationalDiagonal_mul hc hd hcarried hperiodic hreal

theorem tsum_rationalAdeleVectorDiagonal_realFiniteTensor {c : ℕ} (hc : c ≠ 0)
    {f : (Fin n → RationalFiniteAdele) → ℂ} (hcarried : IsStandardCarried c f)
    (realTest : (Fin n → ℝ) → ℂ) :
    (∑' q : Fin n → ℚ,
      realTest (rationalAdeleVectorRealPart n (rationalAdeleVectorDiagonal n q)) *
        f (rationalAdeleVectorFinitePart n (rationalAdeleVectorDiagonal n q))) =
      ∑' m : Fin n → ℤ,
        realTest (rationalRealVector n (rationalScaledIntegerVector c m)) *
          f (rationalFiniteAdeleVectorDiagonal n (rationalScaledIntegerVector c m)) := by
  simp only [rationalAdeleVectorRealPart_rationalDiagonal,
    rationalAdeleVectorFinitePart_diagonal]
  exact tsum_rationalDiagonal_mul hc hcarried
    (fun q => realTest (rationalRealVector n q))

/-! ## The finite factor as a periodic lattice weight -/

/-- On the reindexed lattice the finite factor is a weight of period `c * d`.
The theta sum is therefore a `(c*d)^n`-fold combination of shifted lattice sums;
no such Euclidean identity is asserted here. -/
theorem rationalScaledIntegerVector_diagonal_periodic {c d : ℕ} (hc : c ≠ 0)
    {f : (Fin n → RationalFiniteAdele) → ℂ} (hperiodic : IsStandardPeriodic d f)
    (m k : Fin n → ℤ) :
    f (rationalFiniteAdeleVectorDiagonal n
        (rationalScaledIntegerVector c (fun i => m i + ((c * d : ℕ) : ℤ) * k i))) =
      f (rationalFiniteAdeleVectorDiagonal n (rationalScaledIntegerVector c m)) := by
  have hq : ((c : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hc
  have hrw : rationalScaledIntegerVector c (fun i => m i + ((c * d : ℕ) : ℤ) * k i) =
      fun i => rationalScaledIntegerVector c m i + (d : ℚ) * (k i : ℚ) := by
    funext i
    show (((m i + ((c * d : ℕ) : ℤ) * k i : ℤ)) : ℚ) / (c : ℚ) =
      ((m i : ℚ)) / (c : ℚ) + (d : ℚ) * (k i : ℚ)
    push_cast
    field_simp
  rw [hrw]
  exact hperiodic.rationalDiagonal_add _ k

/-! ## The generator output side -/

/-- The generator output is again a family member, so the same collapse applies
to it at its explicit scales.  Both sides of a prospective orbit Poisson
identity are therefore literal lattice sums; the identity itself is not
asserted. -/
theorem summable_rationalDiagonal_mul_finiteWeylUnipotent
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ) {c d : ℕ} (hc : c ≠ 0) (hd : d ≠ 0)
    {f : (Fin n → RationalFiniteAdele) → ℂ}
    (hcarried : IsStandardCarried c f) (hperiodic : IsStandardPeriodic d f)
    {g : (Fin n → ℚ) → ℂ}
    (hg : Summable fun m : Fin n → ℤ =>
      ‖g (rationalScaledIntegerVector (t.den * c * d) m)‖) :
    Summable fun w : Fin n → ℚ =>
      g w * standardFiniteFourier
        (fun x =>
          (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase t x : ℂ) * f x)
        (rationalFiniteAdeleVectorDiagonal n w) :=
  summable_rationalDiagonal_mul (mul_ne_zero (mul_ne_zero t.den_nz hc) hd) hc
    (isStandardCarried_finiteWeylUnipotent L t hcarried hperiodic)
    (isStandardPeriodic_finiteWeylUnipotent L.rationalQuadraticSpaceMatrix t hcarried) hg

theorem tsum_rationalDiagonal_mul_finiteWeylUnipotent
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ) {c d : ℕ} (hc : c ≠ 0) (hd : d ≠ 0)
    {f : (Fin n → RationalFiniteAdele) → ℂ}
    (hcarried : IsStandardCarried c f) (hperiodic : IsStandardPeriodic d f)
    (g : (Fin n → ℚ) → ℂ) :
    (∑' w : Fin n → ℚ, g w * standardFiniteFourier
        (fun x =>
          (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase t x : ℂ) * f x)
        (rationalFiniteAdeleVectorDiagonal n w)) =
      ∑' m : Fin n → ℤ,
        g (rationalScaledIntegerVector (t.den * c * d) m) *
          standardFiniteFourier
            (fun x =>
              (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase t x : ℂ) * f x)
            (rationalFiniteAdeleVectorDiagonal n
              (rationalScaledIntegerVector (t.den * c * d) m)) :=
  tsum_rationalDiagonal_mul (mul_ne_zero (mul_ne_zero t.den_nz hc) hd)
    (isStandardCarried_finiteWeylUnipotent L t hcarried hperiodic) g

end RationalQuadraticSpaceMatrix

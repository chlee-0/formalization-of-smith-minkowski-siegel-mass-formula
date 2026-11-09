import SMSFormula.RationalAdeleVectorPolarGaussianLattice

/-!
# Intrinsic reduction of polar adelic Poisson to Euclidean lattice theta

This file isolates the exact remaining theorem after the full rational-adelic
polar Fourier transform. It defines the standard integral rational vectors
and the intrinsic rational polar-dual lattice

`{q : ℚ^n | C q has integral coordinates}`,

without choosing `C⁻¹` or a lattice representative. The finite adelic
indicators are proved to have exactly these two rational-diagonal supports.
Both rational-adelic sums therefore reindex canonically to intrinsic
Euclidean theta sums, and the desired rational-diagonal polar Poisson theorem
is equivalent to equality of those theta sums.

No Euclidean matrix-lattice Poisson theorem is asserted here. The reduction
shows precisely that this correlated positive-definite Gaussian identity is
the sole remaining additive statement; product Fubini and the existing
one-dimensional theta theorem do not by themselves prove it. No shell,
orbital distribution, or Tamagawa-number assertion is introduced.
-/

noncomputable section

open MeasureTheory Set
open scoped FourierTransform

namespace PositiveDefiniteIntegralLattice

/-- The complete rational diagonal in the native adelic vector carrier. -/
def rationalAdeleVectorDiagonal (d : ℕ) (q : Fin d → ℚ) :
    Fin d → RationalAdele :=
  fun i => algebraMap ℚ RationalAdele (q i)

/-- The real coordinate vector underlying a rational vector. -/
def rationalRealVector (d : ℕ) (q : Fin d → ℚ) : Fin d → ℝ :=
  fun i => (q i : ℝ)

/-- Rational vectors whose coordinates are all integers. -/
def rationalIntegralVectors (d : ℕ) : Set (Fin d → ℚ) :=
  {q | ∀ i, q i ∈ Set.range (algebraMap ℤ ℚ)}

/-- The intrinsic rational `C`-dual of the standard lattice: no inverse matrix
or representative is chosen. -/
def _root_.RationalQuadraticSpaceMatrix.rationalPolarDualVectors
    {n : ℕ} (V : RationalQuadraticSpaceMatrix n) :
    Set (Fin n → ℚ) :=
  {q | ∀ i, V.polarMatrix.mulVec q i ∈ Set.range (algebraMap ℤ ℚ)}

private theorem rationalAdele_algebraMap_fst_vectorPoisson (q : ℚ) :
    (algebraMap ℚ RationalAdele q).1 =
      algebraMap ℚ RationalInfiniteAdele q := by
  exact DFunLike.congr_fun
    (RingHom.ext_rat
      ((RingHom.fst RationalInfiniteAdele RationalFiniteAdele).comp
        (algebraMap ℚ RationalAdele))
      (algebraMap ℚ RationalInfiniteAdele)) q

private theorem rationalAdele_algebraMap_snd_vectorPoisson (q : ℚ) :
    (algebraMap ℚ RationalAdele q).2 =
      algebraMap ℚ RationalFiniteAdele q := by
  exact DFunLike.congr_fun
    (RingHom.ext_rat
      ((RingHom.snd RationalInfiniteAdele RationalFiniteAdele).comp
        (algebraMap ℚ RationalAdele))
      (algebraMap ℚ RationalFiniteAdele)) q

@[simp]
theorem rationalAdeleVectorRealPart_rationalDiagonal
    (d : ℕ) (q : Fin d → ℚ) :
    rationalAdeleVectorRealPart d (rationalAdeleVectorDiagonal d q) =
      rationalRealVector d q := by
  funext i
  change rationalInfiniteAdeleContinuousAddEquivReal
      (algebraMap ℚ RationalAdele (q i)).1 = (q i : ℝ)
  rw [rationalAdele_algebraMap_fst_vectorPoisson,
    rationalInfiniteAdeleContinuousAddEquivReal_algebraMap]
  exact map_ratCast (algebraMap ℚ ℝ) (q i)

@[simp]
theorem rationalAdeleVectorFinitePart_rationalDiagonal
    (d : ℕ) (q : Fin d → ℚ) :
    rationalAdeleVectorFinitePart d (rationalAdeleVectorDiagonal d q) =
      fun i => algebraMap ℚ RationalFiniteAdele (q i) := by
  funext i
  exact rationalAdele_algebraMap_snd_vectorPoisson (q i)

theorem rationalAdeleVectorFinitePart_rationalDiagonal_mem_iff
    (d : ℕ) (q : Fin d → ℚ) :
    rationalAdeleVectorFinitePart d (rationalAdeleVectorDiagonal d q) ∈
        integralFiniteAdeleVectors d ↔
      q ∈ rationalIntegralVectors d := by
  rw [rationalAdeleVectorFinitePart_rationalDiagonal]
  simp only [rationalIntegralVectors, Set.mem_setOf_eq]
  constructor
  · intro h i
    exact (rational_mem_integralFiniteAdeleSubring_iff (q i)).mp (h i)
  · intro h i
    exact (rational_mem_integralFiniteAdeleSubring_iff (q i)).mpr (h i)

theorem rationalAdeleVectorFinitePart_rationalDiagonal_mem_polarDual_iff
    {n : ℕ} (V : RationalQuadraticSpaceMatrix n) (q : Fin n → ℚ) :
    rationalAdeleVectorFinitePart n (rationalAdeleVectorDiagonal n q) ∈
        V.finitePolarDualLattice ↔
      q ∈ V.rationalPolarDualVectors := by
  rw [RationalQuadraticSpaceMatrix.mem_finitePolarDualLattice_iff]
  have hfull := V.fullAdelicPolarMatrix_mulVec_rationalDiagonal q
  have hfin := congrArg (rationalAdeleVectorFinitePart n) hfull
  rw [rationalAdeleVectorFinitePart_fullAdelicPolarMatrix_mulVec] at hfin
  have hfin' :
      V.finiteAdelicPolarMatrix.mulVec
          (rationalAdeleVectorFinitePart n (rationalAdeleVectorDiagonal n q)) =
        rationalAdeleVectorFinitePart n
          (rationalAdeleVectorDiagonal n (V.polarMatrix.mulVec q)) := by
    simpa [rationalAdeleVectorDiagonal] using hfin
  rw [hfin']
  simp only [RationalQuadraticSpaceMatrix.rationalPolarDualVectors,
    Set.mem_setOf_eq]
  rw [rationalAdeleVectorFinitePart_rationalDiagonal]
  constructor
  · intro h i
    exact (rational_mem_integralFiniteAdeleSubring_iff
      (V.polarMatrix.mulVec q i)).mp (h i)
  · intro h i
    exact (rational_mem_integralFiniteAdeleSubring_iff
      (V.polarMatrix.mulVec q i)).mpr (h i)

@[simp]
theorem rationalAdeleVectorPolarGaussianLatticeTest_rationalDiagonal_of_mem
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) (b : ℂ) (q : Fin n → ℚ)
    (hq : q ∈ rationalIntegralVectors n) :
    rationalAdeleVectorPolarGaussianLatticeTest L b
        (rationalAdeleVectorDiagonal n q) =
      polarRealGaussian L b (rationalRealVector n q) := by
  rw [rationalAdeleVectorPolarGaussianLatticeTest,
    rationalAdeleVectorRealPart_rationalDiagonal]
  rw [RationalQuadraticSpaceMatrix.rationalFiniteAdeleVectorIntegralIndicator_of_mem]
  · simp
  · exact (rationalAdeleVectorFinitePart_rationalDiagonal_mem_iff n q).mpr hq

theorem rationalAdeleVectorPolarGaussianLatticeTest_rationalDiagonal_eq_zero_of_not_mem
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) (b : ℂ) (q : Fin n → ℚ)
    (hq : q ∉ rationalIntegralVectors n) :
    rationalAdeleVectorPolarGaussianLatticeTest L b
        (rationalAdeleVectorDiagonal n q) = 0 := by
  rw [rationalAdeleVectorPolarGaussianLatticeTest]
  rw [RationalQuadraticSpaceMatrix.rationalFiniteAdeleVectorIntegralIndicator_of_not_mem]
  · simp
  · exact fun h => hq
      ((rationalAdeleVectorFinitePart_rationalDiagonal_mem_iff n q).mp h)

@[simp]
theorem rationalAdeleVectorPolarGaussianLatticeFourierProduct_rationalDiagonal_of_mem
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) (b : ℂ) (q : Fin n → ℚ)
    (hq : q ∈ L.rationalQuadraticSpaceMatrix.rationalPolarDualVectors) :
    rationalAdeleVectorPolarGaussianLatticeFourierProduct L b
        (rationalAdeleVectorDiagonal n q) =
      polarRealGaussianFourierProduct L b (rationalRealVector n q) := by
  rw [rationalAdeleVectorPolarGaussianLatticeFourierProduct,
    rationalAdeleVectorRealPart_rationalDiagonal]
  rw [RationalQuadraticSpaceMatrix.finitePolarDualLatticeIndicator_of_mem]
  · simp
  · exact
      (rationalAdeleVectorFinitePart_rationalDiagonal_mem_polarDual_iff
        L.rationalQuadraticSpaceMatrix q).mpr hq

theorem rationalAdeleVectorPolarGaussianLatticeFourierProduct_rationalDiagonal_eq_zero_of_not_mem
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) (b : ℂ) (q : Fin n → ℚ)
    (hq : q ∉ L.rationalQuadraticSpaceMatrix.rationalPolarDualVectors) :
    rationalAdeleVectorPolarGaussianLatticeFourierProduct L b
        (rationalAdeleVectorDiagonal n q) = 0 := by
  rw [rationalAdeleVectorPolarGaussianLatticeFourierProduct]
  rw [RationalQuadraticSpaceMatrix.finitePolarDualLatticeIndicator_of_not_mem]
  · simp
  · exact fun h => hq
      ((rationalAdeleVectorFinitePart_rationalDiagonal_mem_polarDual_iff
        L.rationalQuadraticSpaceMatrix q).mp h)

/-! ## The two intrinsic Euclidean theta sums -/

/-- The real polar Gaussian summed over the standard integral rational
lattice. -/
def rationalAdeleVectorPolarStandardTheta
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) (b : ℂ) : ℂ :=
  ∑' q : {q : Fin n → ℚ // q ∈ rationalIntegralVectors n},
    polarRealGaussian L b (rationalRealVector n q.1)

/-- The determinant-normalized real Fourier product summed over the intrinsic
rational polar-dual lattice. -/
def rationalAdeleVectorPolarDualTheta
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) (b : ℂ) : ℂ :=
  ∑' q : {q : Fin n → ℚ //
      q ∈ L.rationalQuadraticSpaceMatrix.rationalPolarDualVectors},
    polarRealGaussianFourierProduct L b (rationalRealVector n q.1)

private theorem support_polarGaussianLatticeTest_rationalDiagonal
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) (b : ℂ) :
    Function.support (fun q : Fin n → ℚ =>
      rationalAdeleVectorPolarGaussianLatticeTest L b
        (rationalAdeleVectorDiagonal n q)) ⊆
      rationalIntegralVectors n := by
  intro q hq
  by_contra hnot
  exact hq
    (rationalAdeleVectorPolarGaussianLatticeTest_rationalDiagonal_eq_zero_of_not_mem
      L b q hnot)

private theorem support_polarGaussianLatticeFourierProduct_rationalDiagonal
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) (b : ℂ) :
    Function.support (fun q : Fin n → ℚ =>
      rationalAdeleVectorPolarGaussianLatticeFourierProduct L b
        (rationalAdeleVectorDiagonal n q)) ⊆
      L.rationalQuadraticSpaceMatrix.rationalPolarDualVectors := by
  intro q hq
  by_contra hnot
  exact hq
    (rationalAdeleVectorPolarGaussianLatticeFourierProduct_rationalDiagonal_eq_zero_of_not_mem
      L b q hnot)

/-- The rational-diagonal adelic test sum is exactly the standard intrinsic
Euclidean theta sum. -/
theorem tsum_polarGaussianLatticeTest_rationalDiagonal_eq_standardTheta
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) (b : ℂ) :
    (∑' q : Fin n → ℚ,
      rationalAdeleVectorPolarGaussianLatticeTest L b
        (rationalAdeleVectorDiagonal n q)) =
      rationalAdeleVectorPolarStandardTheta L b := by
  rw [← Subtype.val_injective.tsum_eq (fun q hq =>
    ⟨⟨q, support_polarGaussianLatticeTest_rationalDiagonal L b hq⟩, rfl⟩)]
  apply tsum_congr
  intro q
  exact rationalAdeleVectorPolarGaussianLatticeTest_rationalDiagonal_of_mem
    L b q.1 q.2

/-- The rational-diagonal Fourier-product sum is exactly the intrinsic dual
Euclidean theta sum. -/
theorem tsum_polarGaussianLatticeFourierProduct_rationalDiagonal_eq_dualTheta
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) (b : ℂ) :
    (∑' q : Fin n → ℚ,
      rationalAdeleVectorPolarGaussianLatticeFourierProduct L b
        (rationalAdeleVectorDiagonal n q)) =
      rationalAdeleVectorPolarDualTheta L b := by
  rw [← Subtype.val_injective.tsum_eq (fun q hq =>
    ⟨⟨q, support_polarGaussianLatticeFourierProduct_rationalDiagonal L b hq⟩,
      rfl⟩)]
  apply tsum_congr
  intro q
  exact
    rationalAdeleVectorPolarGaussianLatticeFourierProduct_rationalDiagonal_of_mem
      L b q.1 q.2

/-- Rational-diagonal polar adelic Poisson summation is equivalent to the
positive-definite Euclidean theta equality for the standard integral rational
lattice and its intrinsic `C`-dual. -/
theorem rationalAdeleVectorPolarGaussianLattice_poisson_iff_euclideanTheta
    {n : ℕ} {b : ℂ} (hb : 0 < b.re) (L : PositiveDefiniteIntegralLattice n) :
    ((∑' q : Fin n → ℚ,
        rationalAdeleVectorPolarGaussianLatticeTest L b
          (rationalAdeleVectorDiagonal n q)) =
      ∑' q : Fin n → ℚ,
        Fourier.fourierIntegral (rationalAdeleCoordinateFourierChar n)
          (rationalAdeleCoordinateAddHaarMeasure n)
          (rationalAdeleVectorPolarGaussianLatticeTest L b)
          (L.rationalQuadraticSpaceMatrix.fullAdelicPolarMatrix.mulVec
            (rationalAdeleVectorDiagonal n q))) ↔
      rationalAdeleVectorPolarStandardTheta L b =
        rationalAdeleVectorPolarDualTheta L b := by
  rw [tsum_polarGaussianLatticeTest_rationalDiagonal_eq_standardTheta]
  have hfourier :
      (fun q : Fin n → ℚ =>
        Fourier.fourierIntegral (rationalAdeleCoordinateFourierChar n)
          (rationalAdeleCoordinateAddHaarMeasure n)
          (rationalAdeleVectorPolarGaussianLatticeTest L b)
          (L.rationalQuadraticSpaceMatrix.fullAdelicPolarMatrix.mulVec
            (rationalAdeleVectorDiagonal n q))) =
      fun q => rationalAdeleVectorPolarGaussianLatticeFourierProduct L b
        (rationalAdeleVectorDiagonal n q) := by
    funext q
    exact rationalAdeleVectorPolar_fourierIntegral_gaussianLattice hb L
      (rationalAdeleVectorDiagonal n q)
  rw [hfourier,
    tsum_polarGaussianLatticeFourierProduct_rationalDiagonal_eq_dualTheta]

end PositiveDefiniteIntegralLattice
/-! ## Exact finite-support identifications -/

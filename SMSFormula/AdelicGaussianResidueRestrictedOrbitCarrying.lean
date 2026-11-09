import SMSFormula.AdelicGaussianResidueRestrictedOrbitImage
import SMSFormula.PadicQuadraticOrbitCarrierResidueData
import SMSFormula.RationalCliffordGeneralSpinHorizontalValueTailResidueCount

/-!
# Discharging the carrying and unimodularity hypotheses of the orbit image

The presentation image of a central-cutoff orbit was identified with the carried fiber set of a
CRT residue set under two supplied local hypotheses. Both are discharged here.

* Unimodularity off a finite set. The presentation matrix `E` and its inverse `F` are
  rational; at a prime not dividing the product `D_P` of all their denominators both are
  `ℤ_p`-integral, so `E_p` preserves integrality in both directions (`F E = 1`).  `D_P` is
  determined by the supplied presentation; no set of places is chosen.
* Carrying.  If the local orbit `O_v ⊆ X_a(ℚ_p)` (block coordinates) is compact, open in the
  block shell and `E_v`-integral, the residue-data existence theorem gives a level `e ≥ 1`
  and residues `R` with `E_v z ∈ T_R ⟺ z ∈ O_v` for every block shell point `z`.  Residue data at
  the places of `S ∪ bad` assemble into a prime-indexed family (the place of a prime is unique).

Hence, under the integral-orbit hypotheses, `D_P`-coprimality off `S ∪ bad` and compact open
integral local orbits, there exist residue data at the primes of `S ∪ bad` whose carried fiber set
is `e_X(O)`.  Only existence is asserted; no level or residue set is chosen.
-/

noncomputable section

open PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix Rat.HeightOneSpectrum Metric
open scoped Matrix

local instance orbitCarryingDecidableEq : DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

theorem mulVec_mem_subring {k l : ℕ} (A : Matrix (Fin k) (Fin l) ℚ_[p])
    (hA : ∀ i j, A i j ∈ PadicInt.subring p) {z : Fin l → ℚ_[p]}
    (hz : ∀ j, z j ∈ PadicInt.subring p) (i : Fin k) : (A *ᵥ z) i ∈ PadicInt.subring p := by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ ↦ Subring.mul_mem _ (hA i j) (hz j)

theorem map_ratMatrix_mem_subring {k l : ℕ} (E : Matrix (Fin k) (Fin l) ℚ)
    (hE : ∀ i j, ¬ p ∣ (E i j).den) (i : Fin k) (j : Fin l) :
    E.map (algebraMap ℚ ℚ_[p]) i j ∈ PadicInt.subring p := by
  rw [Matrix.map_apply, eq_ratCast]
  exact Padic.norm_rat_le_one (hE i j)

/-- A rational matrix with a left inverse, both `p`-integral, preserves `p`-integrality in both
directions. -/
theorem mulVec_mem_subring_iff_of_mul_eq_one {k l : ℕ} (E : Matrix (Fin k) (Fin l) ℚ)
    (F : Matrix (Fin l) (Fin k) ℚ) (hFE : F * E = 1) (hE : ∀ i j, ¬ p ∣ (E i j).den)
    (hF : ∀ i j, ¬ p ∣ (F i j).den) (z : Fin l → ℚ_[p]) :
    (∀ i, (E.map (algebraMap ℚ ℚ_[p]) *ᵥ z) i ∈ PadicInt.subring p) ↔
      ∀ i, z i ∈ PadicInt.subring p := by
  constructor
  · intro h i
    have := mulVec_mem_subring (F.map (algebraMap ℚ ℚ_[p])) (map_ratMatrix_mem_subring F hF) h i
    rwa [Matrix.mulVec_mulVec, ← Matrix.map_mul, hFE,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec] at this
  · intro h i
    exact mulVec_mem_subring _ (map_ratMatrix_mem_subring E hE) h i

variable {N : ℕ}

/-- Raising the level of residue data does not change the restricted integral set. -/
theorem restrictedIntegralVectors_castHom_preimage {e k : ℕ} (hek : e ≤ k)
    (R : Set (Fin N → ZMod (p ^ e))) :
    restrictedIntegralVectors k
        ((fun w : Fin N → ZMod (p ^ k) ↦ fun i ↦ ZMod.castHom (pow_dvd_pow p hek) (ZMod (p ^ e))
          (w i)) ⁻¹' R) = restrictedIntegralVectors e R := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [vectorInclusion_mem_restrictedIntegralVectors_iff, ← castHom_vectorReduction hek]
    exact hz
  · rintro ⟨z, hz, rfl⟩
    rw [vectorInclusion_mem_restrictedIntegralVectors_iff]
    change (fun i ↦ ZMod.castHom (pow_dvd_pow p hek) (ZMod (p ^ e)) (vectorReduction k z i)) ∈ R
    rw [castHom_vectorReduction hek]
    exact hz

end PadicInt

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

variable {n m : ℕ} {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

/-- The product of all denominators of the presentation matrix and its inverse. -/
def presentationDenominator (hx : V.nativeRationalQuadraticForm x ≠ 0) : ℕ :=
  (∏ i, ∏ j, (P.blockToAmbientRationalMatrix hx i j).den) *
    ∏ i, ∏ j, (P.ambientToBlockRationalMatrix hx i j).den

/-- Off the primes of `D_P` the presentation preserves integrality. -/
theorem blockToAmbientBaseChangeIsometryEquiv_mem_subring_iff
    (hx : V.nativeRationalQuadraticForm x ≠ 0) (p : ℕ) [Fact p.Prime]
    (hp : ¬ p ∣ P.presentationDenominator hx) (z : Fin (m + 1) → ℚ_[p]) :
    (∀ i, P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[p] z i ∈ PadicInt.subring p) ↔
      ∀ i, z i ∈ PadicInt.subring p := by
  rw [P.blockToAmbientBaseChangeIsometryEquiv_eq_mulVec hx ℚ_[p]]
  unfold presentationDenominator at hp
  refine PadicInt.mulVec_mem_subring_iff_of_mul_eq_one _ _
    (P.ambientToBlockRationalMatrix_mul_blockToAmbientRationalMatrix hx) (fun i j h ↦ hp ?_)
    (fun i j h ↦ hp ?_) z
  · exact h.trans ((Finset.dvd_prod_of_mem (fun j ↦ (P.blockToAmbientRationalMatrix hx i j).den)
      (Finset.mem_univ j)).trans ((Finset.dvd_prod_of_mem
        (fun i ↦ ∏ j, (P.blockToAmbientRationalMatrix hx i j).den) (Finset.mem_univ i)).trans
          (dvd_mul_right _ _)))
  · exact h.trans ((Finset.dvd_prod_of_mem (fun j ↦ (P.ambientToBlockRationalMatrix hx i j).den)
      (Finset.mem_univ j)).trans ((Finset.dvd_prod_of_mem
        (fun i ↦ ∏ j, (P.ambientToBlockRationalMatrix hx i j).den) (Finset.mem_univ i)).trans
          (dvd_mul_left _ _)))

/-- Local carrying data exist: a compact, open, `E`-integral set `O` of block shell points at `p`
is carried by residue data of some level `e ≥ 1`: `E z ∈ T_R ⟺ z ∈ O`. -/
theorem exists_restrictedIntegralVectors_blockToAmbient_iff
    (hx : V.nativeRationalQuadraticForm x ≠ 0) (p : ℕ) [Fact p.Prime]
    (O : Set (P.lowerSpace.nonisotropicLastQuadraticShell (V.nativeRationalQuadraticForm x) hx
      ℚ_[p]))
    (hOc : IsCompact O) (hOo : IsOpen O)
    (hOint : ∀ z ∈ O, ∀ i, P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[p] z.1 i ∈
      PadicInt.subring p) :
    ∃ e : ℕ, 1 ≤ e ∧ ∃ R : Set (Fin n → ZMod (p ^ e)),
      ∀ z : P.lowerSpace.nonisotropicLastQuadraticShell (V.nativeRationalQuadraticForm x) hx
          ℚ_[p],
        P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[p] z.1 ∈
          PadicInt.restrictedIntegralVectors e R ↔ z ∈ O := by
  let H := P.blockToAmbientShellHomeomorph hx ℚ_[p]
  let Oa : Set (Fin n → ℚ_[p]) := Subtype.val '' (H '' O)
  have hc : IsCompact Oa := (hOc.image H.continuous).image continuous_subtype_val
  obtain ⟨W, hW, hWe⟩ := isOpen_induced_iff.mp (H.isOpenMap _ hOo)
  have hOX : Oa = V.anisotropicRationalAmbientShell x ℚ_[p] ∩ W := by
    change Subtype.val '' (H '' O) = _
    rw [← hWe]
    exact Subtype.image_preimage_coe _ W
  have hint : Oa ⊆ closedBall (0 : Fin n → ℚ_[p]) 1 := by
    rintro _ ⟨w, ⟨z, hz, rfl⟩, rfl⟩
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    exact fun i ↦ hOint z hz i
  obtain ⟨e, R, hR⟩ := PadicInt.exists_restrictedIntegralVectors_inter_eq hc hW hOX hint
  refine ⟨e + 1, Nat.le_add_left 1 e,
    (fun w : Fin n → ZMod (p ^ (e + 1)) ↦ fun i ↦
      ZMod.castHom (pow_dvd_pow p (Nat.le_succ e)) (ZMod (p ^ e)) (w i)) ⁻¹' R, fun z ↦ ?_⟩
  rw [PadicInt.restrictedIntegralVectors_castHom_preimage (Nat.le_succ e)]
  have hHz : P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[p] z.1 = (H z).1 := rfl
  rw [hHz]
  constructor
  · intro h
    have hmem : (H z).1 ∈ Oa := hR ▸ ⟨h, (H z).2⟩
    rw [Subtype.val_injective.mem_set_image, H.injective.mem_set_image] at hmem
    exact hmem
  · intro hz
    have hmem : (H z).1 ∈ Oa := ⟨H z, ⟨z, hz, rfl⟩, rfl⟩
    rw [← hR] at hmem
    exact hmem.1

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

theorem prime_of_mem_placeBlockPrimes {T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)} {p : ℕ}
    (hp : p ∈ placeBlockPrimes T) : p.Prime := by
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hp
  exact (primesEquiv w).2

/-- Prime-indexed residue data from place-indexed data: the place over a prime is unique, so
residue data chosen at the places of `T` assemble into a family indexed by primes. -/
theorem exists_primeIndexed_residueData {n : ℕ} (T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (C : ∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ) (e : ℕ),
      Set (Fin n → ZMod ((primesEquiv v : ℕ) ^ e)) → Prop)
    (hC : ∀ v ∈ T, ∃ e : ℕ, 1 ≤ e ∧ ∃ R, C v e R) :
    ∃ (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin n → ZMod (p ^ e p))),
      ∀ v ∈ T, 1 ≤ e (primesEquiv v) ∧ C v (e (primesEquiv v)) (R (primesEquiv v)) := by
  have hΦ : ∀ p : ℕ, ∃ (e : ℕ) (R : Set (Fin n → ZMod (p ^ e))),
      ∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ) (hv : (primesEquiv v : ℕ) = p), v ∈ T →
        1 ≤ e ∧ C v e (hv ▸ R) := by
    intro p
    by_cases h : ∃ v ∈ T, (primesEquiv v : ℕ) = p
    · obtain ⟨v₀, hv₀T, rfl⟩ := h
      obtain ⟨e, he, R, hR⟩ := hC v₀ hv₀T
      refine ⟨e, R, fun v hv _ ↦ ?_⟩
      have hvv : v = v₀ := primesEquiv.injective (Subtype.ext hv)
      subst hvv
      exact ⟨he, hR⟩
    · exact ⟨0, ∅, fun v hv hvT ↦ (h ⟨v, hvT, hv⟩).elim⟩
  choose e R hR using hΦ
  exact ⟨e, R, fun v hv ↦ hR _ v rfl hv⟩

variable {n m : ℕ} (L : PositiveDefiniteIntegralLattice n) {x : Fin n → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x m) [NeZero m]
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

/-- The orbit image is a carried fiber set, with the carrying and unimodularity hypotheses
discharged: if `S ∪ bad` contains the odd-unimodular bad places and the primes of `D_P`,
`a` is a unit off `S ∪ bad`, and the local orbits `s_v · x_old` (`v ∈ S ∪ bad`) are compact,
open and `E_v`-integral, then there exist residue data of levels `≥ 1` at the primes of `S ∪ bad`
whose carried fiber set is `e_X((cutoff ⊤ cyl(S, s)) · x_old)`. -/
theorem exists_residueData_image_centralCutoffOrbit_eq
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (s : ∀ v : {v // v ∈ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces},
      Subgroup ((P.blockSpace hx).HeightOnePadicCliffordGeneralSpinGroup v.1))
    (hodd : (P.blockSpace hx).cliffordSpinCandidateOddUnimodularBadPlaces ⊆
      S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)
    (haunit : ∀ v, v ∉ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces →
      finiteAdelicUnitHeightOneComponentHom v
          (Units.map (algebraMap ℚ RationalFiniteAdele).toMonoidHom
            (Units.mk0 (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx)) ∈
        padicIntegralUnitsSubgroup (primesEquiv v).1)
    (hden : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
      v ∉ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces →
      ¬ (primesEquiv v : ℕ) ∣ P.presentationDenominator hx)
    (hOc : ∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ)
      (h : v ∈ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces),
      IsCompact ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
        ℚ_[(primesEquiv v).1]) '' (s ⟨v, h⟩ : Set _)))
    (hOo : ∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ)
      (h : v ∈ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces),
      IsOpen ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
        ℚ_[(primesEquiv v).1]) '' (s ⟨v, h⟩ : Set _)))
    (hOint : ∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ)
      (h : v ∈ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces),
      ∀ z ∈ (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
        ℚ_[(primesEquiv v).1]) '' (s ⟨v, h⟩ : Set _), ∀ i,
        P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(primesEquiv v).1] z.1 i ∈
          PadicInt.subring (primesEquiv v).1) :
    ∃ (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin n → ZMod (p ^ e p))),
      (∀ p ∈ placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces),
        p.Prime ∧ 1 ≤ e p) ∧
      (∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ)
        (h : v ∈ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)
        (z : P.lowerSpace.nonisotropicLastQuadraticShell
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ_[(primesEquiv v).1]),
        P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(primesEquiv v).1] z.1 ∈
            PadicInt.restrictedIntegralVectors (e (primesEquiv v)) (R (primesEquiv v)) ↔
          z ∈ (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
            ℚ_[(primesEquiv v).1]) '' (s ⟨v, h⟩ : Set _)) ∧
      haveI : NeZero (localRestrictionLevel (placeBlockPrimes
          (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)) e) :=
        ⟨localRestrictionLevel_ne_zero fun _ hp ↦ prime_of_mem_placeBlockPrimes hp⟩
      (P.blockToAmbientShellHomeomorph hx RationalAdele ''
          ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) ''
            ((P.blockSpace hx).centralCutoffSubgroup ⊤
              ((P.blockSpace hx).cliffordGeneralSpinHorizontalCylinderSubgroup S s) : Set _)) :
          Set (adelicValueFiber L (algebraMap ℚ RationalAdele
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)))) =
        fiberResidueRestrictedSet L _
          (localRestrictionLevel (placeBlockPrimes
            (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)) e)
          (localRestrictionSet (placeBlockPrimes
            (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)) e R) := by
  obtain ⟨e, R, hR⟩ := exists_primeIndexed_residueData (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)
    (fun v e R ↦ ∀ h : v ∈ (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces), ∀ z : P.lowerSpace.nonisotropicLastQuadraticShell
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ_[(primesEquiv v).1],
      P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(primesEquiv v).1] z.1 ∈
          PadicInt.restrictedIntegralVectors e R ↔
        z ∈ (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
          ℚ_[(primesEquiv v).1]) '' (s ⟨v, h⟩ : Set _))
    (fun v hv ↦ by
      obtain ⟨e, he, R, hR⟩ := P.exists_restrictedIntegralVectors_blockToAmbient_iff hx
        (primesEquiv v).1 _ (hOc v hv) (hOo v hv) (hOint v hv)
      exact ⟨e, he, R, fun _ ↦ hR⟩)
  have hPrime : ∀ p ∈ placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces), p.Prime := fun _ hp ↦ prime_of_mem_placeBlockPrimes hp
  refine ⟨e, R, fun p hp ↦ ⟨hPrime p hp, ?_⟩, fun v h z ↦ (hR v h).2 h z, ?_⟩
  · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hp
    exact (hR w hw).1
  · exact image_blockToAmbientShellHomeomorph_centralCutoffOrbit_eq L P hx S s hodd haunit
      (placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)) e R hPrime (mem_placeBlockPrimes_iff (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces))
      (fun v h z ↦ (hR v h).2 h z)
      (fun v hv z ↦ P.blockToAmbientBaseChangeIsometryEquiv_mem_subring_iff hx _ (hden v hv) z)

section Ratio

local instance : MeasurableSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := borel _
local instance : BorelSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := ⟨rfl⟩

variable (hn : 4 < n) {b : ℝ} (hb : 0 < b)
variable (x₀ : adelicValueFiber L (algebraMap ℚ RationalAdele
  (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)))
variable (K : Subgroup L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
variable (hc : IsCompact (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup))
variable (ho : IsOpen (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup))
include hn hc ho

/-- The Riesz ratio at the central-cutoff orbit through an orbit test: under the hypotheses of
`exists_residueData_image_centralCutoffOrbit_eq` and `0 < N(O) < ∞`, there exist residue data at
the primes of `S ∪ bad` whose orbit test `Φ` gives `σ(U)/M_native(U) = c_G · ofReal(d_Φ(a))/N(O)`. -/
theorem exists_residueData_div_nativeShellMeasure_eq_orbitTestDensity
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (s : ∀ v : {v // v ∈ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces},
      Subgroup ((P.blockSpace hx).HeightOnePadicCliffordGeneralSpinGroup v.1))
    (hodd : (P.blockSpace hx).cliffordSpinCandidateOddUnimodularBadPlaces ⊆
      S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)
    (haunit : ∀ v, v ∉ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces →
      finiteAdelicUnitHeightOneComponentHom v
          (Units.map (algebraMap ℚ RationalFiniteAdele).toMonoidHom
            (Units.mk0 (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx)) ∈
        padicIntegralUnitsSubgroup (primesEquiv v).1)
    (hden : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
      v ∉ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces →
      ¬ (primesEquiv v : ℕ) ∣ P.presentationDenominator hx)
    (hOc : ∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ)
      (h : v ∈ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces),
      IsCompact ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
        ℚ_[(primesEquiv v).1]) '' (s ⟨v, h⟩ : Set _)))
    (hOo : ∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ)
      (h : v ∈ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces),
      IsOpen ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
        ℚ_[(primesEquiv v).1]) '' (s ⟨v, h⟩ : Set _)))
    (hOint : ∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ)
      (h : v ∈ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces),
      ∀ z ∈ (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
        ℚ_[(primesEquiv v).1]) '' (s ⟨v, h⟩ : Set _), ∀ i,
        P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(primesEquiv v).1] z.1 i ∈
          PadicInt.subring (primesEquiv v).1)
    (h0 : P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
        ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) ''
          ((P.blockSpace hx).centralCutoffSubgroup ⊤
            ((P.blockSpace hx).cliffordGeneralSpinHorizontalCylinderSubgroup S s) : Set _)) ≠ 0)
    (htop : P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
        ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) ''
          ((P.blockSpace hx).centralCutoffSubgroup ⊤
            ((P.blockSpace hx).cliffordGeneralSpinHorizontalCylinderSubgroup S s) : Set _)) ≠ ⊤) :
    ∃ (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin n → ZMod (p ^ e p))),
      (∀ p ∈ placeBlockPrimes
        (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces), p.Prime ∧ 1 ≤ e p) ∧
      haveI : NeZero (localRestrictionLevel (placeBlockPrimes
        (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)) e) :=
        ⟨localRestrictionLevel_ne_zero fun _ hp ↦ prime_of_mem_placeBlockPrimes hp⟩
      let a := algebraMap ℚ RationalAdele
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)
      let σ := gaussianFiberMeasure L hn hb a
      let M := nativeShellMeasureOnValueFiber L P hx
      let U := (fun g ↦ g • x₀) ''
        (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
      σ U / M U =
        (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx : ENNReal) *
          (ENNReal.ofReal (L.rationalQuadraticSpaceMatrix.realValueDensity
              (gaussianResidueRestrictedUnit L b a (localRestrictionLevel (placeBlockPrimes
        (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)) e)
                (localRestrictionSet (placeBlockPrimes
        (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)) e R)).val a) /
            P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
              (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
              ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace
                (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) ''
                ((P.blockSpace hx).centralCutoffSubgroup ⊤
                  ((P.blockSpace hx).cliffordGeneralSpinHorizontalCylinderSubgroup S s) :
                    Set _))) := by
  obtain ⟨e, R, he, -, hO⟩ := exists_residueData_image_centralCutoffOrbit_eq L P hx S s hodd haunit
    hden hOc hOo hOint
  haveI : NeZero (localRestrictionLevel (placeBlockPrimes
        (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)) e) :=
    ⟨localRestrictionLevel_ne_zero fun _ hp ↦ prime_of_mem_placeBlockPrimes hp⟩
  exact ⟨e, R, he, div_nativeShellMeasure_eq_scalar_mul_orbitTestDensity_div L P hx hn hb x₀ K hc ho
    _ _ _ hO h0 htop⟩

end Ratio

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

import SMSFormula.AdelicGaussianNativeShellOrbitRatio
import SMSFormula.RationalCliffordGeneralSpinFullAdelicCentralCutoffOrbit
import SMSFormula.RationalAdeleFiniteResidueLocalComponent
import SMSFormula.RationalQuadraticIsometryGeneralSpinHaarModulus
import SMSFormula.AdelicGaussianResidueRestrictedReplacement

/-!
# The presentation image of a central-cutoff orbit is a carried fiber set

For a supplied compatible presentation `P` of the lattice form at the anisotropic rational
vector `x`, the block-to-ambient map `e_X` is, over every commutative `ℚ`-algebra, the matrix
of the rational isometry; hence it commutes with every `ℚ`-algebra map, in particular with the
real/finite projections and the height-one evaluations.

Let `O = K · x_old` be the orbit of the central cutoff with full real `SO` and the
horizontal cylinder over supplied local subgroups `s_v` (`v ∈ S ∪ bad`).  Suppose

* `S ∪ bad` contains the odd-unimodular bad places and `a` is a unit off `S ∪ bad`
  (the hypotheses of the integral-orbit description);
* off `S ∪ bad` the presentation matrix preserves integrality (supplied);
* the supplied residue data `(P, e, R_p)` live exactly at the primes of `S ∪ bad` and carry the
  local orbits: for a block shell point `z` at `v`, `E_v z ∈ T_{R_{p_v}} ⟺ z ∈ s_v · x_old`.

Then `e_X(O)` is the carried fiber set `{x ∈ X_a : x_f ∈ U_R}` of the CRT product `R`.  Together
with the Riesz ratio at a block-shell set and the Riesz evaluation of carried fiber sets,

`σ(U)/M_native(U) = c_G · ofReal(d_Φ(a)) / N(O)`

for the orbit test `Φ` of `R`.  The existence of carrying residue data is the
`exists_restrictedIntegralVectors_inter_eq`; nothing is chosen here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix Rat.HeightOneSpectrum
open scoped Matrix ENNReal

local instance orbitImageDecidableEq : DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

variable {n m : ℕ} {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

/-- Over every commutative `ℚ`-algebra the scalar-extended presentation is multiplication by the
rational block-to-ambient matrix. -/
theorem blockToAmbientBaseChangeIsometryEquiv_eq_mulVec
    (hx : V.nativeRationalQuadraticForm x ≠ 0) (A : Type*) [CommRing A] [Algebra ℚ A]
    (y : Fin (m + 1) → A) :
    P.blockToAmbientBaseChangeIsometryEquiv hx A y =
      (P.blockToAmbientRationalMatrix hx).map (algebraMap ℚ A) *ᵥ y := by
  classical
  let L := (P.blockToAmbientBaseChangeIsometryEquiv hx A).toLinearEquiv.toLinearMap
  let R := Matrix.toLin' ((P.blockToAmbientRationalMatrix hx).map (algebraMap ℚ A))
  have hLR : L = R := by
    apply (Pi.basisFun A (Fin (m + 1))).ext
    intro i
    have hb : (Pi.basisFun A (Fin (m + 1))) i =
        fun j ↦ algebraMap ℚ A ((Pi.basisFun ℚ (Fin (m + 1))) i j) := by
      ext j
      by_cases hij : i = j <;> simp [Pi.basisFun_apply, hij]
    change P.blockToAmbientBaseChangeIsometryEquiv hx A ((Pi.basisFun A (Fin (m + 1))) i) =
      (P.blockToAmbientRationalMatrix hx).map (algebraMap ℚ A) *ᵥ
        ((Pi.basisFun A (Fin (m + 1))) i)
    rw [hb, P.blockToAmbientBaseChangeIsometryEquiv_rational hx A]
    ext j
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, blockToAmbientRationalMatrix,
      LinearMap.toMatrix'_apply]
    simp [Pi.single_apply]
  change L y = R y
  rw [hLR]

/-- The presentation commutes with every `ℚ`-algebra map. -/
theorem map_blockToAmbientBaseChangeIsometryEquiv (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {A B : Type*} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B] (f : A →ₐ[ℚ] B)
    (y : Fin (m + 1) → A) :
    (fun i ↦ f (P.blockToAmbientBaseChangeIsometryEquiv hx A y i)) =
      P.blockToAmbientBaseChangeIsometryEquiv hx B (fun i ↦ f (y i)) := by
  rw [P.blockToAmbientBaseChangeIsometryEquiv_eq_mulVec hx A,
    P.blockToAmbientBaseChangeIsometryEquiv_eq_mulVec hx B]
  funext i
  change (f : A →+* B) _ = _
  rw [RingHom.map_mulVec (f : A →+* B), Matrix.map_map]
  congr 2
  funext q
  exact f.commutes q

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

namespace PadicInt

variable {p : ℕ} [Fact p.Prime] {N : ℕ}

/-- Restricted integral vectors are integral. -/
theorem mem_subring_of_mem_restrictedIntegralVectors {e : ℕ} {R : Set (Fin N → ZMod (p ^ e))}
    {w : Fin N → ℚ_[p]} (hw : w ∈ restrictedIntegralVectors e R) (i : Fin N) :
    w i ∈ PadicInt.subring p := by
  obtain ⟨z, -, rfl⟩ := hw
  exact PadicInt.norm_le_one (z i)

end PadicInt

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

variable {n m : ℕ} (L : PositiveDefiniteIntegralLattice n) {x : Fin n → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x m) [NeZero m]
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

/-- Integrality of a finite-adelic vector, read through the height-one evaluations. -/
theorem mem_integralFiniteAdeleVectors_iff_heightOne (w : Fin n → RationalFiniteAdele) :
    w ∈ integralFiniteAdeleVectors n ↔
      ∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ) (i : Fin n),
        finiteAdelicCliffordGeneralSpinHeightOneAlgHom v (w i) ∈
          PadicInt.subring (primesEquiv v).1 := by
  rw [mem_integralFiniteAdeleVectors_iff]
  constructor
  · intro h v i
    exact (mem_adicCompletionIntegers_iff_padic v _).mp (h i v)
  · intro h i v
    exact (mem_adicCompletionIntegers_iff_padic v _).mpr (h v i)

set_option backward.isDefEq.respectTransparency false in
/-- The presentation image of a central-cutoff orbit is the carried fiber set, pointwise. -/
theorem blockToAmbientShellHomeomorph_mem_fiberResidueRestrictedSet_iff
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
    (Pr : Finset ℕ) (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin n → ZMod (p ^ e p)))
    (hPr : ∀ p ∈ Pr, p.Prime)
    (hPrS : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ, (primesEquiv v : ℕ) ∈ Pr ↔
      v ∈ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)
    (hcarry : ∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ)
      (h : v ∈ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)
      (z : P.lowerSpace.nonisotropicLastQuadraticShell
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ_[(primesEquiv v).1]),
      P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(primesEquiv v).1] z.1 ∈
          PadicInt.restrictedIntegralVectors (e (primesEquiv v)) (R (primesEquiv v)) ↔
        z ∈ (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
          ℚ_[(primesEquiv v).1]) '' (s ⟨v, h⟩ : Set _))
    (hunimod : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
      v ∉ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces →
      ∀ z : Fin (m + 1) → ℚ_[(primesEquiv v).1],
        (∀ i, P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(primesEquiv v).1] z i ∈
          PadicInt.subring (primesEquiv v).1) ↔ ∀ i, z i ∈ PadicInt.subring (primesEquiv v).1)
    (y : P.lowerSpace.nonisotropicLastQuadraticShell
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) :
    haveI : NeZero (localRestrictionLevel Pr e) := ⟨localRestrictionLevel_ne_zero hPr⟩
    ((P.blockToAmbientShellHomeomorph hx RationalAdele y : adelicValueFiber L
        (algebraMap ℚ RationalAdele (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x))) ∈
        fiberResidueRestrictedSet L _ (localRestrictionLevel Pr e) (localRestrictionSet Pr e R)) ↔
      y ∈ (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) ''
        ((P.blockSpace hx).centralCutoffSubgroup ⊤
          ((P.blockSpace hx).cliffordGeneralSpinHorizontalCylinderSubgroup S s) : Set _) := by
  haveI : NeZero (localRestrictionLevel Pr e) := ⟨localRestrictionLevel_ne_zero hPr⟩
  set a := L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x with ha_def
  rw [mem_fiberResidueRestrictedSet_localRestriction_iff L _ Pr e R hPr,
    P.lowerSpace.mem_image_shellOrbit_centralCutoffSubgroup_top_iff a hx,
    P.lowerSpace.mem_image_shellOrbit_cylinderSubgroup_iff_integral a hx S s hodd haunit]
  -- the local block components and the local ambient components
  let z : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
      P.lowerSpace.nonisotropicLastQuadraticShell a hx ℚ_[(primesEquiv v).1] := fun v ↦
    P.lowerSpace.nonisotropicLastQuadraticShellMap a hx
      (finiteAdelicCliffordGeneralSpinHeightOneAlgHom v)
      (P.lowerSpace.nonisotropicLastQuadraticShellMap a hx
        fullAdelicCliffordGeneralSpinFiniteAlgHom y)
  have hamb : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
      (fun i ↦ adicCompletion.padicEquiv v (rationalAdeleVectorFinitePart n
        (P.blockToAmbientShellHomeomorph hx RationalAdele y).1 i v)) =
        P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(primesEquiv v).1] (z v).1 := by
    intro v
    exact P.map_blockToAmbientBaseChangeIsometryEquiv hx
      ((finiteAdelicCliffordGeneralSpinHeightOneAlgHom v).comp
        fullAdelicCliffordGeneralSpinFiniteAlgHom) y.1
  have hint : rationalAdeleVectorFinitePart n (P.blockToAmbientShellHomeomorph hx RationalAdele y).1
      ∈ integralFiniteAdeleVectors n ↔ ∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ) (i : Fin n),
        P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(primesEquiv v).1] (z v).1 i ∈
          PadicInt.subring (primesEquiv v).1 := by
    rw [mem_integralFiniteAdeleVectors_iff_heightOne]
    refine forall_congr' fun v ↦ ?_
    rw [← hamb v]
    rfl
  constructor
  · rintro ⟨hI, hT⟩ v
    have hI' := hint.mp hI
    refine ⟨fun h ↦ (hcarry v h (z v)).mp ?_, fun hv ↦ (hunimod v hv (z v).1).mp (hI' v)⟩
    have hTv := hT v ((hPrS v).mpr h)
    rwa [hamb v] at hTv
  · intro hO
    refine ⟨hint.mpr fun v ↦ ?_, fun v hv ↦ ?_⟩
    · by_cases h : v ∈ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces
      · exact fun i ↦ PadicInt.mem_subring_of_mem_restrictedIntegralVectors
          ((hcarry v h (z v)).mpr ((hO v).1 h)) i
      · exact (hunimod v h (z v).1).mpr ((hO v).2 h)
    · rw [hamb v]
      exact (hcarry v ((hPrS v).mp hv) (z v)).mpr ((hO v).1 ((hPrS v).mp hv))

set_option backward.isDefEq.respectTransparency false in
/-- The presentation image of a central-cutoff orbit is the carried fiber set:
`e_X(K · x_old) = {x ∈ X_a : x_f ∈ U_R}`. -/
theorem image_blockToAmbientShellHomeomorph_centralCutoffOrbit_eq
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
    (Pr : Finset ℕ) (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin n → ZMod (p ^ e p)))
    (hPr : ∀ p ∈ Pr, p.Prime)
    (hPrS : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ, (primesEquiv v : ℕ) ∈ Pr ↔
      v ∈ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)
    (hcarry : ∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ)
      (h : v ∈ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)
      (z : P.lowerSpace.nonisotropicLastQuadraticShell
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ_[(primesEquiv v).1]),
      P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(primesEquiv v).1] z.1 ∈
          PadicInt.restrictedIntegralVectors (e (primesEquiv v)) (R (primesEquiv v)) ↔
        z ∈ (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
          ℚ_[(primesEquiv v).1]) '' (s ⟨v, h⟩ : Set _))
    (hunimod : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
      v ∉ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces →
      ∀ z : Fin (m + 1) → ℚ_[(primesEquiv v).1],
        (∀ i, P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(primesEquiv v).1] z i ∈
          PadicInt.subring (primesEquiv v).1) ↔ ∀ i, z i ∈ PadicInt.subring (primesEquiv v).1) :
    haveI : NeZero (localRestrictionLevel Pr e) := ⟨localRestrictionLevel_ne_zero hPr⟩
    (P.blockToAmbientShellHomeomorph hx RationalAdele ''
        ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) ''
          ((P.blockSpace hx).centralCutoffSubgroup ⊤
            ((P.blockSpace hx).cliffordGeneralSpinHorizontalCylinderSubgroup S s) : Set _)) :
        Set (adelicValueFiber L (algebraMap ℚ RationalAdele
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)))) =
      fiberResidueRestrictedSet L _ (localRestrictionLevel Pr e) (localRestrictionSet Pr e R) := by
  haveI : NeZero (localRestrictionLevel Pr e) := ⟨localRestrictionLevel_ne_zero hPr⟩
  ext w
  obtain ⟨y, rfl⟩ := (P.blockToAmbientShellHomeomorph hx RationalAdele).surjective w
  rw [(P.blockToAmbientShellHomeomorph hx RationalAdele).injective.mem_set_image]
  exact (blockToAmbientShellHomeomorph_mem_fiberResidueRestrictedSet_iff L P hx S s hodd haunit
    Pr e R hPr hPrS hcarry hunimod y).symm

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

/-- The Riesz ratio through the orbit test: if the presentation image of a block-shell set `O`
with `0 < N(O) < ∞` is the carried fiber set of `U_R`, then
`σ(U)/M_native(U) = c_G · ofReal(d_Φ(a)) / N(O)` for the orbit test `Φ` of `R`. -/
theorem div_nativeShellMeasure_eq_scalar_mul_orbitTestDensity_div
    (N₀ : ℕ) [NeZero N₀] (R : Set (Fin n → ZMod N₀))
    (O : Set (P.lowerSpace.nonisotropicLastQuadraticShell
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele))
    (hO : (P.blockToAmbientShellHomeomorph hx RationalAdele '' O : Set (adelicValueFiber L
        (algebraMap ℚ RationalAdele (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x))))
      = fiberResidueRestrictedSet L _ N₀ R)
    (h0 : P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx O ≠ 0)
    (htop : P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx O ≠ ⊤) :
    let a := algebraMap ℚ RationalAdele (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)
    let σ := gaussianFiberMeasure L hn hb a
    let M := nativeShellMeasureOnValueFiber L P hx
    let U := (fun g ↦ g • x₀) ''
      (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
    σ U / M U =
      (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0∞) *
        (ENNReal.ofReal (L.rationalQuadraticSpaceMatrix.realValueDensity
            (gaussianResidueRestrictedUnit L b a N₀ R).val a) /
          P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx O) := by
  intro a σ M U
  have h := div_nativeShellMeasure_eq_scalar_mul_div_blockImage L P hx hn hb x₀ K hc ho O h0 htop
  simp only at h
  rw [h, hO, gaussianFiberMeasure_fiberResidueRestrictedSet]

/-- The Riesz ratio through the replacement lemma: at a rational-integer value
`M`, if the presentation image of `O` is the carried fiber set of the CRT product `R` of supplied
local residue data whose counts are eventually in the ratio `gR_p : gF_p`, then
`σ(U)/M_native(U) = c_G · ((∏ gR/∏ gF) · σ(X_a ∩ {x_f integral})) / N(O)`. -/
theorem div_nativeShellMeasure_eq_scalar_mul_localRatio_mul_div
    (M : ℤ) (hM : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x = ((M : ℤ) : ℚ))
    (Pr : Finset ℕ) (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin n → ZMod (p ^ e p)))
    (hPr : ∀ p ∈ Pr, p.Prime ∧ 1 ≤ e p) (gF gR : ℕ → ℝ≥0∞)
    (hgF0 : ∀ p ∈ Pr, gF p ≠ 0) (hgFt : ∀ p ∈ Pr, gF p ≠ ⊤)
    (hloc : ∀ p ∈ Pr, ∀ᶠ v : ℕ in Filter.atTop,
      (L.restrictedResidueCount M Pr e R (p ^ v) : ℝ≥0∞) * gF p =
        (L.fullResidueCount M (p ^ v) : ℝ≥0∞) * gR p)
    (hFne : ∀ p ∈ Pr, ∀ᶠ v : ℕ in Filter.atTop, L.fullResidueCount M (p ^ v) ≠ 0)
    (O : Set (P.lowerSpace.nonisotropicLastQuadraticShell
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele))
    (hO : haveI : NeZero (localRestrictionLevel Pr e) :=
        ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hPr p hp).1⟩
      (P.blockToAmbientShellHomeomorph hx RationalAdele '' O : Set (adelicValueFiber L
        (algebraMap ℚ RationalAdele (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x))))
      = fiberResidueRestrictedSet L _ (localRestrictionLevel Pr e) (localRestrictionSet Pr e R))
    (h0 : P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx O ≠ 0)
    (htop : P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx O ≠ ⊤) :
    let a := algebraMap ℚ RationalAdele (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)
    let σ := gaussianFiberMeasure L hn hb a
    let Mn := nativeShellMeasureOnValueFiber L P hx
    let U := (fun g ↦ g • x₀) ''
      (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
    σ U / Mn U =
      (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0∞) *
        (((∏ p ∈ Pr, gR p) / ∏ p ∈ Pr, gF p) * σ (fiberDividedCarrier L a 1) /
          P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx O) := by
  intro a σ Mn U
  haveI : NeZero (localRestrictionLevel Pr e) :=
    ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hPr p hp).1⟩
  have h := div_nativeShellMeasure_eq_scalar_mul_div_blockImage L P hx hn hb x₀ K hc ho O h0 htop
  simp only at h
  have ha2 : a.2 = algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ) := by
    change (algebraMap ℚ RationalAdele (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)).2
      = _
    rw [hM]
    rfl
  rw [h, hO, gaussianFiberMeasure_fiberResidueRestrictedSet_localRestriction L hn hb a M ha2 Pr e R
    hPr gF gR hgF0 hgFt hloc hFne]

end Ratio

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

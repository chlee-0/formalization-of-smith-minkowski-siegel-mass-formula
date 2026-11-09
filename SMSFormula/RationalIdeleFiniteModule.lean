import SMSFormula.RationalCliffordGeneralSpinLatticeAdelicSimilitudeExactness
import SMSFormula.RationalPadicNormProductFormula

/-!
# The finite rational idele module

For a finite idele, only finitely many height-one components fail to be
p-adic units.  The product of the local p-adic norms over that literal support
is therefore well-defined.  This file packages the finite product and proves
its multiplicativity; it is the finite factor in the logarithmic character
used by the crossed `GSpin` cutoff.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped BigOperators ENNReal NNReal RestrictedProduct

namespace RationalQuadraticSpaceMatrix

local instance rationalIdeleFiniteModuleDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) := Classical.decEq _

local instance rationalIdeleFiniteModulePrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- The finite set of places where a finite idele or its inverse is not
integral. -/
def finiteIdeleNormSupport (a : RationalFiniteAdeleˣ) :
    Finset (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  finiteAdeleNonintegralPlaces (a : RationalFiniteAdele) ∪
    finiteAdeleNonintegralPlaces ((a⁻¹ : RationalFiniteAdeleˣ) : RationalFiniteAdele)

theorem not_mem_finiteIdeleNormSupport_iff
    (a : RationalFiniteAdeleˣ) (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    v ∉ finiteIdeleNormSupport a ↔
      (a : RationalFiniteAdele) v ∈ v.adicCompletionIntegers ℚ ∧
        ((a⁻¹ : RationalFiniteAdeleˣ) : RationalFiniteAdele) v ∈
          v.adicCompletionIntegers ℚ := by
  simp [finiteIdeleNormSupport, mem_finiteAdeleNonintegralPlaces_iff]

/-- A finite idele component has p-adic norm one outside its literal norm
support. -/
theorem nnnorm_finiteAdelicUnitHeightOneComponent_eq_one_of_not_mem
    (a : RationalFiniteAdeleˣ) (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∉ finiteIdeleNormSupport a) :
    ‖(finiteAdelicUnitHeightOneComponentHom v a :
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])‖₊ = 1 := by
  have hv' := (not_mem_finiteIdeleNormSupport_iff a v).1 hv
  have ha : finiteAdelicUnitHeightOneComponentHom v a ∈
      padicIntegralUnitsSubgroup (Rat.HeightOneSpectrum.primesEquiv v).1 := by
    rw [mem_padicIntegralUnitsSubgroup_iff]
    constructor
    · exact (mem_adicCompletionIntegers_iff_padic v _).1 hv'.1
    · exact (mem_adicCompletionIntegers_iff_padic v _).1 hv'.2
  let z : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ :=
    PositiveDefiniteIntegralLattice.padicIntUnitOfPadicIntegralUnit
      (Rat.HeightOneSpectrum.primesEquiv v).1
      (finiteAdelicUnitHeightOneComponentHom v a) ha
  apply NNReal.eq
  change ‖(finiteAdelicUnitHeightOneComponentHom v a :
    ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])‖ = (1 : ℝ)
  rw [← PositiveDefiniteIntegralLattice.coe_padicIntUnitOfPadicIntegralUnit
    (Rat.HeightOneSpectrum.primesEquiv v).1
    (finiteAdelicUnitHeightOneComponentHom v a) ha]
  exact PadicInt.norm_units z

/-- The finite idelic module as the product of local p-adic norms over the
literal finite support. -/
def finiteIdeleModuleNNReal (a : RationalFiniteAdeleˣ) : ℝ≥0 :=
  ∏ v ∈ finiteIdeleNormSupport a,
    ‖(finiteAdelicUnitHeightOneComponentHom v a :
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])‖₊

/-- The finite module can be evaluated over any larger finite set. -/
theorem finiteIdeleModuleNNReal_eq_prod_of_subset
    (a : RationalFiniteAdeleˣ)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hS : finiteIdeleNormSupport a ⊆ S) :
    finiteIdeleModuleNNReal a =
      ∏ v ∈ S, ‖(finiteAdelicUnitHeightOneComponentHom v a :
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])‖₊ := by
  unfold finiteIdeleModuleNNReal
  apply Finset.prod_subset hS
  intro v hvS hv
  exact nnnorm_finiteAdelicUnitHeightOneComponent_eq_one_of_not_mem a v hv

/-- The finite module can also be evaluated over a finite set outside which
all local norms are one, without first comparing literal supports. -/
theorem finiteIdeleModuleNNReal_eq_prod_of_eq_one_outside
    (a : RationalFiniteAdeleˣ)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hS : ∀ v, v ∉ S →
      ‖(finiteAdelicUnitHeightOneComponentHom v a :
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])‖₊ = 1) :
    finiteIdeleModuleNNReal a =
      ∏ v ∈ S, ‖(finiteAdelicUnitHeightOneComponentHom v a :
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])‖₊ := by
  let U := finiteIdeleNormSupport a ∪ S
  rw [finiteIdeleModuleNNReal_eq_prod_of_subset a U Finset.subset_union_left]
  apply (Finset.prod_subset Finset.subset_union_right ?_).symm
  intro v hvU hvSnot
  exact hS v hvSnot

/-- The support of a product is contained in the union of the two supports. -/
theorem finiteIdeleNormSupport_mul_subset
    (a b : RationalFiniteAdeleˣ) :
    finiteIdeleNormSupport (a * b) ⊆
      finiteIdeleNormSupport a ∪ finiteIdeleNormSupport b := by
  intro v hv
  by_contra hvUnion
  have hvUnion' : v ∉ finiteIdeleNormSupport a ∧
      v ∉ finiteIdeleNormSupport b := by simpa using hvUnion
  have hva : v ∉ finiteIdeleNormSupport a := hvUnion'.1
  have hvb : v ∉ finiteIdeleNormSupport b := hvUnion'.2
  have ha := (not_mem_finiteIdeleNormSupport_iff a v).1 hva
  have hb := (not_mem_finiteIdeleNormSupport_iff b v).1 hvb
  have hnot : v ∉ finiteIdeleNormSupport (a * b) := by
    rw [not_mem_finiteIdeleNormSupport_iff]
    constructor
    · exact (v.adicCompletionIntegers ℚ).mul_mem _ _ ha.1 hb.1
    · change (((b⁻¹ * a⁻¹ : RationalFiniteAdeleˣ) : RationalFiniteAdele) v) ∈
        v.adicCompletionIntegers ℚ
      exact (v.adicCompletionIntegers ℚ).mul_mem _ _ hb.2 ha.2
  exact hnot hv

/-- The finite idelic module is multiplicative. -/
theorem finiteIdeleModuleNNReal_mul (a b : RationalFiniteAdeleˣ) :
    finiteIdeleModuleNNReal (a * b) =
      finiteIdeleModuleNNReal a * finiteIdeleModuleNNReal b := by
  let S := finiteIdeleNormSupport a ∪ finiteIdeleNormSupport b
  rw [finiteIdeleModuleNNReal_eq_prod_of_subset (a * b) S
      (finiteIdeleNormSupport_mul_subset a b),
    finiteIdeleModuleNNReal_eq_prod_of_subset a S (Finset.subset_union_left),
    finiteIdeleModuleNNReal_eq_prod_of_subset b S (Finset.subset_union_right)]
  simp_rw [map_mul, Units.val_mul, nnnorm_mul]
  exact Finset.prod_mul_distrib

theorem finiteIdeleModuleNNReal_one : finiteIdeleModuleNNReal 1 = 1 := by
  unfold finiteIdeleModuleNNReal
  rw [show finiteIdeleNormSupport 1 = ∅ by
    ext v
    constructor
    · intro hv
      exact False.elim ((not_mem_finiteIdeleNormSupport_iff 1 v).2
        ⟨(v.adicCompletionIntegers ℚ).one_mem,
          (v.adicCompletionIntegers ℚ).one_mem⟩ hv)
    · intro hv
      simp at hv]
  simp

theorem finiteIdeleModuleNNReal_ne_zero (a : RationalFiniteAdeleˣ) :
    finiteIdeleModuleNNReal a ≠ 0 := by
  unfold finiteIdeleModuleNNReal
  apply Finset.prod_ne_zero_iff.mpr
  intro v hv
  rw [ne_eq, nnnorm_eq_zero]
  exact Units.ne_zero _

/-- The finite idelic module as a multiplicative homomorphism to positive
nonnegative-real units. -/
def finiteIdeleModuleHom : RationalFiniteAdeleˣ →* ℝ≥0ˣ where
  toFun a := Units.mk0 (finiteIdeleModuleNNReal a)
    (finiteIdeleModuleNNReal_ne_zero a)
  map_one' := by
    apply Units.ext
    exact finiteIdeleModuleNNReal_one
  map_mul' a b := by
    apply Units.ext
    exact finiteIdeleModuleNNReal_mul a b

@[simp]
theorem coe_finiteIdeleModuleHom (a : RationalFiniteAdeleˣ) :
    (finiteIdeleModuleHom a : ℝ≥0) = finiteIdeleModuleNNReal a :=
  rfl

/-! ## Rational diagonal product formula -/

/-- Rational units embedded diagonally in the finite ideles. -/
def rationalUnitFiniteAdelicDiagonalHom : ℚˣ →* RationalFiniteAdeleˣ :=
  Units.map (algebraMap ℚ RationalFiniteAdele).toMonoidHom

/-- The height-one places corresponding to the numerator/denominator prime
support of a rational scalar. -/
def rationalPadicNormSupportPlaces (q : ℚ) :
    Finset (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  (Rat.padicNormPrimeSupport q).map
    Rat.HeightOneSpectrum.primesEquiv.symm.toEmbedding

/-- The NNReal p-adic norm at a prime subtype, with primality installed from
the subtype proof. -/
def rationalPadicNormNNRealAtPrime (q : ℚ)
    (p : {p : ℕ // Nat.Prime p}) : ℝ≥0 :=
  letI : Fact (Nat.Prime p.1) := ⟨p.2⟩
  ‖algebraMap ℚ ℚ_[p.1] q‖₊

theorem nnnorm_finiteAdelicUnitHeightOneComponent_rationalUnitDiagonal
    (q : ℚˣ) (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    ‖(finiteAdelicUnitHeightOneComponentHom v
        (rationalUnitFiniteAdelicDiagonalHom q) :
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])‖₊ =
      rationalPadicNormNNRealAtPrime (q : ℚ)
        (Rat.HeightOneSpectrum.primesEquiv v) := by
  rw [show finiteAdelicUnitHeightOneComponentHom v
      (rationalUnitFiniteAdelicDiagonalHom q) =
      finiteAdelicCliffordGeneralSpinHeightOneAlgHom v
        (algebraMap ℚ RationalFiniteAdele (q : ℚ)) by rfl]
  rw [(finiteAdelicCliffordGeneralSpinHeightOneAlgHom v).commutes]
  rfl

theorem finiteIdeleModuleNNReal_rationalUnitDiagonal
    (q : ℚˣ) :
    finiteIdeleModuleNNReal (rationalUnitFiniteAdelicDiagonalHom q) =
      ∏ p ∈ Rat.padicNormPrimeSupport (q : ℚ),
        rationalPadicNormNNRealAtPrime (q : ℚ) p := by
  rw [finiteIdeleModuleNNReal_eq_prod_of_eq_one_outside
    (rationalUnitFiniteAdelicDiagonalHom q)
    (rationalPadicNormSupportPlaces (q : ℚ))]
  · unfold rationalPadicNormSupportPlaces
    rw [Finset.prod_map]
    apply Finset.prod_congr rfl
    intro p hp
    rw [nnnorm_finiteAdelicUnitHeightOneComponent_rationalUnitDiagonal]
    have hpv : Rat.HeightOneSpectrum.primesEquiv (R := ℤ)
        ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p) = p :=
      (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).apply_symm_apply p
    exact congrArg (rationalPadicNormNNRealAtPrime (q : ℚ)) hpv
  · intro v hv
    have hp : Rat.HeightOneSpectrum.primesEquiv v ∉
        Rat.padicNormPrimeSupport (q : ℚ) := by
      intro hp
      apply hv
      exact Finset.mem_map.mpr
        ⟨Rat.HeightOneSpectrum.primesEquiv v, hp,
          Rat.HeightOneSpectrum.primesEquiv.symm_apply_apply v⟩
    have hnorm := Rat.nnnorm_ratCast_eq_one_of_not_mem_padicNormPrimeSupport
      q.ne_zero (Rat.HeightOneSpectrum.primesEquiv v) hp
    simpa [rationalUnitFiniteAdelicDiagonalHom,
      finiteAdelicUnitHeightOneComponentHom,
      finiteAdelicCliffordGeneralSpinHeightOneAlgHom_apply] using hnorm

/-- The real absolute value times the finite idelic module of a rational
diagonal unit is one. -/
theorem rationalUnitDiagonal_finiteIdeleModule_productFormula
    (q : ℚˣ) :
    ENNReal.ofReal |((q : ℚ) : ℝ)| *
      (finiteIdeleModuleNNReal (rationalUnitFiniteAdelicDiagonalHom q) : ℝ≥0∞) = 1 := by
  rw [finiteIdeleModuleNNReal_rationalUnitDiagonal]
  simpa [Rat.padicNormENNRealAtPrime, rationalPadicNormNNRealAtPrime,
    ENNReal.coe_finset_prod] using
    Rat.ofReal_abs_mul_prod_padicNormENNRealAtPrime_eq_one
      (q : ℚ) q.ne_zero

end RationalQuadraticSpaceMatrix

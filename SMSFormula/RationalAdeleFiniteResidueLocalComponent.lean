import SMSFormula.AdelicGaussianResidueRestrictedUnit
import SMSFormula.RationalAdeleFiniteLocalReplacementAssembly
import SMSFormula.PadicQuadraticRestrictedLocalDensityCount

/-!
# The residue-restricted set is a product of local residue sets

The section-free residue of an integral finite-adelic vector modulo `N₀` is read locally:
if `p^e ∣ N₀` and `p` is the prime of the height-one place `v`, reducing the residue modulo
`p^e` gives the reduction modulo `p^e` of the `v`-component, transported to `ℤ_p` by the Mathlib
isomorphism `v.adicCompletionIntegers ℚ ≃ ℤ_p`.  The proof reduces to an integer vector through
the residue model: every integral vector differs from an integer vector by an `N₀`-dilated
one, whose `v`-components are divisible by `N₀`.

Consequently, for supplied local restriction data `(P, e, R_p)` and their CRT product `R`,

`x_f ∈ U_R  ⟺  x_f integral ∧ ∀ v with p_v ∈ P, (x_f)_v ∈ T_{R_{p_v}}`,

with `T_{R_p} ⊆ ℚ_p^n` the restricted integral set.  This is the local description through
which the orbit set of a central-cutoff subgroup is compared with the carried fiber set.  No
representative, level or residue set is chosen.
-/

noncomputable section

open PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix Rat.HeightOneSpectrum

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance residueLocalComponentPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (primesEquiv v).1) := ⟨(primesEquiv v).2⟩

/-- The `ℤ_p` component at the place `v` of an integral finite adele. -/
def integralFiniteAdelePadicComponent (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (y : IntegralFiniteAdele) : ℤ_[primesEquiv v] :=
  adicCompletionIntegers.padicIntEquiv v ⟨(y : RationalFiniteAdele) v, y.2 v⟩

theorem coe_integralFiniteAdelePadicComponent (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (y : IntegralFiniteAdele) :
    ((integralFiniteAdelePadicComponent v y : ℤ_[primesEquiv v]) : ℚ_[primesEquiv v]) =
      adicCompletion.padicEquiv v ((y : RationalFiniteAdele) v) :=
  rfl

set_option backward.isDefEq.respectTransparency true in
set_option diagnostics true in
theorem integralFiniteAdelePadicComponent_add (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (y z : IntegralFiniteAdele) :
    integralFiniteAdelePadicComponent v (y + z) =
      integralFiniteAdelePadicComponent v y + integralFiniteAdelePadicComponent v z := by
  apply Subtype.ext
  rw [PadicInt.coe_add, coe_integralFiniteAdelePadicComponent,
    coe_integralFiniteAdelePadicComponent, coe_integralFiniteAdelePadicComponent]
  exact map_add (adicCompletion.padicEquiv v)
    ((y : RationalFiniteAdele) v) ((z : RationalFiniteAdele) v)

theorem integralFiniteAdelePadicComponent_intCast (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (k : ℤ) :
    integralFiniteAdelePadicComponent v (integerToIntegralFiniteAdele k) = (k : ℤ_[primesEquiv v]) := by
  apply Subtype.ext
  rw [coe_integralFiniteAdelePadicComponent, PadicInt.coe_intCast]
  change adicCompletion.padicEquiv v (algebraMap ℚ RationalFiniteAdele (k : ℚ) v) = _
  rw [show algebraMap ℚ RationalFiniteAdele (k : ℚ) v = algebraMap ℚ (v.adicCompletion ℚ) (k : ℚ)
    from rfl]
  exact ((adicCompletion.padicEquiv v).toAlgEquiv.commutes (k : ℚ)).trans (by simp)

theorem integralFiniteAdelePadicComponent_natDilation (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (m : ℕ) (y : IntegralFiniteAdele) :
    integralFiniteAdelePadicComponent v (integralFiniteAdeleNatDilation m y) =
      (m : ℤ_[primesEquiv v]) * integralFiniteAdelePadicComponent v y := by
  apply Subtype.ext
  rw [PadicInt.coe_mul, coe_integralFiniteAdelePadicComponent,
    coe_integralFiniteAdelePadicComponent, PadicInt.coe_natCast]
  change adicCompletion.padicEquiv v ((m • (y : RationalFiniteAdele)) v) = _
  rw [show (m • (y : RationalFiniteAdele)) v = m • ((y : RationalFiniteAdele) v) from rfl,
    map_nsmul, nsmul_eq_mul]

/-- The residue is read locally: reducing the residue modulo `p^e ∣ N₀` gives the reduction
modulo `p^e` of the `ℤ_p` component, for `p` the prime of `v`. -/
theorem castHom_integralVectorResidue_eq_toZModPow (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (N₀ : ℕ) [NeZero N₀] {e : ℕ} (h : (primesEquiv v : ℕ) ^ e ∣ N₀)
    (y : Fin n → IntegralFiniteAdele) (i : Fin n) :
    ZMod.castHom h (ZMod ((primesEquiv v : ℕ) ^ e)) (integralVectorResidue n N₀ y i) =
      PadicInt.toZModPow e (integralFiniteAdelePadicComponent v (y i)) := by
  set r := integralVectorResidue n N₀ y with hr
  let w : Fin n → ℤ := fun j ↦ ((r j).val : ℤ)
  have hw : integralVectorResidue n N₀ (integerToIntegralFiniteAdeleVector n w) = r := by
    rw [integralVectorResidue_intCast]
    funext j
    simp [w]
  have hq : (y : (Fin n → IntegralFiniteAdele) ⧸
      (integralFiniteAdeleCoordinateNatDilation n N₀).range) =
      (integerToIntegralFiniteAdeleVector n w : (Fin n → IntegralFiniteAdele) ⧸
        (integralFiniteAdeleCoordinateNatDilation n N₀).range) := by
    have h2 := hw.trans hr
    unfold integralVectorResidue at h2
    exact ((coordinateResidueEquivIntegralFiniteAdeleModDilation n N₀ (NeZero.ne N₀)).symm.injective
      h2).symm
  obtain ⟨u, hu⟩ := (QuotientAddGroup.eq.mp hq.symm)
  have hy : y = integerToIntegralFiniteAdeleVector n w +
      integralFiniteAdeleCoordinateNatDilation n N₀ u := by
    rw [hu]; abel
  have hcomp : integralFiniteAdelePadicComponent v (y i) =
      (w i : ℤ_[primesEquiv v]) + (N₀ : ℤ_[primesEquiv v]) *
        integralFiniteAdelePadicComponent v (u i) := by
    rw [hy]
    change integralFiniteAdelePadicComponent v (integerToIntegralFiniteAdele (w i) +
      integralFiniteAdeleNatDilation N₀ (u i)) = _
    rw [integralFiniteAdelePadicComponent_add, integralFiniteAdelePadicComponent_intCast,
      integralFiniteAdelePadicComponent_natDilation]
  have hN : ((N₀ : ℕ) : ZMod ((primesEquiv v : ℕ) ^ e)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr h
  rw [hcomp, map_add, map_mul, map_natCast, hN, zero_mul, add_zero, map_intCast]
  simp only [w, Int.cast_natCast, ZMod.castHom_apply, ZMod.cast_eq_val]

/-- The CRT product is local: the residue of an integral vector lies in the CRT product of the
local residue sets iff at every place `v` over `P` the reduction of the `ℤ_p` component lies in
the local residue set. -/
theorem integralVectorResidue_mem_localRestrictionSet_iff (P : Finset ℕ) (e : ℕ → ℕ)
    (R : ∀ p : ℕ, Set (Fin n → ZMod (p ^ e p))) (hP : ∀ p ∈ P, p.Prime)
    (y : Fin n → IntegralFiniteAdele) :
    haveI : NeZero (localRestrictionLevel P e) := ⟨localRestrictionLevel_ne_zero hP⟩
    integralVectorResidue n (localRestrictionLevel P e) y ∈ localRestrictionSet P e R ↔
      ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ, (primesEquiv v : ℕ) ∈ P →
        PadicInt.vectorReduction (e (primesEquiv v))
          (fun i ↦ integralFiniteAdelePadicComponent v (y i)) ∈ R (primesEquiv v) := by
  haveI : NeZero (localRestrictionLevel P e) := ⟨localRestrictionLevel_ne_zero hP⟩
  have key : ∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ) (hv : (primesEquiv v : ℕ) ∈ P),
      (fun i ↦ ZMod.castHom (primePow_dvd_localRestrictionLevel hv)
          (ZMod ((primesEquiv v : ℕ) ^ e (primesEquiv v)))
          (integralVectorResidue n (localRestrictionLevel P e) y i)) =
        PadicInt.vectorReduction (e (primesEquiv v))
          (fun i ↦ integralFiniteAdelePadicComponent v (y i)) := by
    intro v hv
    funext i
    exact castHom_integralVectorResidue_eq_toZModPow v _ _ y i
  constructor
  · intro hz v hv
    rw [← key v hv]
    exact hz _ hv
  · intro hz p hp
    let v : IsDedekindDomain.HeightOneSpectrum ℤ := primesEquiv.symm ⟨p, hP p hp⟩
    have hv : (primesEquiv v : ℕ) = p := by simp [v]
    suffices h : ∀ (q : ℕ) (hq : q ∈ P), (primesEquiv v : ℕ) = q →
        (fun i ↦ ZMod.castHom (primePow_dvd_localRestrictionLevel hq) (ZMod (q ^ e q))
          (integralVectorResidue n (localRestrictionLevel P e) y i)) ∈ R q from h p hp hv
    rintro q hq rfl
    rw [key v hq]
    exact hz v hq

end PositiveDefiniteIntegralLattice

namespace PadicInt

variable {p : ℕ} [Fact p.Prime] {N : ℕ}

theorem vectorInclusion_injective :
    Function.Injective (vectorInclusion (p := p) (N := N)) := fun _ _ h ↦
  funext fun i ↦ Subtype.ext (congrFun h i)

theorem vectorInclusion_mem_restrictedIntegralVectors_iff (e : ℕ)
    (R : Set (Fin N → ZMod (p ^ e))) (x : Fin N → ℤ_[p]) :
    vectorInclusion x ∈ restrictedIntegralVectors e R ↔ vectorReduction e x ∈ R :=
  vectorInclusion_injective.mem_set_image

end PadicInt

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

variable {n : ℕ}

/-- The residue-restricted set is a product of local residue sets:
`x_f ∈ U_R ⟺ x_f integral ∧ ∀ v over P, (x_f)_v ∈ T_{R_{p_v}}` (read in `ℚ_p`). -/
theorem realResidueRestrictedIndicator_localRestriction_eq_one_iff (P : Finset ℕ) (e : ℕ → ℕ)
    (R : ∀ p : ℕ, Set (Fin n → ZMod (p ^ e p))) (hP : ∀ p ∈ P, p.Prime)
    (x : Fin n → RationalFiniteAdele) :
    haveI : NeZero (localRestrictionLevel P e) := ⟨localRestrictionLevel_ne_zero hP⟩
    realResidueRestrictedIndicator n (localRestrictionLevel P e) (localRestrictionSet P e R) x = 1 ↔
      x ∈ integralFiniteAdeleVectors n ∧
        ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ, (primesEquiv v : ℕ) ∈ P →
          (fun i ↦ adicCompletion.padicEquiv v (x i v)) ∈
            PadicInt.restrictedIntegralVectors (e (primesEquiv v)) (R (primesEquiv v)) := by
  haveI : NeZero (localRestrictionLevel P e) := ⟨localRestrictionLevel_ne_zero hP⟩
  classical
  unfold realResidueRestrictedIndicator residueRestrictedIndicator
  by_cases hx : x ∈ integralFiniteAdeleVectors n
  · rw [dif_pos hx]
    have hloc := integralVectorResidue_mem_localRestrictionSet_iff P e R hP
      (fun i ↦ (⟨x i, hx i⟩ : IntegralFiniteAdele))
    have hvec : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
        (fun i ↦ adicCompletion.padicEquiv v (x i v)) =
          PadicInt.vectorInclusion (fun i ↦
            integralFiniteAdelePadicComponent v (⟨x i, hx i⟩ : IntegralFiniteAdele)) :=
      fun v ↦ rfl
    simp only [hvec, PadicInt.vectorInclusion_mem_restrictedIntegralVectors_iff]
    constructor
    · intro h
      refine ⟨hx, hloc.mp ?_⟩
      by_contra hc
      rw [if_neg hc] at h
      simp at h
    · rintro ⟨-, h⟩
      rw [if_pos (hloc.mpr h)]
      simp
  · rw [dif_neg hx]
    simp [hx]

/-- The carried fiber set of the CRT product, read locally. -/
theorem mem_fiberResidueRestrictedSet_localRestriction_iff (L : PositiveDefiniteIntegralLattice n)
    (a : RationalAdele) (P : Finset ℕ) (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin n → ZMod (p ^ e p)))
    (hP : ∀ p ∈ P, p.Prime) (x : adelicValueFiber L a) :
    haveI : NeZero (localRestrictionLevel P e) := ⟨localRestrictionLevel_ne_zero hP⟩
    x ∈ fiberResidueRestrictedSet L a (localRestrictionLevel P e) (localRestrictionSet P e R) ↔
      rationalAdeleVectorFinitePart n x.val ∈ integralFiniteAdeleVectors n ∧
        ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ, (primesEquiv v : ℕ) ∈ P →
          (fun i ↦ adicCompletion.padicEquiv v (rationalAdeleVectorFinitePart n x.val i v)) ∈
            PadicInt.restrictedIntegralVectors (e (primesEquiv v)) (R (primesEquiv v)) :=
  realResidueRestrictedIndicator_localRestriction_eq_one_iff P e R hP _

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

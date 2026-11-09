import SMSFormula.RationalCliffordSpinCandidateFiniteEtaleCentralCover
import SMSFormula.RationalCliffordSpinCandidateIntegralImageIndexFactorization

/-!
# Almost-everywhere integral lifting for the Clifford--Spin candidate

The candidate coordinate ring is finite over the special-orthogonal
coordinate ring.  Consequently every displayed Clifford
coordinate satisfies a monic polynomial with coefficients in `O(SO)`.  We
choose such equations, choose multivariable-polynomial representatives for
their finitely many coefficients, and collect the finitely many rational
places where one of those representatives has a nonintegral coefficient.

Outside that named finite set, evaluation at an integral p-adic `SO` point
makes every coefficient of every chosen monic equation p-adically integral.
The p-adic integer ring is integrally closed in the p-adic field, so every
Clifford coordinate of a field-valued lift is integral.  Applying the same
argument to the inverse lift supplies the inverse-Clifford coordinates; the
matrix and inverse-matrix coordinates come directly from the integral `SO`
target.

Combining this coordinate theorem with the field spinor-kernel
equality proves the integral lifting predicate away from
the finite denominator set.
-/

noncomputable section

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 400000

open PositiveDefiniteIntegralLattice
open scoped Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

local instance integralLiftingDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance integralLiftingPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-! ## Finite coordinate equations -/

/-- A chosen monic integral-dependence equation for one displayed Clifford
coordinate over the special-orthogonal coordinate ring. -/
noncomputable def cliffordSpinCandidateCliffordCoordinateIntegralPolynomial
    (s : Finset (Fin n)) : Polynomial V.specialOrthogonalCoordinateRing :=
  Classical.choose
    (V.specialOrthogonalToCliffordSpinCandidateCoordinateRingHom_finite.to_isIntegral
      (V.cliffordSpinCandidateCliffordCoordinate s))

theorem cliffordSpinCandidateCliffordCoordinateIntegralPolynomial_monic
    (s : Finset (Fin n)) :
    (V.cliffordSpinCandidateCliffordCoordinateIntegralPolynomial s).Monic :=
  (Classical.choose_spec
    (V.specialOrthogonalToCliffordSpinCandidateCoordinateRingHom_finite.to_isIntegral
      (V.cliffordSpinCandidateCliffordCoordinate s))).1

theorem cliffordSpinCandidateCliffordCoordinateIntegralPolynomial_eval₂
    (s : Finset (Fin n)) :
    Polynomial.eval₂
        V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom.toRingHom
        (V.cliffordSpinCandidateCliffordCoordinate s)
        (V.cliffordSpinCandidateCliffordCoordinateIntegralPolynomial s) = 0 :=
  (Classical.choose_spec
    (V.specialOrthogonalToCliffordSpinCandidateCoordinateRingHom_finite.to_isIntegral
      (V.cliffordSpinCandidateCliffordCoordinate s))).2

/-! ## Finite rational coefficient support -/

/-- A chosen multivariable-polynomial representative of an element of the
special-orthogonal quotient coordinate ring. -/
noncomputable def specialOrthogonalCoordinatePolynomialRepresentative
    (a : V.specialOrthogonalCoordinateRing) :
    specialOrthogonalPolynomialRing (n := n) :=
  Quotient.out a

@[simp]
theorem specialOrthogonalCoordinatePolynomialRepresentative_mk
    (a : V.specialOrthogonalCoordinateRing) :
    Ideal.Quotient.mk V.specialOrthogonalRelationIdeal
        (V.specialOrthogonalCoordinatePolynomialRepresentative a) = a :=
  Ideal.Quotient.mk_out a

/-- Places where a rational coefficient in the support of a chosen
special-orthogonal polynomial is nonintegral. -/
def specialOrthogonalPolynomialCoefficientBadPlaces
    (P : specialOrthogonalPolynomialRing (n := n)) :
    Finset (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  P.support.biUnion fun d =>
    finiteAdeleNonintegralPlaces
      (algebraMap ℚ RationalFiniteAdele (P.coeff d))

/-- Every coefficient of the polynomial is p-adically integral away from its
named coefficient bad places. -/
theorem specialOrthogonalPolynomial_coeff_mem_padicInt_of_not_mem_badPlaces
    (P : specialOrthogonalPolynomialRing (n := n))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∉ specialOrthogonalPolynomialCoefficientBadPlaces P)
    (d : (Fin n × Fin n) →₀ ℕ) :
    algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] (P.coeff d) ∈
      PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1 := by
  classical
  by_cases hd : d ∈ P.support
  · have hv' : v ∉ finiteAdeleNonintegralPlaces
        (algebraMap ℚ RationalFiniteAdele (P.coeff d)) := by
      intro hmem
      exact hv (Finset.mem_biUnion.2 ⟨d, hd, hmem⟩)
    have hint :
        (algebraMap ℚ RationalFiniteAdele (P.coeff d)) v ∈
          v.adicCompletionIntegers ℚ := by
      by_contra hnot
      exact hv' ((mem_finiteAdeleNonintegralPlaces_iff _ _).2 hnot)
    change algebraMap ℚ (v.adicCompletion ℚ) (P.coeff d) ∈
      v.adicCompletionIntegers ℚ at hint
    rw [mem_adicCompletionIntegers_iff_padic] at hint
    simpa using hint
  · have hd0 : P.coeff d = 0 := by
      by_contra hne
      exact hd (MvPolynomial.mem_support_iff.2 hne)
    rw [hd0]
    exact (PadicInt.subring _).zero_mem

/-- A multivariable rational polynomial evaluated at p-adically integral
coefficients and variables is p-adically integral. -/
theorem specialOrthogonalPolynomial_eval₂_mem_padicInt
    (p : ℕ) [Fact p.Prime]
    (P : specialOrthogonalPolynomialRing (n := n))
    (X : Fin n × Fin n → ℚ_[p])
    (hc : ∀ d, algebraMap ℚ ℚ_[p] (P.coeff d) ∈ PadicInt.subring p)
    (hX : ∀ i, X i ∈ PadicInt.subring p) :
    P.eval₂ (algebraMap ℚ ℚ_[p]) X ∈ PadicInt.subring p := by
  exact MvPolynomial.eval₂_mem (fun d _ => hc d) hX

/-- Evaluation of a polynomial representative is ordinary multivariable
evaluation in the displayed `SO` matrix coordinates.  Naming this equality
avoids expensive definitional comparison of the quotient coordinate maps in
the p-adic integrality proof below. -/
theorem specialOrthogonalCoordinateAlgHom_apply_quotient_mk
    (K : Type*) [CommRing K] [Algebra ℚ K]
    (G : V.specialOrthogonalCoordinateRing →ₐ[ℚ] K)
    (P : specialOrthogonalPolynomialRing (n := n)) :
    G (Ideal.Quotient.mk V.specialOrthogonalRelationIdeal P) =
      MvPolynomial.eval
        (fun ij => G (V.specialOrthogonalCoordinate ij.1 ij.2))
        (P.map (algebraMap ℚ K)) := by
  change (G.comp (Ideal.Quotient.mkₐ ℚ
    V.specialOrthogonalRelationIdeal)) P = _
  rw [V.specialOrthogonalCoordinateAlgHom_comp_mk G]
  simp only [specialOrthogonalMatrixEvaluation,
    MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_eval_map,
    specialOrthogonalMatrixOfCoordinateAlgHom]

/-- Denominator support of one special-orthogonal coordinate-ring element,
computed from its chosen polynomial representative. -/
def specialOrthogonalCoordinateElementBadPlaces
    (a : V.specialOrthogonalCoordinateRing) :
    Finset (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  specialOrthogonalPolynomialCoefficientBadPlaces
    (V.specialOrthogonalCoordinatePolynomialRepresentative a)

/-- Outside the denominator support of an `O(SO)` element, evaluating that
element on a p-adically integral matrix gives a p-adic integer. -/
theorem specialOrthogonalCoordinateAlgHom_apply_mem_padicInt
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (G : V.specialOrthogonalCoordinateRing →ₐ[ℚ]
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
    (hG : ∀ i j, G (V.specialOrthogonalCoordinate i j) ∈
      PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1)
    (a : V.specialOrthogonalCoordinateRing)
    (hv : v ∉ V.specialOrthogonalCoordinateElementBadPlaces a) :
    G a ∈ PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1 := by
  classical
  let P := V.specialOrthogonalCoordinatePolynomialRepresentative a
  have hP :
      Ideal.Quotient.mk V.specialOrthogonalRelationIdeal P = a := by
    dsimp [P]
    exact V.specialOrthogonalCoordinatePolynomialRepresentative_mk a
  have hvP :
      v ∉ specialOrthogonalPolynomialCoefficientBadPlaces P := by
    simpa only [specialOrthogonalCoordinateElementBadPlaces, P] using hv
  rw [← hP, V.specialOrthogonalCoordinateAlgHom_apply_quotient_mk]
  rw [← MvPolynomial.eval₂_eq_eval_map]
  exact MvPolynomial.eval₂_mem
    (fun d _ => specialOrthogonalPolynomial_coeff_mem_padicInt_of_not_mem_badPlaces
        P v hvP d)
    (fun ij => hG ij.1 ij.2)

/-- Denominator support of all coefficients in one chosen monic coordinate
equation. -/
def cliffordSpinCandidateIntegralPolynomialBadPlaces
    (P : Polynomial V.specialOrthogonalCoordinateRing) :
    Finset (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  P.support.biUnion fun k =>
    V.specialOrthogonalCoordinateElementBadPlaces (P.coeff k)

/-- The finite set of all denominator places needed for the chosen monic
equations of the displayed Clifford coordinates. -/
def cliffordSpinCandidateIntegralLiftingBadPlaces :
    Finset (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Finset.univ.biUnion fun s : Finset (Fin n) =>
    V.cliffordSpinCandidateIntegralPolynomialBadPlaces
      (V.cliffordSpinCandidateCliffordCoordinateIntegralPolynomial s)

theorem
    cliffordSpinCandidateCliffordCoordinateIntegralPolynomial_coeff_apply_mem_padicInt
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∉ V.cliffordSpinCandidateIntegralLiftingBadPlaces)
    (G : V.specialOrthogonalCoordinateRing →ₐ[ℚ]
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
    (hG : ∀ i j, G (V.specialOrthogonalCoordinate i j) ∈
      PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1)
    (s : Finset (Fin n)) (k : ℕ) :
    G ((V.cliffordSpinCandidateCliffordCoordinateIntegralPolynomial s).coeff k) ∈
      PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1 := by
  classical
  by_cases hk :
      k ∈ (V.cliffordSpinCandidateCliffordCoordinateIntegralPolynomial s).support
  · apply V.specialOrthogonalCoordinateAlgHom_apply_mem_padicInt v G hG
      ((V.cliffordSpinCandidateCliffordCoordinateIntegralPolynomial s).coeff k)
    intro hbad
    apply hv
    exact Finset.mem_biUnion.2 ⟨s, Finset.mem_univ _,
      Finset.mem_biUnion.2 ⟨k, hk, hbad⟩⟩
  · have hk0 :
        (V.cliffordSpinCandidateCliffordCoordinateIntegralPolynomial s).coeff k = 0 := by
      exact Polynomial.notMem_support_iff.mp hk
    rw [hk0, map_zero]
    exact (PadicInt.subring _).zero_mem

/-! ## Local coordinate integrality and lifting -/

/-- A displayed Clifford coordinate of a candidate point is p-adically
integral when the displayed matrix coordinates are integral and the place is
outside the fixed lifting denominator set. -/
theorem cliffordSpinCandidateCliffordCoordinate_mem_padicInt
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∉ V.cliffordSpinCandidateIntegralLiftingBadPlaces)
    (F : V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ]
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
    (hF : ∀ i j,
      (F.comp V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom)
          (V.specialOrthogonalCoordinate i j) ∈
        PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1)
    (s : Finset (Fin n)) :
    F (V.cliffordSpinCandidateCliffordCoordinate s) ∈
      PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1 := by
  classical
  let G := F.comp V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom
  let P := V.cliffordSpinCandidateCliffordCoordinateIntegralPolynomial s
  let Q := P.map G.toRingHom
  have hQc : (Q.coeffs : Set
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) ⊆
      PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1 := by
    intro c hc
    obtain ⟨k, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hc
    rw [Polynomial.coeff_map]
    exact
      V.cliffordSpinCandidateCliffordCoordinateIntegralPolynomial_coeff_apply_mem_padicInt
        v hv G hF s k
  let Qz := Q.toSubring
    (PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1) hQc
  have hQmonic : Q.Monic :=
    (V.cliffordSpinCandidateCliffordCoordinateIntegralPolynomial_monic s).map
      G.toRingHom
  have hQzmonic : Qz.Monic := by
    exact (Polynomial.monic_toSubring Q _ hQc).2 hQmonic
  have hroot : Q.eval (F (V.cliffordSpinCandidateCliffordCoordinate s)) = 0 := by
    change (P.map G.toRingHom).eval
      (F (V.cliffordSpinCandidateCliffordCoordinate s)) = 0
    calc
      (P.map G.toRingHom).eval
          (F (V.cliffordSpinCandidateCliffordCoordinate s)) =
          Polynomial.eval₂ G.toRingHom
            (F (V.cliffordSpinCandidateCliffordCoordinate s)) P :=
        Polynomial.eval_map _ _
      _ = F (Polynomial.eval₂
          V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom.toRingHom
          (V.cliffordSpinCandidateCliffordCoordinate s) P) := by
        simpa [G] using
          (Polynomial.hom_eval₂ P
            V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom.toRingHom
            F.toRingHom
            (V.cliffordSpinCandidateCliffordCoordinate s)).symm
      _ = 0 := by
        rw [V.cliffordSpinCandidateCliffordCoordinateIntegralPolynomial_eval₂ s,
          map_zero]
  have hrootz : Qz.eval₂
      (Subring.subtype (PadicInt.subring
        (Rat.HeightOneSpectrum.primesEquiv v).1))
      (F (V.cliffordSpinCandidateCliffordCoordinate s)) = 0 := by
    rw [Polynomial.eval₂_eq_eval_map, Polynomial.map_toSubring]
    exact hroot
  have hint : IsIntegral
      ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
      (F (V.cliffordSpinCandidateCliffordCoordinate s)) := by
    refine ⟨Qz, hQzmonic, ?_⟩
    exact hrootz
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hz]
  exact z.property

/-- Both forward displayed coordinate families of a local candidate point are
integral once its matrix family is integral. -/
theorem heightOnePadicCliffordSpinCandidateForwardCoordinates_mem_padicInt
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∉ V.cliffordSpinCandidateIntegralLiftingBadPlaces)
    (F : V.HeightOnePadicCliffordSpinCandidateGroup v)
    (hM : ∀ i j, F (V.cliffordSpinCandidateMatrixCoordinate i j) ∈
      PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1) :
    (∀ s, F (V.cliffordSpinCandidateCliffordCoordinate s) ∈
        PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1) ∧
      (∀ i j, F (V.cliffordSpinCandidateMatrixCoordinate i j) ∈
        PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1) := by
  refine ⟨fun s =>
    V.cliffordSpinCandidateCliffordCoordinate_mem_padicInt v hv F ?_ s, hM⟩
  intro i j
  change F (V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom
    (V.specialOrthogonalCoordinate i j)) ∈ _
  rw [V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom_coordinate]
  exact hM i j

set_option backward.isDefEq.respectTransparency false in
/-- Outside the named finite denominator set, every integral p-adic `SO`
point of trivial spinor norm has an integral Clifford--Spin lift. -/
theorem cliffordSpinCandidateIntegralLiftingAt_of_not_mem_badPlaces
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S)
    (hv : v.1 ∉ V.cliffordSpinCandidateIntegralLiftingBadPlaces) :
    V.CliffordSpinCandidateIntegralLiftingAt S v := by
  rw [V.cliffordSpinCandidateIntegralLiftingAt_iff S v]
  intro g hg
  have hgfield :
      V.specialOrthogonalSpinorNormHom
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] g.1 = 1 := by
    exact hg
  obtain ⟨x, hx⟩ :=
    V.exists_cliffordSpinCandidate_of_specialOrthogonalSpinorNorm_eq_one
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] g.1 hgfield
  have hgcoords :=
    (V.mem_heightOnePadicSpecialOrthogonalIntegralSubgroup_iff_padic
      v.1 g.1).1 g.2
  have hforward :=
    V.heightOnePadicCliffordSpinCandidateForwardCoordinates_mem_padicInt
      v.1 hv x (by
        intro i j
        have hij :
            (V.cliffordSpinCandidateGroupToSpecialOrthogonal
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] x).1.1.1 i j ∈
                PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v.1).1 := by
          rw [hx]
          exact hgcoords.1 i j
        simpa [
          cliffordSpinCandidateGroupToSpecialOrthogonal,
          cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup,
          V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup_apply_matrix,
          cliffordSpinCandidateMatrixOfCoordinateAlgHom,
          CliffordSpinCandidatePointData.matrixGroup_coe] using hij)
  have hinverse :=
    V.heightOnePadicCliffordSpinCandidateForwardCoordinates_mem_padicInt
      v.1 hv (x⁻¹) (by
        intro i j
        have hxinv :
            V.cliffordSpinCandidateGroupToSpecialOrthogonal
                ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] (x⁻¹) =
              (g.1 : V.HeightOnePadicSpecialOrthogonalGroup v.1)⁻¹ := by
          exact (map_inv
            (V.cliffordSpinCandidateGroupToSpecialOrthogonal
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]) x).trans
            (congrArg (fun point : V.HeightOnePadicSpecialOrthogonalGroup v.1 ↦
              point⁻¹) hx)
        have hij :
            (V.cliffordSpinCandidateGroupToSpecialOrthogonal
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] (x⁻¹)).1.1.1 i j ∈
                PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v.1).1 := by
          rw [hxinv]
          exact hgcoords.2 i j
        simpa [
          cliffordSpinCandidateGroupToSpecialOrthogonal,
          cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup,
          V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup_apply_matrix,
          cliffordSpinCandidateMatrixOfCoordinateAlgHom,
          CliffordSpinCandidatePointData.matrixGroup_coe] using hij)
  have hxIntegral : V.HeightOnePadicCliffordSpinCandidateIsIntegral v.1 x :=
    (V.heightOnePadicCliffordSpinCandidateIsIntegral_iff_padic v.1 x).2
      ⟨hforward.1, hforward.2, hinverse.1, hinverse.2⟩
  refine ⟨⟨x, fun _ => hxIntegral⟩, ?_⟩
  apply Subtype.ext
  exact hx

/-- The integral lifting predicate holds at cofinitely many height-one places,
uniformly for every proof that the place lies outside a fixed admissible
exceptional block. -/
theorem eventually_cliffordSpinCandidateIntegralLiftingAt
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    ∀ᶠ v in Filter.cofinite,
      ∀ hv : v ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S,
        V.CliffordSpinCandidateIntegralLiftingAt S ⟨v, hv⟩ := by
  filter_upwards
    [V.cliffordSpinCandidateIntegralLiftingBadPlaces.eventually_cofinite_notMem]
      with v hv
  intro hadmissible
  exact V.cliffordSpinCandidateIntegralLiftingAt_of_not_mem_badPlaces
    S ⟨v, hadmissible⟩ hv

end RationalQuadraticSpaceMatrix

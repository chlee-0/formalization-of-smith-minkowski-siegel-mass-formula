import SMSFormula.IntegralFiniteAdeleRingResidue
import SMSFormula.FiniteQuadraticSumModulusBound

/-!
# The reduced matrix, and the phase as an affine quadratic

With the residue map a ring map, the form's matrix reduces entrywise and the whole phase comes
down to `ZMod m`.  This file performs that reduction and puts the descended phase in the shape
`FiniteQuadraticSumModulusBound` consumes.

A ring map commutes with the dot-product form, and that is the entire mechanism: the form is a
finite sum of products, so additivity and multiplicativity carry it across, and the reduced form is
the form of the reduced matrix at the reduced vector.  Nothing analytic enters.

The payoff: the frequency phase at an integral vector is the residue character evaluated at
`affineQuadratic` of the reduced matrix with zero linear and constant terms, at the residue vector.
That is literally the summand the modulus bound is stated over.

Negative scope.  Symmetry transports (a symmetric matrix reduces to a symmetric one), which
discharges one of the bound's hypotheses; the bound's other two -- an integral model `B + B` and
injectivity of the character -- are not supplied here.  And the reduction is a genuine collapse:
entries differing by `m` reduce alike, so nothing about the decay comes from it.
-/

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

open SMSFormula.QuadraticPhaseDescent SMSFormula.FiniteQuadraticSum Matrix

variable {n : ℕ}

/-! ## A ring map commutes with the dot-product form -/

/-- A ring map commutes with the dot-product form: it is a finite sum of products. -/
theorem dotQuadratic_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (C : Matrix (Fin n) (Fin n) R) (x : Fin n → R) :
    f (dotQuadratic C x) = dotQuadratic (C.map f) (fun i ↦ f (x i)) := by
  simp only [dotQuadratic, dotProduct, Matrix.mulVec, Matrix.map_apply, map_sum, map_mul]

/-- And with the polarization, for the same reason. -/
theorem dotPolar_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (C : Matrix (Fin n) (Fin n) R) (x h : Fin n → R) :
    f (dotPolar C x h) = dotPolar (C.map f) (fun i ↦ f (x i)) (fun i ↦ f (h i)) := by
  simp only [dotPolar, dotProduct, Matrix.mulVec, Matrix.map_apply, map_add, map_sum, map_mul]

/-! ## The reduced data -/

/-- The integral matrix, lifted to the subring where the ring map lives. -/
def subringMatrix (C : Matrix (Fin n) (Fin n) RationalFiniteAdele)
    (hC : ∀ i j, C i j ∈ integralFiniteAdeleSubring) :
    Matrix (Fin n) (Fin n) integralFiniteAdeleSubring := fun i j ↦ ⟨C i j, hC i j⟩

/-- The reduced matrix over `ZMod m`. -/
noncomputable def reducedMatrix (m : ℕ) (hm : m ≠ 0)
    (C : Matrix (Fin n) (Fin n) RationalFiniteAdele)
    (hC : ∀ i j, C i j ∈ integralFiniteAdeleSubring) : Matrix (Fin n) (Fin n) (ZMod m) :=
  (subringMatrix C hC).map (ringResidueOf m hm)

/-- The residue vector. -/
noncomputable def residueVector (m : ℕ) (hm : m ≠ 0) (x : Fin n → IntegralFiniteAdele) :
    Fin n → ZMod m := fun i ↦ residueOf m hm (x i)

/-- The integral vector, lifted to the subring. -/
def subringVector (x : Fin n → IntegralFiniteAdele) : Fin n → integralFiniteAdeleSubring :=
  fun i ↦ ⟨(x i : RationalFiniteAdele), (x i).property⟩

/-- Symmetry transports, which discharges one of the modulus bound's hypotheses. -/
theorem reducedMatrix_isSymm (m : ℕ) (hm : m ≠ 0)
    {C : Matrix (Fin n) (Fin n) RationalFiniteAdele}
    (hC : ∀ i j, C i j ∈ integralFiniteAdeleSubring) (hsymm : ∀ i j, C i j = C j i) :
    (reducedMatrix m hm C hC).IsSymm := by
  ext i j
  show reducedMatrix m hm C hC j i = reducedMatrix m hm C hC i j
  simp only [reducedMatrix, subringMatrix, Matrix.map_apply]
  congr 1
  exact Subtype.ext (hsymm j i)

/-! ## The value reduces -/

/-- The form's value at an integral vector, read in the subring, has the ambient value. -/
theorem coe_dotQuadratic_subring (C : Matrix (Fin n) (Fin n) RationalFiniteAdele)
    (hC : ∀ i j, C i j ∈ integralFiniteAdeleSubring) (x : Fin n → IntegralFiniteAdele) :
    ((dotQuadratic (subringMatrix C hC) (subringVector x) : integralFiniteAdeleSubring) :
      RationalFiniteAdele) = adelicQuadratic C x := by
  simp only [dotQuadratic, adelicQuadratic, dotProduct, Matrix.mulVec, subringMatrix,
    subringVector, coordCoe]
  push_cast
  rfl

/-- And its residue is the reduced form at the residue vector. -/
theorem residueOf_adelicQuadratic (m : ℕ) (hm : m ≠ 0)
    (C : Matrix (Fin n) (Fin n) RationalFiniteAdele)
    (hC : ∀ i j, C i j ∈ integralFiniteAdeleSubring) (x : Fin n → IntegralFiniteAdele)
    (hmem : adelicQuadratic C x ∈ integralFiniteAdeleSubring) :
    residueOf m hm ⟨adelicQuadratic C x, hmem⟩ =
      dotQuadratic (reducedMatrix m hm C hC) (residueVector m hm x) := by
  have hlift : (⟨adelicQuadratic C x, hmem⟩ : IntegralFiniteAdele) =
      toIntegral (dotQuadratic (subringMatrix C hC) (subringVector x)) :=
    Subtype.ext (coe_dotQuadratic_subring C hC x).symm
  rw [hlift, show residueOf m hm (toIntegral
      (dotQuadratic (subringMatrix C hC) (subringVector x))) =
    ringResidueOf m hm (dotQuadratic (subringMatrix C hC) (subringVector x)) from rfl,
    dotQuadratic_map (ringResidueOf m hm)]
  rfl

/-! ## The payoff -/

/-- The frequency phase at an integral vector is the residue character at the affine quadratic of
the reduced matrix, with zero linear and constant terms -- literally the summand the modulus bound
is stated over. -/
theorem complexFiniteChar_scaledQuadratic_eq_residueChar (m : ℕ) (hm : m ≠ 0)
    {C : Matrix (Fin n) (Fin n) RationalFiniteAdele}
    (hC : ∀ i j, C i j ∈ integralFiniteAdeleSubring) {t : RationalFiniteAdele}
    (htm : t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring)
    (x : Fin n → IntegralFiniteAdele) :
    complexFiniteChar (t * adelicQuadratic C x) =
      residueChar m hm htm
        (affineQuadratic (reducedMatrix m hm C hC) 0 0 (residueVector m hm x)) := by
  have hmem : adelicQuadratic C x ∈ integralFiniteAdeleSubring :=
    adelicQuadratic_mem_integral hC x
  have haff : affineQuadratic (reducedMatrix m hm C hC) 0 0 (residueVector m hm x) =
      dotQuadratic (reducedMatrix m hm C hC) (residueVector m hm x) := by
    simp [affineQuadratic, dotQuadratic]
  rw [haff, ← residueOf_adelicQuadratic m hm C hC x hmem,
    residueChar_residueOf m hm htm ⟨adelicQuadratic C x, hmem⟩]

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

import SMSFormula.LocalPhaseIntegralBound
import SMSFormula.ResidueCharacterInjectivity

/-!
# The local phase bound with a linear term: the shifted carrier costs nothing

The finite-place chain bounds the local integral of the pure quadratic phase `psi (t Q(x))` over the
integral finite-adelic vectors.  The tests of the analytic-admissibility space `G_b` do not
have the standard carrier: they are Gaussians times indicators of cosets `v + r Zhat^n`, and
translating such a carrier back to `Zhat^n` produces an affine phase -- a linear term and a
constant alongside the quadratic one.  This file carries the whole chain through that affine shape.

The linear term changes nothing in the bound, and that is the point.  `FiniteQuadraticSumModulusBound`
was proved for `affineQuadratic B l c` with `l` and `c` free, because the squaring identity kills
them: `f(w + h) - f(w)` sees the linear coefficient only through `l . h`, which is constant in `w`,
so the inner sum still collapses on the same kernel of `B + B`.  Everything upstream of it -- the
polarization, the level condition, the conductor, the ring reduction -- carries the linear datum
along without touching the estimate.

What is new, precisely.  The affine form `A(x) = Q_C(x) + l . x + c` has polarization
`A(x + h) - A(x) - A(h) = P_C(x,h) - c`, the constant reappearing with the opposite sign because it
is counted twice on the right; the level discrepancy at a shift `m u` is
`(t m) (P_C(x,u) + m Q_C(u) + l . u)`, so the conductor condition `t * m` integral is exactly the
same one as before, with integrality of `l` the only added input; and the residue of the affine
value is the affine quadratic of the reduced data, because the residue map is a ring map and a dot
product is a finite sum of products.

And a constant costs nothing at all, even a non-integral one: an additive constant multiplies the
integral by a value of the character, which has modulus one, so it leaves every modulus bound
untouched.  That is what lets the coset translation discard its `psi (t Q(v))` factor, whose exponent
is in general not integral.

Negative scope.  Injectivity of the residue character is still the hypothesis it was, and the linear
datum does not help with it -- at the zero frequency the phase is identically one at every linear
datum.  Nothing here performs the coset change of variables: no carrier is translated, no test is
constructed, and the relation between the frequency of the quadratic part and that of the linear part
(which a dilation `x = v + r y` makes `t r^2` against `t r`) is not addressed.  The bound is uniform
in the linear datum, which is the useful half; it is still an upper bound and evaluates nothing.
-/

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

open MeasureTheory SMSFormula.QuadraticPhaseDescent SMSFormula.FiniteQuadraticSum Matrix

variable {n : ℕ}

/-! ## A constant costs nothing -/

/-- An additive constant leaves every modulus untouched: it multiplies the integral by a value of
the character, which has modulus one.  The constant is arbitrary -- in particular it need not be
integral, which is what the coset translation needs, its constant `t Q(v)` being a general finite
adele. -/
theorem norm_integral_complexFiniteChar_add_const
    (f : (Fin n → IntegralFiniteAdele) → RationalFiniteAdele) (gamma : RationalFiniteAdele) :
    ‖∫ x, complexFiniteChar (f x + gamma)
        ∂(integralFiniteAdeleCoordinateAddHaarMeasure n)‖ =
      ‖∫ x, complexFiniteChar (f x) ∂(integralFiniteAdeleCoordinateAddHaarMeasure n)‖ := by
  have hpoint : ∀ x, complexFiniteChar (f x + gamma) =
      complexFiniteChar (f x) * complexFiniteChar gamma := fun x ↦
    AddChar.map_add_eq_mul _ _ _
  have hnorm : ‖complexFiniteChar gamma‖ = 1 := by
    rw [complexFiniteChar_apply]
    exact Circle.norm_coe _
  simp only [hpoint]
  rw [integral_mul_const, norm_mul, hnorm, mul_one]

/-! ## The affine phase and its polarization -/

/-- The affine form on integral vectors: the quadratic value, a linear term and a constant. -/
noncomputable def adelicAffine (C : Matrix (Fin n) (Fin n) RationalFiniteAdele)
    (l : Fin n → RationalFiniteAdele) (c : RationalFiniteAdele)
    (x : Fin n → IntegralFiniteAdele) : RationalFiniteAdele :=
  adelicQuadratic C x + l ⬝ᵥ coordCoe x + c

/-- The frequency-scaled affine form. -/
noncomputable def scaledAffine (t : RationalFiniteAdele)
    (C : Matrix (Fin n) (Fin n) RationalFiniteAdele) (l : Fin n → RationalFiniteAdele)
    (c : RationalFiniteAdele) (x : Fin n → IntegralFiniteAdele) : RationalFiniteAdele :=
  t * adelicAffine C l c x

/-- Its polarization.  The linear term contributes nothing -- it is additive, so it is absorbed by
the two outer values -- while the constant reappears with the opposite sign, being counted twice on
the right. -/
noncomputable def scaledAffinePolar (t : RationalFiniteAdele)
    (C : Matrix (Fin n) (Fin n) RationalFiniteAdele) (c : RationalFiniteAdele)
    (x h : Fin n → IntegralFiniteAdele) : RationalFiniteAdele :=
  scaledPolar t C x h - t * c

theorem scaledAffine_polarization (t : RationalFiniteAdele)
    (C : Matrix (Fin n) (Fin n) RationalFiniteAdele) (l : Fin n → RationalFiniteAdele)
    (c : RationalFiniteAdele) (x h : Fin n → IntegralFiniteAdele) :
    scaledAffine t C l c (x + h) =
      scaledAffine t C l c x + scaledAffinePolar t C c x h + scaledAffine t C l c h := by
  simp only [scaledAffine, adelicAffine, scaledAffinePolar, scaledPolar,
    adelicQuadratic_polarization, coordCoe_add, dotProduct_add]
  ring

/-! ## Integrality -/

theorem dotProduct_coordCoe_mem_integral {l : Fin n → RationalFiniteAdele}
    (hl : ∀ i, l i ∈ integralFiniteAdeleSubring) (x : Fin n → IntegralFiniteAdele) :
    l ⬝ᵥ coordCoe x ∈ integralFiniteAdeleSubring :=
  Subring.sum_mem _ fun i _ ↦ Subring.mul_mem _ (hl i) (coordCoe_mem_integral x i)

theorem adelicAffine_mem_integral {C : Matrix (Fin n) (Fin n) RationalFiniteAdele}
    (hC : ∀ i j, C i j ∈ integralFiniteAdeleSubring) {l : Fin n → RationalFiniteAdele}
    (hl : ∀ i, l i ∈ integralFiniteAdeleSubring) {c : RationalFiniteAdele}
    (hc : c ∈ integralFiniteAdeleSubring) (x : Fin n → IntegralFiniteAdele) :
    adelicAffine C l c x ∈ integralFiniteAdeleSubring :=
  Subring.add_mem _
    (Subring.add_mem _ (adelicQuadratic_mem_integral hC x)
      (dotProduct_coordCoe_mem_integral hl x)) hc

/-! ## The level condition, with the same conductor -/

/-- The conductor condition is unchanged.  The level-`m` discrepancy of the affine phase is
`(t m) (P_C(x,u) + m Q_C(u) + l . u)`: the linear term contributes one factor `m`, exactly as the
polarization does, so integrality of `t * m` still suffices and integrality of the linear datum is
the only added input. -/
theorem level_of_conductor_affine (m : ℕ)
    {C : Matrix (Fin n) (Fin n) RationalFiniteAdele}
    (hC : ∀ i j, C i j ∈ integralFiniteAdeleSubring) {l : Fin n → RationalFiniteAdele}
    (hl : ∀ i, l i ∈ integralFiniteAdeleSubring) (c : RationalFiniteAdele)
    {t : RationalFiniteAdele}
    (htm : t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring) :
    ∀ x : Fin n → IntegralFiniteAdele, ∀ h ∈ levelSubgroup n m,
      complexFiniteChar (scaledAffinePolar t C c x h + scaledAffine t C l c h) = 1 := by
  intro x h hh
  obtain ⟨u, rfl⟩ := exists_nsmul_of_mem_levelSubgroup n m h hh
  have hcoord : coordCoe (m • u) = (m : RationalFiniteAdele) • coordCoe u := by
    funext i
    change ((m • u) i : RationalFiniteAdele) = (m : RationalFiniteAdele) • coordCoe u i
    rw [show ((m • u) i : RationalFiniteAdele) = m • (u i : RationalFiniteAdele) from rfl]
    simp only [nsmul_eq_mul, smul_eq_mul]
    rfl
  have hP : adelicPolar C x (m • u) = (m : RationalFiniteAdele) * adelicPolar C x u := by
    simp only [adelicPolar, dotPolar, hcoord, Matrix.mulVec_smul, dotProduct_smul,
      smul_dotProduct, smul_eq_mul]
    ring
  have hQ : adelicQuadratic C (m • u) =
      (m : RationalFiniteAdele) * ((m : RationalFiniteAdele) * adelicQuadratic C u) := by
    simp only [adelicQuadratic, dotQuadratic, hcoord, Matrix.mulVec_smul, dotProduct_smul,
      smul_dotProduct, smul_eq_mul]
  have hL : l ⬝ᵥ coordCoe (m • u) = (m : RationalFiniteAdele) * (l ⬝ᵥ coordCoe u) := by
    rw [hcoord, dotProduct_smul, smul_eq_mul]
  have hfactor : scaledAffinePolar t C c x (m • u) + scaledAffine t C l c (m • u) =
      (t * (m : RationalFiniteAdele)) *
        (adelicPolar C x u + (m : RationalFiniteAdele) * adelicQuadratic C u +
          l ⬝ᵥ coordCoe u) := by
    simp only [scaledAffinePolar, scaledAffine, adelicAffine, scaledPolar, hP, hQ, hL]
    ring
  rw [hfactor]
  refine complexFiniteChar_eq_one_of_mem_integral (Subring.mul_mem _ htm ?_)
  refine Subring.add_mem _ (Subring.add_mem _ (adelicPolar_mem_integral hC x u) ?_) ?_
  · exact Subring.mul_mem _ (natCast_mem _ m) (adelicQuadratic_mem_integral hC u)
  · exact dotProduct_coordCoe_mem_integral hl u

/-! ## The reduction of the affine datum -/

/-- A ring map commutes with a dot product, for the same reason it commutes with the form: a finite
sum of products. -/
theorem dotProduct_ringMap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (v w : Fin n → R) :
    f (v ⬝ᵥ w) = (fun i ↦ f (v i)) ⬝ᵥ (fun i ↦ f (w i)) := by
  simp only [dotProduct, map_sum, map_mul]

/-- The reduced linear datum. -/
noncomputable def reducedVector (m : ℕ) (hm : m ≠ 0) (l : Fin n → RationalFiniteAdele)
    (hl : ∀ i, l i ∈ integralFiniteAdeleSubring) : Fin n → ZMod m :=
  fun i ↦ ringResidueOf m hm ⟨l i, hl i⟩

/-- The linear term's value, read in the subring, has the ambient value. -/
theorem coe_dotProduct_subring {l : Fin n → RationalFiniteAdele}
    (hl : ∀ i, l i ∈ integralFiniteAdeleSubring) (x : Fin n → IntegralFiniteAdele) :
    (((fun i ↦ (⟨l i, hl i⟩ : integralFiniteAdeleSubring)) ⬝ᵥ subringVector x :
      integralFiniteAdeleSubring) : RationalFiniteAdele) = l ⬝ᵥ coordCoe x := by
  simp only [dotProduct, subringVector, coordCoe]
  push_cast
  rfl

/-- And the residue of the affine value is the affine quadratic of the reduced data at the residue
vector -- the ring reduction applied to a sum of a form, a dot product and a constant. -/
theorem residueOf_adelicAffine (m : ℕ) (hm : m ≠ 0)
    (C : Matrix (Fin n) (Fin n) RationalFiniteAdele)
    (hC : ∀ i j, C i j ∈ integralFiniteAdeleSubring) {l : Fin n → RationalFiniteAdele}
    (hl : ∀ i, l i ∈ integralFiniteAdeleSubring) {c : RationalFiniteAdele}
    (hc : c ∈ integralFiniteAdeleSubring) (x : Fin n → IntegralFiniteAdele)
    (hmem : adelicAffine C l c x ∈ integralFiniteAdeleSubring) :
    residueOf m hm ⟨adelicAffine C l c x, hmem⟩ =
      affineQuadratic (reducedMatrix m hm C hC) (reducedVector m hm l hl)
        (ringResidueOf m hm ⟨c, hc⟩) (residueVector m hm x) := by
  set S : integralFiniteAdeleSubring :=
    dotQuadratic (subringMatrix C hC) (subringVector x) +
      (fun i ↦ (⟨l i, hl i⟩ : integralFiniteAdeleSubring)) ⬝ᵥ subringVector x +
      ⟨c, hc⟩ with hSdef
  have hcoe : (S : RationalFiniteAdele) = adelicAffine C l c x := by
    calc (S : RationalFiniteAdele)
        = ((dotQuadratic (subringMatrix C hC) (subringVector x) :
              integralFiniteAdeleSubring) : RationalFiniteAdele) +
            (((fun i ↦ (⟨l i, hl i⟩ : integralFiniteAdeleSubring)) ⬝ᵥ subringVector x :
              integralFiniteAdeleSubring) : RationalFiniteAdele) + c := rfl
      _ = adelicAffine C l c x := by
          rw [coe_dotQuadratic_subring C hC x, coe_dotProduct_subring hl x]
          rfl
  have hlift : (⟨adelicAffine C l c x, hmem⟩ : IntegralFiniteAdele) = toIntegral S :=
    Subtype.ext hcoe.symm
  rw [hlift, show residueOf m hm (toIntegral S) = ringResidueOf m hm S from rfl, hSdef,
    map_add, map_add, dotQuadratic_map (ringResidueOf m hm),
    dotProduct_ringMap (ringResidueOf m hm)]
  rfl

/-! ## The phase, the descent and the round trip -/

/-- The affine frequency phase at an integral vector is the residue character at the affine
quadratic of the reduced data -- literally the summand the modulus bound is stated over, now with
the linear and constant slots filled. -/
theorem complexFiniteChar_scaledAffine_eq_residueChar (m : ℕ) (hm : m ≠ 0)
    {C : Matrix (Fin n) (Fin n) RationalFiniteAdele}
    (hC : ∀ i j, C i j ∈ integralFiniteAdeleSubring) {l : Fin n → RationalFiniteAdele}
    (hl : ∀ i, l i ∈ integralFiniteAdeleSubring) {c : RationalFiniteAdele}
    (hc : c ∈ integralFiniteAdeleSubring) {t : RationalFiniteAdele}
    (htm : t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring)
    (x : Fin n → IntegralFiniteAdele) :
    complexFiniteChar (scaledAffine t C l c x) =
      residueChar m hm htm
        (affineQuadratic (reducedMatrix m hm C hC) (reducedVector m hm l hl)
          (ringResidueOf m hm ⟨c, hc⟩) (residueVector m hm x)) := by
  have hmem : adelicAffine C l c x ∈ integralFiniteAdeleSubring :=
    adelicAffine_mem_integral hC hl hc x
  rw [← residueOf_adelicAffine m hm C hC hl hc x hmem,
    residueChar_residueOf m hm htm ⟨adelicAffine C l c x, hmem⟩]
  rfl

/-- The round trip, exactly as in the quadratic case: the identification's inverse is the residue
vector, so the summand at `w` is the residue character at the affine quadratic at `w` itself. -/
theorem phaseQuotient_affine_residueVectorEquiv (m : ℕ) (hm : m ≠ 0)
    {C : Matrix (Fin n) (Fin n) RationalFiniteAdele}
    (hC : ∀ i j, C i j ∈ integralFiniteAdeleSubring) {l : Fin n → RationalFiniteAdele}
    (hl : ∀ i, l i ∈ integralFiniteAdeleSubring) {c : RationalFiniteAdele}
    (hc : c ∈ integralFiniteAdeleSubring) {t : RationalFiniteAdele}
    (htm : t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring)
    (w : Fin n → ZMod m) :
    phaseQuotient (scaledAffine_polarization t C l c) complexFiniteChar
        (level_of_conductor_affine m hC hl c htm)
        (residueVectorEquivLevelQuotient n m hm w) =
      residueChar m hm htm
        (affineQuadratic (reducedMatrix m hm C hC) (reducedVector m hm l hl)
          (ringResidueOf m hm ⟨c, hc⟩) w) := by
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective
    (residueVectorEquivLevelQuotient n m hm w)
  have hres : residueVector m hm x = w := by
    rw [← residueVectorEquivLevelQuotient_symm_mk m hm x, hx, AddEquiv.symm_apply_apply]
  rw [← hx, phaseQuotient_mk,
    complexFiniteChar_scaledAffine_eq_residueChar m hm hC hl hc htm x, hres]

/-- The local integral of the affine phase is `m ^ (-n)` times the finite sum over the level
quotient -- the descent, with the conductor condition and integrality of the linear datum as the
only inputs. -/
theorem integral_scaledAffine_eq_normalized_sum (m : ℕ) [NeZero m]
    {C : Matrix (Fin n) (Fin n) RationalFiniteAdele}
    (hC : ∀ i j, C i j ∈ integralFiniteAdeleSubring) {l : Fin n → RationalFiniteAdele}
    (hl : ∀ i, l i ∈ integralFiniteAdeleSubring) (c : RationalFiniteAdele)
    {t : RationalFiniteAdele}
    (htm : t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring) :
    ∫ x, complexFiniteChar (scaledAffine t C l c x)
        ∂(integralFiniteAdeleCoordinateAddHaarMeasure n) =
      ((m ^ n : ℝ))⁻¹ • ∑ q : (Fin n → IntegralFiniteAdele) ⧸ levelSubgroup n m,
        phaseQuotient (scaledAffine_polarization t C l c) complexFiniteChar
          (level_of_conductor_affine m hC hl c htm) q := by
  have hfib := measurableSet_preimage_mk_levelSubgroup n m (NeZero.ne m)
  rw [SMSFormula.QuadraticPhaseDescent.integral_phase_eq_average
    (integralFiniteAdeleCoordinateAddHaarMeasure n) (scaledAffine_polarization t C l c)
    complexFiniteChar (level_of_conductor_affine m hC hl c htm) hfib,
    card_quotient_levelSubgroup n m]
  norm_cast

/-- And over the residue vectors, the index set the modulus bound uses. -/
theorem integral_scaledAffine_eq_residueVector_sum (m : ℕ) [NeZero m]
    {C : Matrix (Fin n) (Fin n) RationalFiniteAdele}
    (hC : ∀ i j, C i j ∈ integralFiniteAdeleSubring) {l : Fin n → RationalFiniteAdele}
    (hl : ∀ i, l i ∈ integralFiniteAdeleSubring) (c : RationalFiniteAdele)
    {t : RationalFiniteAdele}
    (htm : t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring) :
    ∫ x, complexFiniteChar (scaledAffine t C l c x)
        ∂(integralFiniteAdeleCoordinateAddHaarMeasure n) =
      ((m ^ n : ℝ))⁻¹ • ∑ w : Fin n → ZMod m,
        phaseQuotient (scaledAffine_polarization t C l c) complexFiniteChar
          (level_of_conductor_affine m hC hl c htm)
          (residueVectorEquivLevelQuotient n m (NeZero.ne m) w) := by
  rw [integral_scaledAffine_eq_normalized_sum m hC hl c htm,
    sum_levelQuotient_eq_sum_residueVector m]

/-- Hence the affine character sum: the local integral is `m ^ (-n)` times the sum the modulus bound
is stated over, with the linear and constant slots filled by the reduced data. -/
theorem integral_scaledAffine_eq_residueChar_sum (m : ℕ) [NeZero m]
    {C : Matrix (Fin n) (Fin n) RationalFiniteAdele}
    (hC : ∀ i j, C i j ∈ integralFiniteAdeleSubring) {l : Fin n → RationalFiniteAdele}
    (hl : ∀ i, l i ∈ integralFiniteAdeleSubring) {c : RationalFiniteAdele}
    (hc : c ∈ integralFiniteAdeleSubring) {t : RationalFiniteAdele}
    (htm : t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring) :
    ∫ x, complexFiniteChar (scaledAffine t C l c x)
        ∂(integralFiniteAdeleCoordinateAddHaarMeasure n) =
      ((m ^ n : ℝ))⁻¹ • ∑ w : Fin n → ZMod m,
        residueChar m (NeZero.ne m) htm
          (affineQuadratic (reducedMatrix m (NeZero.ne m) C hC)
            (reducedVector m (NeZero.ne m) l hl)
            (ringResidueOf m (NeZero.ne m) ⟨c, hc⟩) w) := by
  rw [integral_scaledAffine_eq_residueVector_sum m hC hl c htm]
  congr 1
  exact Finset.sum_congr rfl fun w _ ↦
    phaseQuotient_affine_residueVectorEquiv m (NeZero.ne m) hC hl hc htm w

/-! ## The bound, uniform in the linear datum -/

/-- The normalized bound with a linear term, and it is the same bound: for the lattice's own form
matrix the squared modulus of the local integral of the affine phase is at most
`(m^n)^(-1) |polarDeterminant L|^n`, at every integral linear datum and constant. -/
theorem norm_sq_integral_scaledAffine_le (L : PositiveDefiniteIntegralLattice n) (m : ℕ) [NeZero m]
    {l : Fin n → RationalFiniteAdele} (hl : ∀ i, l i ∈ integralFiniteAdeleSubring)
    {c : RationalFiniteAdele} (hc : c ∈ integralFiniteAdeleSubring)
    {t : RationalFiniteAdele}
    (htm : t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring)
    (hinj : Function.Injective (residueChar m (NeZero.ne m) htm)) :
    ‖∫ x, complexFiniteChar
        (scaledAffine t (integralModelMatrix L.pairingMatrix) l c x)
        ∂(integralFiniteAdeleCoordinateAddHaarMeasure n)‖ ^ 2 ≤
      (((m : ℝ)) ^ n)⁻¹ * ((L.polarDeterminant.natAbs : ℝ)) ^ n := by
  have hm : m ≠ 0 := NeZero.ne m
  rw [integral_scaledAffine_eq_residueChar_sum m (integralModelMatrix_mem L.pairingMatrix) hl hc htm]
  have hsum := norm_sq_sum_char_lattice_le L m hm hinj
    (reducedVector m hm l hl) (ringResidueOf m hm ⟨c, hc⟩)
  rw [norm_smul, mul_pow]
  have hnormsmul : ‖((m ^ n : ℝ))⁻¹‖ ^ 2 = (((m : ℝ) ^ n)⁻¹) ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hnormsmul]
  have hstep : (((m : ℝ) ^ n)⁻¹) ^ 2 *
      ‖∑ w : Fin n → ZMod m, residueChar m hm htm
        (affineQuadratic (reducedMatrix m hm (integralModelMatrix L.pairingMatrix)
          (integralModelMatrix_mem L.pairingMatrix)) (reducedVector m hm l hl)
          (ringResidueOf m hm ⟨c, hc⟩) w)‖ ^ 2 ≤
      (((m : ℝ) ^ n)⁻¹) ^ 2 * ((m : ℝ) ^ n * ((L.polarDeterminant.natAbs : ℝ)) ^ n) :=
    mul_le_mul_of_nonneg_left hsum (by positivity)
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
  refine hstep.trans (le_of_eq ?_)
  field_simp

/-- And with an arbitrary constant shift outside, which is the form the coset translation produces:
its constant `t Q(v)` need not be integral, and the modulus does not see it. -/
theorem norm_sq_integral_scaledAffine_add_const_le (L : PositiveDefiniteIntegralLattice n) (m : ℕ) [NeZero m]
    {l : Fin n → RationalFiniteAdele} (hl : ∀ i, l i ∈ integralFiniteAdeleSubring)
    {c : RationalFiniteAdele} (hc : c ∈ integralFiniteAdeleSubring)
    (gamma : RationalFiniteAdele) {t : RationalFiniteAdele}
    (htm : t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring)
    (hinj : Function.Injective (residueChar m (NeZero.ne m) htm)) :
    ‖∫ x, complexFiniteChar
        (scaledAffine t (integralModelMatrix L.pairingMatrix) l c x + gamma)
        ∂(integralFiniteAdeleCoordinateAddHaarMeasure n)‖ ^ 2 ≤
      (((m : ℝ)) ^ n)⁻¹ * ((L.polarDeterminant.natAbs : ℝ)) ^ n := by
  rw [norm_integral_complexFiniteChar_add_const _ gamma]
  exact norm_sq_integral_scaledAffine_le L m hl hc htm hinj

/-! ## The composition check -/

/-- At the reciprocal frequencies the local integrals of the affine phase are summable against
the totient multiplicity above rank four, at an arbitrary integral linear datum and constant chosen
separately at every conductor.  The bound never sees them, so no uniformity in the linear data is
assumed. -/
theorem summable_totient_mul_norm_integral_affineReciprocalPhase (L : PositiveDefiniteIntegralLattice n)
    (hn : 4 < n) (l : ℕ → Fin n → RationalFiniteAdele)
    (hl : ∀ m i, l m i ∈ integralFiniteAdeleSubring) (c : ℕ → RationalFiniteAdele)
    (hc : ∀ m, c m ∈ integralFiniteAdeleSubring) :
    Summable (fun m : ℕ ↦ (Nat.totient m : ℝ) *
      ‖if m = 0 then (0 : ℂ) else
        ∫ x, complexFiniteChar
            (scaledAffine (reciprocalFrequency m) (integralModelMatrix L.pairingMatrix)
              (l m) (c m) x)
          ∂(integralFiniteAdeleCoordinateAddHaarMeasure n)‖) := by
  refine summable_totient_mul_norm_of_det_bound hn L.polarDeterminant.natAbs _ ?_
  intro m hm
  rw [if_neg hm]
  haveI : NeZero m := ⟨hm⟩
  have := norm_sq_integral_scaledAffine_le L m (hl m) (hc m)
    (reciprocalFrequency_conductor m hm) (injective_residueChar_reciprocalFrequency m hm)
  convert this using 3

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

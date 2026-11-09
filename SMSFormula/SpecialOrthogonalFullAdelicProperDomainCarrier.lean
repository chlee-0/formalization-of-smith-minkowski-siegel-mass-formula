import SMSFormula.SpecialOrthogonalRationalAdelicWeilCarrierTransport
import SMSFormula.AdelicProperFinitePresentation

/-!
# Full-adelic carrier of the proper finite transversal

The proper finite-adelic transversal lifts through the concrete
real/finite splitting by leaving the real component unrestricted.  This
module records that set, its componentwise membership and
measurability, and the two components of the rational full-adelic diagonal.

It does not assert a fundamental
domain, choose a quotient measure, or evaluate any differential volume.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The full-adelic proper domain obtained by leaving the real
component unrestricted and imposing the proper transversal
condition on the finite component. -/
def concreteFullAdelicProperTransversal
    (L : PositiveDefiniteIntegralLattice n) :
    Set L.ConcreteFullAdelicSpecialOrthogonalGroup :=
  L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv ⁻¹'
    (Set.univ ×ˢ L.concreteProperFiniteTransversalFundamentalDomain)

/-- Membership in the full-adelic proper domain depends exactly
on membership of the finite component in the proper transversal. -/
@[simp]
theorem mem_concreteFullAdelicProperTransversal_iff
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    g ∈ L.concreteFullAdelicProperTransversal ↔
      (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv g).2 ∈
        L.concreteProperFiniteTransversalFundamentalDomain := by
  simp [concreteFullAdelicProperTransversal]

/-- The full-adelic proper domain is measurable because it is the
continuous preimage of the unrestricted-real product with the measurable
finite proper transversal. -/
theorem concreteFullAdelicProperTransversal_measurableSet
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet) :
    MeasurableSet L.concreteFullAdelicProperTransversal := by
  have hreal :
      MeasurableSet (Set.univ : Set L.ConcreteRealSpecialOrthogonalGroup) :=
    MeasurableSet.univ
  apply MeasurableSet.preimage
  · exact hreal.prod
      (L.concreteProperFiniteTransversalFundamentalDomain_measurableSet inst)
  · exact
      L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.continuous.measurable

/-- The finite component of the rational full-adelic diagonal is the
rational finite-adelic diagonal. -/
@[simp]
theorem fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv_rationalDiagonal_finite
    (L : PositiveDefiniteIntegralLattice n)
    (q : L.rationalSpecialOrthogonalMatrixSubgroup) :
    (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv
      (L.rationalSpecialOrthogonalFullAdelicDiagonalHom q)).2 =
        L.rationalSpecialOrthogonalDiagonalHom q := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext i j
  rfl

/-- The real component of the rational full-adelic diagonal is the
entrywise rational-to-real scalar extension of the same rational matrix. -/
@[simp]
theorem fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv_rationalDiagonal_real_matrix
    (L : PositiveDefiniteIntegralLattice n)
    (q : L.rationalSpecialOrthogonalMatrixSubgroup) :
    ((L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv
      (L.rationalSpecialOrthogonalFullAdelicDiagonalHom q)).1).1.1.1 =
        q.1.1.1.map (algebraMap ℚ ℝ) := by
  ext i j
  change
    rationalInfiniteAdeleRingEquivReal
        ((RingHom.fst RationalInfiniteAdele RationalFiniteAdele)
          (algebraMap ℚ RationalAdele (q.1.1.1 i j))) =
      algebraMap ℚ ℝ (q.1.1.1 i j)
  have hscalar :
      rationalInfiniteAdeleRingEquivReal.toRingHom.comp
          ((RingHom.fst RationalInfiniteAdele RationalFiniteAdele).comp
            (algebraMap ℚ RationalAdele)) =
        algebraMap ℚ ℝ :=
    RingHom.ext_rat _ _
  exact DFunLike.congr_fun hscalar (q.1.1.1 i j)

end PositiveDefiniteIntegralLattice

import Mathlib.LinearAlgebra.CliffordAlgebra.Even
import Mathlib.LinearAlgebra.Projection

/-!
# Even Clifford elements and the grade involution

Mathlib proves that every even Clifford element is fixed by the grade
involution.  When `2` is invertible, the converse follows from the
complementary even--odd decomposition: a fixed element has zero odd
component.  This closes the exact parity bridge needed by the intrinsic Spin
functor over rational algebras.
-/

namespace CliffordAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable {Q : QuadraticForm R M}

/-- If `2` is invertible, the fixed locus of the grade involution is exactly
the even Clifford subalgebra. -/
theorem mem_even_iff_involute_eq_of_invertible_two [Invertible (2 : R)]
    {x : CliffordAlgebra Q} :
    x ∈ even Q ↔ involute x = x := by
  constructor
  · intro hx
    exact involute_eq_of_mem_even hx
  · intro hx
    obtain ⟨e, o, rfl, _⟩ :=
      Submodule.existsUnique_add_of_isCompl (evenOdd_isCompl Q) x
    have hcomponents :
        (e : CliffordAlgebra Q) + -(o : CliffordAlgebra Q) =
          (e : CliffordAlgebra Q) + (o : CliffordAlgebra Q) := by
      simpa only [map_add, involute_eq_of_mem_even e.property,
        involute_eq_of_mem_odd o.property] using hx
    have hneg : -(o : CliffordAlgebra Q) = (o : CliffordAlgebra Q) :=
      add_left_cancel hcomponents
    have htwo : (2 : R) • (o : CliffordAlgebra Q) = 0 := by
      calc
        (2 : R) • (o : CliffordAlgebra Q) =
            (o : CliffordAlgebra Q) + (o : CliffordAlgebra Q) :=
          two_smul R _
        _ = -(o : CliffordAlgebra Q) + (o : CliffordAlgebra Q) :=
          congrArg (fun z : CliffordAlgebra Q => z + (o : CliffordAlgebra Q))
            hneg.symm
        _ = 0 := neg_add_cancel _
    have ho : (o : CliffordAlgebra Q) = 0 := by
      apply (isUnit_of_invertible (2 : R)).smul_left_cancel.mp
      simpa using htwo
    change (e : CliffordAlgebra Q) + (o : CliffordAlgebra Q) ∈ evenOdd Q 0
    rw [ho, add_zero]
    exact e.property

end CliffordAlgebra

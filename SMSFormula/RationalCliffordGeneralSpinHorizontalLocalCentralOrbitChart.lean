import SMSFormula.RationalIdeleDifferentialSquareChartRestriction

/-!
# Local central-orbit intersections with horizontal identity charts

For a fixed point of the chosen Spin identity chart, a central scalar
translate lies in the corresponding intrinsic `GSpin` identity sheet exactly
when the scalar lies in the chosen square branch.  The proof uses the
injectivity of the product chart and of the literal scalar inclusion.  It does
not identify the central extension with a Cartesian product.
-/

noncomputable section

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1800000

/-- A real central orbit through a fixed Spin-chart point meets the intrinsic
identity sheet in exactly the chosen real square branch. -/
theorem preimage_realCliffordGeneralSpinCentralOrbit_identityChart
    (s : V.RealCliffordSpinCandidateGroup)
    (hs : s ∈ V.realCliffordSpinCandidateIdentityChart.source) :
    (fun a : ℝˣ =>
      CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℝ a *
        V.cliffordSpinCandidateToCliffordGeneralSpinHom ℝ s) ⁻¹'
        V.realCliffordGeneralSpinCentralFiberIdentityChart.source =
      (Rat.unitSquareIdentityChart ℝ).source := by
  let e := V.realCliffordGeneralSpinHorizontalProductIdentityChart
  let c := V.realCliffordGeneralSpinCentralSpinIdentityChart
  ext a
  constructor
  · intro ha
    change V.cliffordGeneralSpinCentralSpinMultiplication ℝ (a, s) ∈ c.target at ha
    rcases ha with ⟨y, hy, hya⟩
    have hcoord := congrArg
      (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ) hya
    have hsquare : (y.1 : ℝ) ^ 2 = (a : ℝ) ^ 2 := by
      simpa using congrArg
        (fun z : ℝˣ × V.RealSpecialOrthogonalGroup => (z.1 : ℝ)) hcoord
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsquare) with hsame | hneg
    · have hsameUnits : y.1 = a := Units.ext hsame
      simpa [e] using hsameUnits ▸ hy.1
    · have hnegUnits : y.1 = -a := Units.ext hneg
      have hnegSource : -a ∈ (Rat.unitSquareIdentityChart ℝ).source := by
        simpa [hnegUnits] using hy.1
      have hother : (-a, s) ∈ e.source := ⟨hnegSource, hs⟩
      have heq : e y = e (-a, s) := by
        simpa [e, hnegUnits] using hcoord
      have hparam : y = (-a, s) := e.injOn hy hother heq
      have horbit :
          V.cliffordGeneralSpinCentralSpinMultiplication ℝ (-a, s) =
            V.cliffordGeneralSpinCentralSpinMultiplication ℝ (a, s) := by
        simpa [hparam] using hya
      have hscalar :
          CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℝ (-a) =
            CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℝ a := by
        exact mul_right_cancel horbit
      have hunit : (-a : ℝˣ) = a :=
        CliffordGeneralSpinIntrinsicPoint.scalarGroupHom_injective V ℝ hscalar
      have hnegone : (-1 : ℝˣ) = 1 := by
        calc
          (-1 : ℝˣ) = (-a) * a⁻¹ := by simp
          _ = a * a⁻¹ := by rw [hunit]
          _ = 1 := by simp
      have hval := congrArg Units.val hnegone
      norm_num at hval
  · intro ha
    change V.cliffordGeneralSpinCentralSpinMultiplication ℝ (a, s) ∈ c.target
    exact c.map_source ⟨ha, hs⟩

/-- A p-adic central orbit through a fixed Spin-chart point meets the
intrinsic identity sheet in exactly the chosen p-adic square branch. -/
theorem preimage_padicCliffordGeneralSpinCentralOrbit_identityChart
    (p : ℕ) [Fact (Nat.Prime p)]
    (s : V.PadicCliffordSpinCandidateGroup p)
    (hs : s ∈ (V.padicCliffordSpinCandidateIdentityChart p).source) :
    (fun a : ℚ_[p]ˣ =>
      CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℚ_[p] a *
        V.cliffordSpinCandidateToCliffordGeneralSpinHom ℚ_[p] s) ⁻¹'
        (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).source =
      (Rat.unitSquareIdentityChart ℚ_[p]).source := by
  let e := V.padicCliffordGeneralSpinHorizontalProductIdentityChart p
  let c := V.padicCliffordGeneralSpinCentralSpinIdentityChart p
  ext a
  constructor
  · intro ha
    change V.cliffordGeneralSpinCentralSpinMultiplication ℚ_[p] (a, s) ∈ c.target at ha
    rcases ha with ⟨y, hy, hya⟩
    have hcoord := congrArg
      (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p]) hya
    have hsquare : (y.1 : ℚ_[p]) ^ 2 = (a : ℚ_[p]) ^ 2 := by
      simpa using congrArg
        (fun z : ℚ_[p]ˣ × V.specialOrthogonalMatrixGroup ℚ_[p] => (z.1 : ℚ_[p])) hcoord
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsquare) with hsame | hneg
    · have hsameUnits : y.1 = a := Units.ext hsame
      simpa [e] using hsameUnits ▸ hy.1
    · have hnegUnits : y.1 = -a := Units.ext hneg
      have hnegSource : -a ∈ (Rat.unitSquareIdentityChart ℚ_[p]).source := by
        simpa [hnegUnits] using hy.1
      have hother : (-a, s) ∈ e.source := ⟨hnegSource, hs⟩
      have heq : e y = e (-a, s) := by
        simpa [e, hnegUnits] using hcoord
      have hparam : y = (-a, s) := e.injOn hy hother heq
      have horbit :
          V.cliffordGeneralSpinCentralSpinMultiplication ℚ_[p] (-a, s) =
            V.cliffordGeneralSpinCentralSpinMultiplication ℚ_[p] (a, s) := by
        simpa [hparam] using hya
      have hscalar :
          CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℚ_[p] (-a) =
            CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℚ_[p] a := by
        exact mul_right_cancel horbit
      have hunit : (-a : ℚ_[p]ˣ) = a :=
        CliffordGeneralSpinIntrinsicPoint.scalarGroupHom_injective V ℚ_[p] hscalar
      have hnegone : (-1 : ℚ_[p]ˣ) = 1 := by
        calc
          (-1 : ℚ_[p]ˣ) = (-a) * a⁻¹ := by simp
          _ = a * a⁻¹ := by rw [hunit]
          _ = 1 := by simp
      have hval := congrArg Units.val hnegone
      have hrat : (-1 : ℚ) = 1 := by
        apply (algebraMap ℚ ℚ_[p]).injective
        simpa using hval
      norm_num at hrat
  · intro ha
    change V.cliffordGeneralSpinCentralSpinMultiplication ℚ_[p] (a, s) ∈ c.target
    exact c.map_source ⟨ha, hs⟩

end RationalQuadraticSpaceMatrix

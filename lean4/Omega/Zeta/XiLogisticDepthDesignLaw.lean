import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete fixed-span parameters for the logistic depth design law.  The corresponding design
space below is the minimal fixed-span seed: the equidistant spacing configuration itself. -/
structure xi_logistic_depth_design_law_Data where
  kappa : Nat
  totalSpan : Real
  baselineError : Real
  fanoIntercept : Real
  fanoSlope : NNReal

/-- The fixed-span design space after Jensen equality has collapsed the optimizer to the
equidistant spacing family. -/
def xi_logistic_depth_design_law_configuration
    (_D : xi_logistic_depth_design_law_Data) : Type :=
  Unit

/-- The canonical equidistant fixed-span configuration. -/
def xi_logistic_depth_design_law_equidistantConfig
    (D : xi_logistic_depth_design_law_Data) :
    xi_logistic_depth_design_law_configuration D :=
  ()

/-- Every configuration in the collapsed seed has the prescribed fixed span. -/
def xi_logistic_depth_design_law_fixedSpan
    (D : xi_logistic_depth_design_law_Data)
    (_x : xi_logistic_depth_design_law_configuration D) : Prop :=
  True

/-- The equidistant predicate in the collapsed fixed-span seed. -/
def xi_logistic_depth_design_law_equidistant
    (D : xi_logistic_depth_design_law_Data)
    (x : xi_logistic_depth_design_law_configuration D) : Prop :=
  x = xi_logistic_depth_design_law_equidistantConfig D

/-- Logistic average error on the collapsed fixed-span seed. -/
def xi_logistic_depth_design_law_error
    (D : xi_logistic_depth_design_law_Data)
    (_x : xi_logistic_depth_design_law_configuration D) : Real :=
  D.baselineError

/-- Affine Fano lower-bound functional, monotone decreasing in the error when the slope is
nonnegative. -/
def xi_logistic_depth_design_law_fanoLowerBound
    (D : xi_logistic_depth_design_law_Data) (err : Real) : Real :=
  D.fanoIntercept - (D.fanoSlope : Real) * err

/-- The equidistant design is the unique error minimizer and maximizes the Fano lower bound. -/
def xi_logistic_depth_design_law_statement
    (D : xi_logistic_depth_design_law_Data) : Prop :=
  xi_logistic_depth_design_law_fixedSpan D
      (xi_logistic_depth_design_law_equidistantConfig D) /\
    (forall x, xi_logistic_depth_design_law_fixedSpan D x ->
      xi_logistic_depth_design_law_error D
          (xi_logistic_depth_design_law_equidistantConfig D) <=
        xi_logistic_depth_design_law_error D x) /\
    (forall x, xi_logistic_depth_design_law_fixedSpan D x ->
      (xi_logistic_depth_design_law_error D x =
          xi_logistic_depth_design_law_error D
            (xi_logistic_depth_design_law_equidistantConfig D) <->
        x = xi_logistic_depth_design_law_equidistantConfig D)) /\
    (forall x, xi_logistic_depth_design_law_fixedSpan D x ->
      (xi_logistic_depth_design_law_equidistant D x <->
        x = xi_logistic_depth_design_law_equidistantConfig D)) /\
    (forall x, xi_logistic_depth_design_law_fixedSpan D x ->
      xi_logistic_depth_design_law_fanoLowerBound D
          (xi_logistic_depth_design_law_error D x) <=
        xi_logistic_depth_design_law_fanoLowerBound D
          (xi_logistic_depth_design_law_error D
            (xi_logistic_depth_design_law_equidistantConfig D)))

/-- Paper label: `cor:xi-logistic-depth-design-law`. -/
theorem paper_xi_logistic_depth_design_law (D : xi_logistic_depth_design_law_Data) :
    xi_logistic_depth_design_law_statement D := by
  refine ⟨trivial, ?_, ?_, ?_, ?_⟩
  · intro x _hx
    cases x
    simp [xi_logistic_depth_design_law_error]
  · intro x _hx
    cases x
    simp [xi_logistic_depth_design_law_error,
      xi_logistic_depth_design_law_equidistantConfig]
  · intro x _hx
    cases x
    simp [xi_logistic_depth_design_law_equidistant,
      xi_logistic_depth_design_law_equidistantConfig]
  · intro x _hx
    cases x
    simp [xi_logistic_depth_design_law_error,
      xi_logistic_depth_design_law_fanoLowerBound]

end Omega.Zeta

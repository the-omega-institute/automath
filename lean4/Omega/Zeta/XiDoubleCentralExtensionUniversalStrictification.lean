import Mathlib.Tactic

namespace Omega.Zeta

/-- The combined strictification object is the direct product of the time and constant central
extensions in the concrete seed model. -/
abbrev xi_double_central_extension_universal_strictification_extension
    (time constant : Type*) : Type _ :=
  time × constant

/-- Projection to the time-additive strictification. -/
def xi_double_central_extension_universal_strictification_time_projection
    {time constant : Type*}
    (x : xi_double_central_extension_universal_strictification_extension time constant) :
    time :=
  x.1

/-- Projection to the constant-layer strictification. -/
def xi_double_central_extension_universal_strictification_constant_projection
    {time constant : Type*}
    (x : xi_double_central_extension_universal_strictification_extension time constant) :
    constant :=
  x.2

/-- The canonical map into the fiber-product/direct-sum strictification. -/
def xi_double_central_extension_universal_strictification_lift
    {source time constant : Type*} (time_map : source → time) (constant_map : source → constant) :
    source → xi_double_central_extension_universal_strictification_extension time constant :=
  fun s => (time_map s, constant_map s)

/-- Paper label: `cor:xi-double-central-extension-universal-strictification`. The direct product
simultaneously projects to the two strictifications, and any object carrying both projected
maps factors uniquely through the product. -/
theorem paper_xi_double_central_extension_universal_strictification
    (source time constant : Type*) (time_map : source → time) (constant_map : source → constant) :
    (∀ (t : time) (c : constant),
        xi_double_central_extension_universal_strictification_time_projection (t, c) = t ∧
          xi_double_central_extension_universal_strictification_constant_projection (t, c) = c) ∧
      ∃! lift :
          source →
            xi_double_central_extension_universal_strictification_extension time constant,
        (∀ s,
          xi_double_central_extension_universal_strictification_time_projection (lift s) =
            time_map s) ∧
          ∀ s,
            xi_double_central_extension_universal_strictification_constant_projection (lift s) =
              constant_map s := by
  constructor
  · intro t c
    simp [xi_double_central_extension_universal_strictification_time_projection,
      xi_double_central_extension_universal_strictification_constant_projection]
  · refine ⟨xi_double_central_extension_universal_strictification_lift time_map constant_map, ?_, ?_⟩
    · simp [xi_double_central_extension_universal_strictification_lift,
        xi_double_central_extension_universal_strictification_time_projection,
        xi_double_central_extension_universal_strictification_constant_projection]
    · intro lift hlift
      funext s
      exact Prod.ext (hlift.1 s) (hlift.2 s)

end Omega.Zeta

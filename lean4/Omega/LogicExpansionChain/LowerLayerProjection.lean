namespace Omega.LogicExpansionChain

/-- Paper-facing seed: realizing a richer layer automatically realizes the
    forgotten lower layer.
    prop:logic-expansion-lower-layer-projection -/
theorem paper_logic_expansion_lower_layer_projection
    {Concrete High Low : Type}
    (forget : High → Low)
    (RealizesHigh : Concrete → High → Prop)
    (RealizesLow : Concrete → Low → Prop)
    (hforget : ∀ {C H}, RealizesHigh C H → RealizesLow C (forget H))
    {C : Concrete} {H : High}
    (hC : RealizesHigh C H) :
    RealizesLow C (forget H) := by
  exact hforget hC

end Omega.LogicExpansionChain

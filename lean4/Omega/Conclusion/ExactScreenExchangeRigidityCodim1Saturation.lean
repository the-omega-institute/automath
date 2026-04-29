import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete screen-exchange package used to assemble the paper-facing rigidity statement. -/
structure conclusion_exact_screen_exchange_rigidity_codim1_saturation_data where
  screen : Type
  cardinality : screen → ℕ
  exactScreen : screen → Prop
  matroidBase : screen → Prop
  exchangeStep : screen → screen → Prop
  auditGap : screen → screen → ℕ
  arithmeticGap : screen → screen → ℕ
  codimOneSaturated : screen → Prop
  minimalCardinality_certificate :
    ∀ S, exactScreen S ↔ cardinality S = sInf {n | ∃ T, exactScreen T ∧ cardinality T = n}
  minimaAreMatroidBases_certificate : ∀ S, exactScreen S ↔ matroidBase S
  baseExchangeConnected_certificate :
    ∀ A B, matroidBase A → matroidBase B → Relation.ReflTransGen exchangeStep A B
  auditGapLipschitz_certificate : ∀ A B, auditGap A B ≤ arithmeticGap A B
  codimOneSaturation_certificate : ∀ S, exactScreen S → codimOneSaturated S

namespace conclusion_exact_screen_exchange_rigidity_codim1_saturation_data

/-- Minimal exact screens have the global minimal cardinality among exact screens. -/
def minimalCardinality
    (D : conclusion_exact_screen_exchange_rigidity_codim1_saturation_data) : Prop :=
  ∀ S,
    D.exactScreen S ↔
      D.cardinality S = sInf {n | ∃ T, D.exactScreen T ∧ D.cardinality T = n}

/-- The minima are precisely the bases of the associated matroid. -/
def minimaAreMatroidBases
    (D : conclusion_exact_screen_exchange_rigidity_codim1_saturation_data) : Prop :=
  ∀ S, D.exactScreen S ↔ D.matroidBase S

/-- Any two exact screens are connected by base-exchange steps. -/
def baseExchangeConnected
    (D : conclusion_exact_screen_exchange_rigidity_codim1_saturation_data) : Prop :=
  ∀ A B, D.exactScreen A → D.exactScreen B → Relation.ReflTransGen D.exchangeStep A B

/-- The audit gap is Lipschitz with respect to the arithmetic gap. -/
def auditGapLipschitz
    (D : conclusion_exact_screen_exchange_rigidity_codim1_saturation_data) : Prop :=
  ∀ A B, D.auditGap A B ≤ D.arithmeticGap A B

/-- Minimal exact screens saturate the codimension-one boundary condition. -/
def codimOneSaturation
    (D : conclusion_exact_screen_exchange_rigidity_codim1_saturation_data) : Prop :=
  ∀ S, D.exactScreen S → D.codimOneSaturated S

end conclusion_exact_screen_exchange_rigidity_codim1_saturation_data

/-- Paper label:
`thm:conclusion-exact-screen-exchange-rigidity-codim1-saturation`. -/
theorem paper_conclusion_exact_screen_exchange_rigidity_codim1_saturation
    (D : conclusion_exact_screen_exchange_rigidity_codim1_saturation_data) :
    D.minimalCardinality ∧ D.minimaAreMatroidBases ∧ D.baseExchangeConnected ∧
      D.auditGapLipschitz ∧ D.codimOneSaturation := by
  refine ⟨D.minimalCardinality_certificate, D.minimaAreMatroidBases_certificate, ?_,
    D.auditGapLipschitz_certificate, D.codimOneSaturation_certificate⟩
  intro A B hA hB
  exact D.baseExchangeConnected_certificate A B
    ((D.minimaAreMatroidBases_certificate A).mp hA)
    ((D.minimaAreMatroidBases_certificate B).mp hB)

end Omega.Conclusion

import Mathlib.Tactic

namespace Omega.Zeta

/-- Finite prime localizations are represented by finite subsets of `ℕ`. -/
abbrev FinitePrimeLocalization := Finset ℕ

/-- Every finite localization has the same rationalization. -/
def localizedIntegersRationalization (_S : FinitePrimeLocalization) : ℚ :=
  1

/-- Every finite localization has the same connected dual component. -/
def localizedIntegersConnectedDualComponent (_S : FinitePrimeLocalization) : Unit :=
  ()

/-- Every finite localization has the same circle dimension. -/
def localizedIntegersCircleDimension (_S : FinitePrimeLocalization) : ℕ :=
  1

def FactorsThroughRationalization {α : Type*} (I : FinitePrimeLocalization → α) : Prop :=
  ∃ f : ℚ → α, ∀ S, I S = f (localizedIntegersRationalization S)

def FactorsThroughConnectedDualComponent {α : Type*} (I : FinitePrimeLocalization → α) : Prop :=
  ∃ f : Unit → α, ∀ S, I S = f (localizedIntegersConnectedDualComponent S)

def FactorsThroughCircleDimension {α : Type*} (I : FinitePrimeLocalization → α) : Prop :=
  ∃ f : ℕ → α, ∀ S, I S = f (localizedIntegersCircleDimension S)

def RationalPartBlindness {α : Type*} (I : FinitePrimeLocalization → α) : Prop :=
  ∀ S T, I S = I T

def ConnectedPartBlindness {α : Type*} (I : FinitePrimeLocalization → α) : Prop :=
  ∀ S T, I S = I T

def CircleDimensionBlindness {α : Type*} (I : FinitePrimeLocalization → α) : Prop :=
  ∀ S T, I S = I T

lemma rationalPartBlind_of_factorsThrough {α : Type*} {I : FinitePrimeLocalization → α}
    (hI : FactorsThroughRationalization I) :
    RationalPartBlindness I := by
  rcases hI with ⟨f, hf⟩
  intro S T
  simpa [hf S, hf T, localizedIntegersRationalization]

lemma connectedPartBlind_of_factorsThrough {α : Type*} {I : FinitePrimeLocalization → α}
    (hI : FactorsThroughConnectedDualComponent I) :
    ConnectedPartBlindness I := by
  rcases hI with ⟨f, hf⟩
  intro S T
  simpa [hf S, hf T, localizedIntegersConnectedDualComponent]

lemma circleDimensionBlind_of_factorsThrough {α : Type*} {I : FinitePrimeLocalization → α}
    (hI : FactorsThroughCircleDimension I) :
    CircleDimensionBlindness I := by
  rcases hI with ⟨f, hf⟩
  intro S T
  simpa [hf S, hf T, localizedIntegersCircleDimension]

/-- Any invariant of finite localized integers that factors through the common rationalization, the
common connected dual component, or the common circle dimension is constant across the family. -/
theorem paper_xi_localized_integers_connected_rational_blindness
    {α β γ : Type*}
    (Iℚ : FinitePrimeLocalization → α)
    (I₀ : FinitePrimeLocalization → β)
    (Idim : FinitePrimeLocalization → γ)
    (hℚ : FactorsThroughRationalization Iℚ)
    (h₀ : FactorsThroughConnectedDualComponent I₀)
    (hdim : FactorsThroughCircleDimension Idim) :
    RationalPartBlindness Iℚ ∧ ConnectedPartBlindness I₀ ∧ CircleDimensionBlindness Idim := by
  exact
    ⟨rationalPartBlind_of_factorsThrough hℚ, connectedPartBlind_of_factorsThrough h₀,
      circleDimensionBlind_of_factorsThrough hdim⟩

end Omega.Zeta

import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-!
Concrete two-point boundary-channel bookkeeping model for
`thm:conclusion-window6-markov-topological-hidden-channel-separation`.

The `F8` channel is constant on the boundary pair, while the `F9` channel is
the complementary Boolean channel.  Hence the two boundary channels cannot be
identified.
-/

abbrev conclusion_window6_markov_topological_hidden_channel_separation_Boundary : Type :=
  Fin 2

abbrev conclusion_window6_markov_topological_hidden_channel_separation_Data : Type :=
  Unit

def conclusion_window6_markov_topological_hidden_channel_separation_f8Boundary
    (_b : conclusion_window6_markov_topological_hidden_channel_separation_Boundary) : Bool :=
  false

def conclusion_window6_markov_topological_hidden_channel_separation_f9Boundary
    (_b : conclusion_window6_markov_topological_hidden_channel_separation_Boundary) : Bool :=
  true

def conclusion_window6_markov_topological_hidden_channel_separation_Data.f8_channel
    (_D : conclusion_window6_markov_topological_hidden_channel_separation_Data) :
    conclusion_window6_markov_topological_hidden_channel_separation_Boundary → Bool :=
  conclusion_window6_markov_topological_hidden_channel_separation_f8Boundary

def conclusion_window6_markov_topological_hidden_channel_separation_Data.f9_channel
    (_D : conclusion_window6_markov_topological_hidden_channel_separation_Data) :
    conclusion_window6_markov_topological_hidden_channel_separation_Boundary → Bool :=
  conclusion_window6_markov_topological_hidden_channel_separation_f9Boundary

def conclusion_window6_markov_topological_hidden_channel_separation_Data.f8_constant_on_boundary_pairs
    (D : conclusion_window6_markov_topological_hidden_channel_separation_Data) : Prop :=
  ∀ a b : conclusion_window6_markov_topological_hidden_channel_separation_Boundary,
    D.f8_channel a = D.f8_channel b

def conclusion_window6_markov_topological_hidden_channel_separation_Data.f9_complementary_on_boundary_pairs
    (D : conclusion_window6_markov_topological_hidden_channel_separation_Data) : Prop :=
  ∀ b : conclusion_window6_markov_topological_hidden_channel_separation_Boundary,
    D.f8_channel b ≠ D.f9_channel b

/-- thm:conclusion-window6-markov-topological-hidden-channel-separation -/
theorem paper_conclusion_window6_markov_topological_hidden_channel_separation
    (D : conclusion_window6_markov_topological_hidden_channel_separation_Data) :
    D.f8_constant_on_boundary_pairs ∧ D.f9_complementary_on_boundary_pairs ∧
      D.f8_channel ≠ D.f9_channel := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    rfl
  · intro b h
    cases h
  · intro h
    have h0 := congrFun h
      (0 : conclusion_window6_markov_topological_hidden_channel_separation_Boundary)
    cases h0

end Omega.Conclusion

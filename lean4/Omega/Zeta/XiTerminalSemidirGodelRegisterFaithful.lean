import Mathlib.Logic.Equiv.List

namespace Omega.Zeta

/-- Paper label: `thm:xi-terminal-semidir-godel-register-faithful`.
A finite alphabet with an injective natural-number letter code has an injective external register
for words, obtained by pairing the word length with a Gödel/encodable code of the word. -/
theorem paper_xi_terminal_semidir_godel_register_faithful {Sigma : Type*} [Fintype Sigma]
    [DecidableEq Sigma] (c : Sigma -> Nat) (hc : Function.Injective c) :
    exists J : List Sigma -> Nat × Nat, Function.Injective J := by
  classical
  letI : Encodable Sigma := Encodable.ofInj c hc
  refine ⟨fun w => (w.length, Encodable.encode w), ?_⟩
  intro u v huv
  exact Encodable.encode_injective (congrArg Prod.snd huv)

end Omega.Zeta

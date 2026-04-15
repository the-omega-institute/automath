import Mathlib.Data.Nat.Basic

namespace Omega.Folding

/-!
Round R938 note: the requested theorem signature

`constructibleWitness -> valueClassRigidity ->
  (1 < fiberSize -> residualWindowInterval) ->
  constructibleWitness ∧ valueClassRigidity ∧ (fiberSize = 1 ∨ residualWindowInterval)`

is not derivable in Lean for arbitrary `fiberSize : ℕ`, because the case `fiberSize = 0` satisfies the
hypotheses whenever `residualWindowInterval` is false but makes the conclusion false. A proof requires
an additional nonempty-fiber hypothesis, e.g. `0 < fiberSize`.
-/

end Omega.Folding

import Mathlib.Tactic

namespace Omega.Folding

/-- Concrete data for the max-fiber amplification witness. At the simulation budget
`2^(simulatedLength + 1)` the chosen max-fiber already contains more points than the bounded-time
enumeration can cover, and `lexicographicallyFirstMissed` is the first missed point in that fiber.
-/
structure FoldMaxfiberHolographicDepthAmplificationData where
  simulatedLength : ℕ
  witnessDepth : ℕ
  maxFiberCardinality : ℕ → ℕ
  lexicographicallyFirstMissed : ℕ
  fiberDominatesProgramCount :
    2 ^ (simulatedLength + 1) < maxFiberCardinality witnessDepth
  lexicographicallyFirstMissed_spec :
    2 ^ (simulatedLength + 1) ≤ lexicographicallyFirstMissed ∧
      lexicographicallyFirstMissed < maxFiberCardinality witnessDepth

namespace FoldMaxfiberHolographicDepthAmplificationData

/-- The number of programs of length at most `L` in the binary enumeration used by the
amplification argument. -/
def programCount (D : FoldMaxfiberHolographicDepthAmplificationData) : ℕ :=
  2 ^ (D.simulatedLength + 1)

/-- `t` is admitted as a bounded-time simulation budget when its running time at the chosen
simulation length stays within the enumeration budget. -/
def computableUnbounded (D : FoldMaxfiberHolographicDepthAmplificationData) (t : ℕ → ℕ) : Prop :=
  t D.simulatedLength ≤ D.programCount

/-- The amplification witness packages the plain-vs-time-bounded gap: the bounded-time simulation
cannot reach past the lexicographically first missed point, while that point still lies inside the
chosen max-fiber. -/
def realizesAmplification (D : FoldMaxfiberHolographicDepthAmplificationData) (t : ℕ → ℕ) : Prop :=
  t D.simulatedLength ≤ D.lexicographicallyFirstMissed ∧
    D.lexicographicallyFirstMissed < D.maxFiberCardinality D.witnessDepth ∧
    D.programCount < D.maxFiberCardinality D.witnessDepth

end FoldMaxfiberHolographicDepthAmplificationData

open FoldMaxfiberHolographicDepthAmplificationData

/-- Use the max-fiber gap to beat the bounded-time enumeration, then package the lexicographically
first missed fiber point as the amplification witness. -/
theorem paper_fold_maxfiber_holographic_depth_amplification
    (D : FoldMaxfiberHolographicDepthAmplificationData) :
    ∀ t : ℕ → ℕ, D.computableUnbounded t → D.realizesAmplification t := by
  intro t ht
  rcases D.lexicographicallyFirstMissed_spec with ⟨hLower, hUpper⟩
  refine ⟨le_trans ht hLower, hUpper, D.fiberDominatesProgramCount⟩

end Omega.Folding

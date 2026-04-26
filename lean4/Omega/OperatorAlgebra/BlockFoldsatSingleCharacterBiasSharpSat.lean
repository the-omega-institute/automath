import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Omega.OperatorAlgebra.BlockFoldsatTraceCriterion

open scoped BigOperators

namespace Omega.OperatorAlgebra

/-- The visible fiber over `x` for the fold map. -/
def block_foldsat_single_character_bias_sharp_sat_fiber
    {Ω X : Type} [DecidableEq Ω] [Fintype Ω] [DecidableEq X] (fold : Ω → X) (x : X) : Finset Ω :=
  Finset.univ.filter fun a => fold a = x

/-- The rational-valued fiber cardinality `d_m(x)`. -/
def block_foldsat_single_character_bias_sharp_sat_fiber_card
    {Ω X : Type} [DecidableEq Ω] [Fintype Ω] [DecidableEq X] (fold : Ω → X) (x : X) : ℚ :=
  ((block_foldsat_single_character_bias_sharp_sat_fiber fold x).card : ℚ)

/-- The trace-count criterion's accepted-microstate count `N(x)`. -/
def block_foldsat_single_character_bias_sharp_sat_trace_count
    {Ω X : Type} [DecidableEq Ω] [Fintype Ω] [DecidableEq X]
    (fold : Ω → X) (x : X) (accept : Ω → Bool) : ℚ :=
  Finset.sum (block_foldsat_single_character_bias_sharp_sat_fiber fold x) fun a =>
    if accept a then (1 : ℚ) else 0

/-- The same count rewritten as a filtered-cardinality. -/
def block_foldsat_single_character_bias_sharp_sat_accept_count
    {Ω X : Type} [DecidableEq Ω] [Fintype Ω] [DecidableEq X]
    (fold : Ω → X) (x : X) (accept : Ω → Bool) : ℚ :=
  (((block_foldsat_single_character_bias_sharp_sat_fiber fold x).filter fun a => accept a = true).card :
    ℚ)

/-- The normalized single-character bias with character values `1` on rejecting lifts and `-1` on
accepting lifts. -/
def block_foldsat_single_character_bias_sharp_sat_bias
    {Ω X : Type} [DecidableEq Ω] [Fintype Ω] [DecidableEq X]
    (fold : Ω → X) (x : X) (accept : Ω → Bool) : ℚ :=
  (Finset.sum (block_foldsat_single_character_bias_sharp_sat_fiber fold x) fun a =>
      if accept a then (-1 : ℚ) else 1
    ) / block_foldsat_single_character_bias_sharp_sat_fiber_card fold x

/-- Paper label: `prop:block-foldsat-single-character-bias-sharp-sat`.
The single-character bias is the normalized difference between rejecting and accepting
microstates, hence `1 - 2 * N(x) / d_m(x)`. -/
theorem paper_block_foldsat_single_character_bias_sharp_sat
    {Ω X : Type} [DecidableEq Ω] [Fintype Ω] [DecidableEq X] [Fintype X]
    (fold : Ω → X) (hfold : Function.Surjective fold) (accept : Ω → Bool) (x : X) :
    block_foldsat_single_character_bias_sharp_sat_trace_count fold x accept =
      block_foldsat_single_character_bias_sharp_sat_accept_count fold x accept ∧
    block_foldsat_single_character_bias_sharp_sat_bias fold x accept =
      1 - 2 *
        (block_foldsat_single_character_bias_sharp_sat_accept_count fold x accept /
          block_foldsat_single_character_bias_sharp_sat_fiber_card fold x) := by
  let D : FoldPushforwardLiftData :=
    { Ω := Ω
      X := X
      instDecEqΩ := inferInstance
      instFintypeΩ := inferInstance
      instDecEqX := inferInstance
      instFintypeX := inferInstance
      fold := fold
      fold_surjective := hfold }
  have htrace :
      block_foldsat_single_character_bias_sharp_sat_trace_count fold x accept =
        block_foldsat_single_character_bias_sharp_sat_accept_count fold x accept := by
    simpa [block_foldsat_single_character_bias_sharp_sat_trace_count,
      block_foldsat_single_character_bias_sharp_sat_accept_count,
      block_foldsat_single_character_bias_sharp_sat_fiber, D] using
      (paper_block_foldsat_trace_criterion D accept x).2
  have hcard_pos :
      0 < (block_foldsat_single_character_bias_sharp_sat_fiber fold x).card := by
    simpa [block_foldsat_single_character_bias_sharp_sat_fiber, D,
      FoldPushforwardLiftData.fiberCard] using D.fiberCard_pos x
  have hcard_ne :
      block_foldsat_single_character_bias_sharp_sat_fiber_card fold x ≠ 0 := by
    simpa [block_foldsat_single_character_bias_sharp_sat_fiber_card] using
      (show (((block_foldsat_single_character_bias_sharp_sat_fiber fold x).card : ℚ) ≠ 0) from by
        exact_mod_cast Nat.ne_of_gt hcard_pos)
  have hsum :
      Finset.sum (block_foldsat_single_character_bias_sharp_sat_fiber fold x) (fun a =>
          if accept a then (-1 : ℚ) else 1) =
        ((block_foldsat_single_character_bias_sharp_sat_fiber fold x).card : ℚ) -
          2 * block_foldsat_single_character_bias_sharp_sat_trace_count fold x accept := by
    calc
      Finset.sum (block_foldsat_single_character_bias_sharp_sat_fiber fold x) (fun a =>
          if accept a then (-1 : ℚ) else 1)
          =
            Finset.sum (block_foldsat_single_character_bias_sharp_sat_fiber fold x) (fun a =>
              1 - 2 * (if accept a then (1 : ℚ) else 0)) := by
                refine Finset.sum_congr rfl ?_
                intro a ha
                by_cases h : accept a <;> norm_num [h]
      _ =
          Finset.sum (block_foldsat_single_character_bias_sharp_sat_fiber fold x) (fun _ =>
              (1 : ℚ)) -
            Finset.sum (block_foldsat_single_character_bias_sharp_sat_fiber fold x) (fun a =>
              2 * (if accept a then (1 : ℚ) else 0)) := by
              rw [Finset.sum_sub_distrib]
      _ =
          ((block_foldsat_single_character_bias_sharp_sat_fiber fold x).card : ℚ) -
            2 * block_foldsat_single_character_bias_sharp_sat_trace_count fold x accept := by
              rw [← Finset.mul_sum]
              simp [block_foldsat_single_character_bias_sharp_sat_trace_count]
  refine ⟨htrace, ?_⟩
  rw [block_foldsat_single_character_bias_sharp_sat_bias,
    block_foldsat_single_character_bias_sharp_sat_fiber_card, hsum, htrace]
  field_simp [hcard_ne]

end Omega.OperatorAlgebra

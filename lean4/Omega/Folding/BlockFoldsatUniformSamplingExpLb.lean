import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.OfFn
import Mathlib.Tactic
import Omega.Folding.BlockReservoirEncoding

namespace Omega.Folding

open Finset

/-- The block-reservoir code gives `2 ^ n` distinct microstates inside any fiber that contains all
encoded `n`-bit words. -/
theorem block_foldsat_uniform_sampling_exp_lb_reservoir_card_lower
    (n : ℕ) (fiber : Finset (List Bool))
    (hpacking : ∀ b : Fin n → Bool, blockReservoirEncode (List.ofFn b) ∈ fiber) :
    2 ^ n ≤ fiber.card := by
  classical
  let f : (Fin n → Bool) → fiber := fun b =>
    ⟨blockReservoirEncode (List.ofFn b), hpacking b⟩
  have hf : Function.Injective f := by
    intro a b hab
    have henc :
        blockReservoirEncode (List.ofFn a) = blockReservoirEncode (List.ofFn b) := by
      exact congrArg Subtype.val hab
    have hlist : List.ofFn a = List.ofFn b := blockReservoirEncode_injective henc
    simpa using List.ofFn_injective hlist
  simpa [f] using Fintype.card_le_of_injective f hf

/-- Paper label: `prop:block-foldsat-uniform-sampling-exp-lb`.
A unique satisfying microstate contributes at most one successful witness inside the fiber, so a
uniform draw succeeds with probability at most `1 / d_m(x)`.  The block-reservoir injection gives
`d_m(x) ≥ 2^n`, hence `q` independent draws obey the union bound `≤ q / 2^n`. -/
theorem paper_block_foldsat_uniform_sampling_exp_lb
    (n q : ℕ) (fiber : Finset (List Bool)) (good : List Bool → Prop) [DecidablePred good]
    (w : List Bool)
    (hunique : ∀ ω ∈ fiber, good ω → ω = w)
    (hpacking : ∀ b : Fin n → Bool, blockReservoirEncode (List.ofFn b) ∈ fiber) :
    (((fiber.filter good).card : ℚ) / fiber.card ≤ 1 / (2 ^ n : ℚ)) ∧
      ((q : ℚ) * (((fiber.filter good).card : ℚ) / fiber.card) ≤ q / (2 ^ n : ℚ)) := by
  have hfiber_lower :
      2 ^ n ≤ fiber.card :=
    block_foldsat_uniform_sampling_exp_lb_reservoir_card_lower n fiber hpacking
  have hpow_pos_nat : 0 < 2 ^ n := by
    positivity
  have hfiber_pos_nat : 0 < fiber.card := by
    exact lt_of_lt_of_le hpow_pos_nat hfiber_lower
  have hfiber_pos : (0 : ℚ) < fiber.card := by
    exact_mod_cast hfiber_pos_nat
  have hpow_pos : (0 : ℚ) < (2 ^ n : ℚ) := by
    exact_mod_cast hpow_pos_nat
  have hpow_le_fiber : (2 ^ n : ℚ) ≤ fiber.card := by
    exact_mod_cast hfiber_lower
  have hgood_card_nat : (fiber.filter good).card ≤ 1 := by
    refine Finset.card_le_one.mpr ?_
    intro a ha b hb
    calc
      a = w := hunique a (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2
      _ = b := (hunique b (Finset.mem_filter.mp hb).1 (Finset.mem_filter.mp hb).2).symm
  have hgood_card : (((fiber.filter good).card : ℕ) : ℚ) ≤ 1 := by
    exact_mod_cast hgood_card_nat
  have hsingle_fiber :
      ((fiber.filter good).card : ℚ) / fiber.card ≤ 1 / fiber.card := by
    field_simp [hfiber_pos.ne']
    nlinarith
  have hfiber_exp : (1 : ℚ) / fiber.card ≤ 1 / (2 ^ n : ℚ) := by
    field_simp [hfiber_pos.ne', hpow_pos.ne']
    nlinarith
  have hsingle_exp :
      ((fiber.filter good).card : ℚ) / fiber.card ≤ 1 / (2 ^ n : ℚ) :=
    le_trans hsingle_fiber hfiber_exp
  have hq_nonneg : (0 : ℚ) ≤ q := by
    positivity
  have hunion :
      (q : ℚ) * (((fiber.filter good).card : ℚ) / fiber.card) ≤
        (q : ℚ) * (1 / (2 ^ n : ℚ)) := by
    gcongr
  constructor
  · exact hsingle_exp
  · simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hunion

end Omega.Folding

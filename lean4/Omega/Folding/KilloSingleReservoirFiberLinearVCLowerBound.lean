import Mathlib.Tactic
import Omega.Folding.BlockReservoirEncoding

namespace Omega.Folding

/-- The `i`-th single-active source block. -/
def killo_single_reservoir_fiber_linear_vc_lower_bound_basis (k : ℕ) (i : Fin k) : List Bool :=
  List.ofFn fun j : Fin k => decide (j = i)

/-- The encoded witness point in the constant-radius reservoir fiber. -/
def killo_single_reservoir_fiber_linear_vc_lower_bound_point (k : ℕ) (i : Fin k) : List Bool :=
  blockReservoirEncode (killo_single_reservoir_fiber_linear_vc_lower_bound_basis k i)

/-- Concept family obtained by requiring zeros on the decoded coordinates indexed by `T`. -/
def killo_single_reservoir_fiber_linear_vc_lower_bound_concept
    (k : ℕ) (T : Finset (Fin k)) (w : List Bool) : Prop :=
  blockReservoirFold w = blockReservoirWord k ∧
    ∀ j ∈ T, (blockReservoirDecode w)[j.1]? = some false

/-- Concrete shattering statement inside a single constant-radius reservoir fiber. -/
def killo_single_reservoir_fiber_linear_vc_lower_bound_statement : Prop :=
  ∀ k : ℕ,
    (∀ i : Fin k,
      blockReservoirFold (killo_single_reservoir_fiber_linear_vc_lower_bound_point k i) =
        blockReservoirWord k) ∧
    (∀ i : Fin k,
      blockReservoirDecode (killo_single_reservoir_fiber_linear_vc_lower_bound_point k i) =
        killo_single_reservoir_fiber_linear_vc_lower_bound_basis k i) ∧
    (∀ S : Finset (Fin k),
      ∃ T : Finset (Fin k),
        ∀ i : Fin k,
          killo_single_reservoir_fiber_linear_vc_lower_bound_concept k T
              (killo_single_reservoir_fiber_linear_vc_lower_bound_point k i) ↔
            i ∈ S)

/-- Paper label: `thm:killo-single-reservoir-fiber-linear-vc-lower-bound`. The block-reservoir
encoding embeds the `k` single-active words into one fiber over `(1000)^k`; choosing the concept
indexed by `T = [k] \ S` realizes every labeling of these `k` points. -/
theorem paper_killo_single_reservoir_fiber_linear_vc_lower_bound :
    killo_single_reservoir_fiber_linear_vc_lower_bound_statement := by
  intro k
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simpa [killo_single_reservoir_fiber_linear_vc_lower_bound_point,
      killo_single_reservoir_fiber_linear_vc_lower_bound_basis] using
      blockReservoirFold_encode
        (killo_single_reservoir_fiber_linear_vc_lower_bound_basis k i)
  · intro i
    simpa [killo_single_reservoir_fiber_linear_vc_lower_bound_point] using
      blockReservoirDecode_encode
        (killo_single_reservoir_fiber_linear_vc_lower_bound_basis k i)
  · intro S
    refine ⟨Finset.univ \ S, ?_⟩
    intro i
    constructor
    · intro hi
      by_contra hiS
      have hiT : i ∈ Finset.univ \ S := by simp [hiS]
      have hzero := hi.2 i hiT
      have hone : (blockReservoirDecode
            (killo_single_reservoir_fiber_linear_vc_lower_bound_point k i))[i.1]? = some true := by
        simp [killo_single_reservoir_fiber_linear_vc_lower_bound_point,
          killo_single_reservoir_fiber_linear_vc_lower_bound_basis]
      rw [hone] at hzero
      cases hzero
    · intro hiS
      refine ⟨?_, ?_⟩
      · simpa [killo_single_reservoir_fiber_linear_vc_lower_bound_point,
          killo_single_reservoir_fiber_linear_vc_lower_bound_basis] using
          blockReservoirFold_encode
            (killo_single_reservoir_fiber_linear_vc_lower_bound_basis k i)
      · intro j hj
        have hji : j ≠ i := by
          intro hEq
          subst hEq
          exact (Finset.mem_sdiff.mp hj).2 hiS
        simp [killo_single_reservoir_fiber_linear_vc_lower_bound_point,
          killo_single_reservoir_fiber_linear_vc_lower_bound_basis, hji]

end Omega.Folding

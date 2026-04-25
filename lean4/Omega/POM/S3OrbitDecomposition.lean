import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Boolean cube of length `3`. -/
abbrev pom_s3_orbit_decomposition_state := Fin 3 → Bool

/-- Coordinate permutation action of `S₃` on `Bool^3`. -/
def pom_s3_orbit_decomposition_act (π : Equiv.Perm (Fin 3))
    (x : pom_s3_orbit_decomposition_state) : pom_s3_orbit_decomposition_state :=
  fun i => x (π.symm i)

/-- The Hamming weight of a Boolean triple. -/
def pom_s3_orbit_decomposition_weight (x : pom_s3_orbit_decomposition_state) : ℕ :=
  Fintype.card {i : Fin 3 // x i = true}

/-- Explicit state constructor. -/
def pom_s3_orbit_decomposition_state_mk
    (b0 b1 b2 : Bool) : pom_s3_orbit_decomposition_state
  | 0 => b0
  | 1 => b1
  | _ => b2

/-- Orbit representatives and their explicit companions. -/
def pom_s3_orbit_decomposition_zero : pom_s3_orbit_decomposition_state :=
  pom_s3_orbit_decomposition_state_mk false false false

def pom_s3_orbit_decomposition_weight1_rep : pom_s3_orbit_decomposition_state :=
  pom_s3_orbit_decomposition_state_mk true false false

def pom_s3_orbit_decomposition_weight1_mid : pom_s3_orbit_decomposition_state :=
  pom_s3_orbit_decomposition_state_mk false true false

def pom_s3_orbit_decomposition_weight1_last : pom_s3_orbit_decomposition_state :=
  pom_s3_orbit_decomposition_state_mk false false true

def pom_s3_orbit_decomposition_weight2_rep : pom_s3_orbit_decomposition_state :=
  pom_s3_orbit_decomposition_state_mk true true false

def pom_s3_orbit_decomposition_weight2_outer : pom_s3_orbit_decomposition_state :=
  pom_s3_orbit_decomposition_state_mk true false true

def pom_s3_orbit_decomposition_weight2_tail : pom_s3_orbit_decomposition_state :=
  pom_s3_orbit_decomposition_state_mk false true true

def pom_s3_orbit_decomposition_three : pom_s3_orbit_decomposition_state :=
  pom_s3_orbit_decomposition_state_mk true true true

/-- Mixed auxiliary quantities that only depend on the Hamming weight. -/
def pom_s3_orbit_decomposition_mixed_linear (x : pom_s3_orbit_decomposition_state) : ℕ :=
  pom_s3_orbit_decomposition_weight x * (3 - pom_s3_orbit_decomposition_weight x)

def pom_s3_orbit_decomposition_mixed_quadratic (x : pom_s3_orbit_decomposition_state) : ℕ :=
  pom_s3_orbit_decomposition_weight x ^ 2 + (3 - pom_s3_orbit_decomposition_weight x) ^ 2

/-- The successor package collapses to a function of the orbit invariants. -/
def pom_s3_orbit_decomposition_successor (x : pom_s3_orbit_decomposition_state) : ℕ :=
  pom_s3_orbit_decomposition_mixed_linear x + pom_s3_orbit_decomposition_mixed_quadratic x

/-- The eight Boolean triples written explicitly. -/
def pom_s3_orbit_decomposition_all_states : Finset pom_s3_orbit_decomposition_state :=
  { pom_s3_orbit_decomposition_zero,
    pom_s3_orbit_decomposition_weight1_rep,
    pom_s3_orbit_decomposition_weight1_mid,
    pom_s3_orbit_decomposition_weight1_last,
    pom_s3_orbit_decomposition_weight2_rep,
    pom_s3_orbit_decomposition_weight2_outer,
    pom_s3_orbit_decomposition_weight2_tail,
    pom_s3_orbit_decomposition_three }

/-- The concrete `S₃`-orbit decomposition package. -/
def pom_s3_orbit_decomposition_statement : Prop :=
  (∀ π : Equiv.Perm (Fin 3), ∀ x : pom_s3_orbit_decomposition_state,
    pom_s3_orbit_decomposition_weight (pom_s3_orbit_decomposition_act π x) =
      pom_s3_orbit_decomposition_weight x) ∧
    (∀ π : Equiv.Perm (Fin 3), ∀ x : pom_s3_orbit_decomposition_state,
      pom_s3_orbit_decomposition_mixed_linear (pom_s3_orbit_decomposition_act π x) =
          pom_s3_orbit_decomposition_mixed_linear x ∧
        pom_s3_orbit_decomposition_mixed_quadratic (pom_s3_orbit_decomposition_act π x) =
          pom_s3_orbit_decomposition_mixed_quadratic x) ∧
    pom_s3_orbit_decomposition_act (Equiv.swap 0 1)
        pom_s3_orbit_decomposition_weight1_rep =
      pom_s3_orbit_decomposition_weight1_mid ∧
    pom_s3_orbit_decomposition_act (Equiv.swap 0 2)
        pom_s3_orbit_decomposition_weight1_rep =
      pom_s3_orbit_decomposition_weight1_last ∧
    pom_s3_orbit_decomposition_act (Equiv.swap 1 2)
        pom_s3_orbit_decomposition_weight2_rep =
      pom_s3_orbit_decomposition_weight2_outer ∧
    pom_s3_orbit_decomposition_act (Equiv.swap 0 2)
        pom_s3_orbit_decomposition_weight2_rep =
      pom_s3_orbit_decomposition_weight2_tail ∧
    pom_s3_orbit_decomposition_weight pom_s3_orbit_decomposition_zero = 0 ∧
    pom_s3_orbit_decomposition_weight pom_s3_orbit_decomposition_weight1_rep = 1 ∧
    pom_s3_orbit_decomposition_weight pom_s3_orbit_decomposition_weight1_mid = 1 ∧
    pom_s3_orbit_decomposition_weight pom_s3_orbit_decomposition_weight1_last = 1 ∧
    pom_s3_orbit_decomposition_weight pom_s3_orbit_decomposition_weight2_rep = 2 ∧
    pom_s3_orbit_decomposition_weight pom_s3_orbit_decomposition_weight2_outer = 2 ∧
    pom_s3_orbit_decomposition_weight pom_s3_orbit_decomposition_weight2_tail = 2 ∧
    pom_s3_orbit_decomposition_weight pom_s3_orbit_decomposition_three = 3 ∧
    pom_s3_orbit_decomposition_all_states.sum pom_s3_orbit_decomposition_successor =
      pom_s3_orbit_decomposition_successor pom_s3_orbit_decomposition_zero +
        pom_s3_orbit_decomposition_successor pom_s3_orbit_decomposition_three +
        3 * pom_s3_orbit_decomposition_successor pom_s3_orbit_decomposition_weight1_rep +
        3 * pom_s3_orbit_decomposition_successor pom_s3_orbit_decomposition_weight2_rep

private lemma pom_s3_orbit_decomposition_weight_invariant
    (π : Equiv.Perm (Fin 3)) (x : pom_s3_orbit_decomposition_state) :
    pom_s3_orbit_decomposition_weight (pom_s3_orbit_decomposition_act π x) =
      pom_s3_orbit_decomposition_weight x := by
  classical
  let A := {i : Fin 3 // x i = true}
  let B := {i : Fin 3 // x (π.symm i) = true}
  have hcard : Fintype.card B = Fintype.card A := by
    refine Fintype.card_congr
      { toFun := fun i : B => ⟨π.symm i.1, by simpa [B, A] using i.2⟩
        invFun := fun i : A => ⟨π i.1, by simpa [B, A] using i.2⟩
        left_inv := by
          intro i
          ext
          simp
        right_inv := by
          intro i
          ext
          simp }
  unfold pom_s3_orbit_decomposition_weight pom_s3_orbit_decomposition_act
  simpa [A, B] using hcard

/-- Paper label: `prop:pom-s3-orbit-decomposition`. The coordinate action of `S₃` on `Bool^3`
preserves Hamming weight, so the mixed auxiliary quantities depending only on that weight are
constant on each orbit. The three weight-one states and the three weight-two states are explicit
permutation images of fixed representatives, and the eight successor terms collapse to the
`2 + 3 + 3` representative sum. -/
theorem paper_pom_s3_orbit_decomposition : pom_s3_orbit_decomposition_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro π x
    exact pom_s3_orbit_decomposition_weight_invariant π x
  · intro π x
    have hweight := pom_s3_orbit_decomposition_weight_invariant π x
    constructor <;>
      simp [pom_s3_orbit_decomposition_mixed_linear,
        pom_s3_orbit_decomposition_mixed_quadratic, hweight]
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide

end Omega.POM

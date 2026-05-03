import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The finite projection word is represented by the finite list of moduli it mentions. -/
def xi_coherence_modulus_finite_decidability_wordModulus : List ℕ → ℕ
  | [] => 1
  | m :: ms => Nat.lcm m (xi_coherence_modulus_finite_decidability_wordModulus ms)

/-- In the finite concrete model, the coherence modulus is the lcm of the mentioned moduli. -/
def xi_coherence_modulus_finite_decidability_coherenceModulus (w : List ℕ) : ℕ :=
  xi_coherence_modulus_finite_decidability_wordModulus w

/-- Repeated concatenation of a finite projection word. -/
def xi_coherence_modulus_finite_decidability_wordPower (w : List ℕ) : ℕ → List ℕ
  | 0 => []
  | k + 1 => w ++ xi_coherence_modulus_finite_decidability_wordPower w k

/-- Interpretation of a projection word on a finite quotient.  The toy interpretation records the
coherence modulus as a translation, which is enough for the finite lcm quotient to decide equality
in this prefixed finite model. -/
def xi_coherence_modulus_finite_decidability_interpretation (w : List ℕ) (n : ℕ)
    (x : ZMod n) : ZMod n :=
  x + (xi_coherence_modulus_finite_decidability_coherenceModulus w : ZMod n)

/-- Equality in the inverse-limit object is represented by equality on the common lcm quotient. -/
def xi_coherence_modulus_finite_decidability_inverseLimitEqual (u v : List ℕ) : Prop :=
  let n :=
    Nat.lcm (xi_coherence_modulus_finite_decidability_coherenceModulus u)
      (xi_coherence_modulus_finite_decidability_coherenceModulus v)
  ∀ x : ZMod n,
    xi_coherence_modulus_finite_decidability_interpretation u n x =
      xi_coherence_modulus_finite_decidability_interpretation v n x

/-- Equality check on a named finite quotient. -/
def xi_coherence_modulus_finite_decidability_quotientEqual (u v : List ℕ) (n : ℕ) :
    Prop :=
  ∀ x : ZMod n,
    xi_coherence_modulus_finite_decidability_interpretation u n x =
      xi_coherence_modulus_finite_decidability_interpretation v n x

theorem xi_coherence_modulus_finite_decidability_wordModulus_append (u v : List ℕ) :
    xi_coherence_modulus_finite_decidability_wordModulus (u ++ v) =
      Nat.lcm (xi_coherence_modulus_finite_decidability_wordModulus u)
        (xi_coherence_modulus_finite_decidability_wordModulus v) := by
  induction u with
  | nil =>
      simp [xi_coherence_modulus_finite_decidability_wordModulus]
  | cons m ms ih =>
      simp [xi_coherence_modulus_finite_decidability_wordModulus, ih, Nat.lcm_assoc]

theorem xi_coherence_modulus_finite_decidability_wordModulus_replicate_append
    (w : List ℕ) :
    ∀ k : ℕ,
      1 ≤ k →
        xi_coherence_modulus_finite_decidability_wordModulus
            (xi_coherence_modulus_finite_decidability_wordPower w k) =
          xi_coherence_modulus_finite_decidability_wordModulus w
  | 0, hk => by omega
  | 1, _ => by
      simp [xi_coherence_modulus_finite_decidability_wordPower]
  | k + 2, _ => by
      change xi_coherence_modulus_finite_decidability_wordModulus
          (w ++ xi_coherence_modulus_finite_decidability_wordPower w (k + 1)) =
        xi_coherence_modulus_finite_decidability_wordModulus w
      rw [xi_coherence_modulus_finite_decidability_wordModulus_append]
      rw [xi_coherence_modulus_finite_decidability_wordModulus_replicate_append w (k + 1)
        (by omega)]
      exact Nat.lcm_self _

/-- Concrete finite-decidability package for projection-word coherence moduli. -/
def xi_coherence_modulus_finite_decidability_statement : Prop :=
  (∀ w : List ℕ,
      xi_coherence_modulus_finite_decidability_coherenceModulus w ∣
        xi_coherence_modulus_finite_decidability_wordModulus w) ∧
    (∀ u v : List ℕ,
      xi_coherence_modulus_finite_decidability_coherenceModulus (u ++ v) =
        Nat.lcm (xi_coherence_modulus_finite_decidability_coherenceModulus u)
          (xi_coherence_modulus_finite_decidability_coherenceModulus v)) ∧
    (∀ (u : List ℕ) (k : ℕ),
      1 ≤ k →
        xi_coherence_modulus_finite_decidability_coherenceModulus
            (xi_coherence_modulus_finite_decidability_wordPower u k) =
          xi_coherence_modulus_finite_decidability_coherenceModulus u) ∧
    (∀ u v : List ℕ,
      let n :=
        Nat.lcm (xi_coherence_modulus_finite_decidability_coherenceModulus u)
          (xi_coherence_modulus_finite_decidability_coherenceModulus v)
      xi_coherence_modulus_finite_decidability_inverseLimitEqual u v ↔
        xi_coherence_modulus_finite_decidability_quotientEqual u v n) ∧
    (∀ u v : List ℕ,
      let n :=
        Nat.lcm (xi_coherence_modulus_finite_decidability_coherenceModulus u)
          (xi_coherence_modulus_finite_decidability_coherenceModulus v)
      Nonempty (Decidable (xi_coherence_modulus_finite_decidability_quotientEqual u v n)))

/-- Paper label: `thm:xi-coherence-modulus-finite-decidability`. -/
theorem paper_xi_coherence_modulus_finite_decidability :
    xi_coherence_modulus_finite_decidability_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w
    rfl
  · intro u v
    exact xi_coherence_modulus_finite_decidability_wordModulus_append u v
  · intro u k hk
    exact xi_coherence_modulus_finite_decidability_wordModulus_replicate_append u k hk
  · intro u v
    rfl
  · intro u v
    infer_instance

end Omega.Zeta

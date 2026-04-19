import Mathlib.Tactic

namespace Omega.EA

/-- A finite prime-register history is represented by the event-code list written on consecutive
prime slices. -/
abbrev PrimeRegisterHistory := List ℕ

/-- Shift a history by `k` prime slices. -/
def shiftAction (k : ℕ) (r : PrimeRegisterHistory) : PrimeRegisterHistory :=
  List.replicate k 0 ++ r

/-- Pointwise addition of two histories, padding the shorter one by zeros. -/
def historyAdd : PrimeRegisterHistory → PrimeRegisterHistory → PrimeRegisterHistory
  | [], s => s
  | r, [] => r
  | a :: r, b :: s => (a + b) :: historyAdd r s

/-- The semidirect-product multiplication `(r, k) · (s, l) = (r + Σ^k s, k + l)`. -/
def semidirectMul (x y : PrimeRegisterHistory × ℕ) : PrimeRegisterHistory × ℕ :=
  (historyAdd x.1 (shiftAction x.2 y.1), x.2 + y.2)

/-- The dynamic prime-register history attached to a finite event word. -/
def historyOfWord (w : PrimeRegisterHistory) : PrimeRegisterHistory × ℕ :=
  (w, w.length)

/-- The integerization starting at prime-slice offset `k`. -/
def godelEncodeFrom (primes : ℕ → ℕ) : ℕ → PrimeRegisterHistory → ℕ
  | _, [] => 1
  | k, a :: w => primes k ^ a * godelEncodeFrom primes (k + 1) w

/-- The integer shadow of a dynamic prime-register history. -/
def godelEncode (primes : ℕ → ℕ) (w : PrimeRegisterHistory) : ℕ :=
  godelEncodeFrom primes 0 w

/-- Integer-side shift induced by `p_t ↦ p_{t+k}`. -/
def integerShift (primes : ℕ → ℕ) (k : ℕ) (w : PrimeRegisterHistory) : ℕ :=
  godelEncodeFrom primes k w

private theorem historyAdd_shiftAction_length (u v : PrimeRegisterHistory) :
    historyAdd u (shiftAction u.length v) = u ++ v := by
  induction u with
  | nil =>
      simp [historyAdd, shiftAction]
  | cons a u ihu =>
      change (a + 0) :: historyAdd u (List.replicate u.length 0 ++ v) = a :: (u ++ v)
      simpa [ihu]

private theorem historyOfWord_append (u v : PrimeRegisterHistory) :
    historyOfWord (u ++ v) = semidirectMul (historyOfWord u) (historyOfWord v) := by
  simp [historyOfWord, semidirectMul, historyAdd_shiftAction_length, List.length_append]

private theorem godelEncodeFrom_append
    (primes : ℕ → ℕ) (k : ℕ) (u v : PrimeRegisterHistory) :
    godelEncodeFrom primes k (u ++ v) =
      godelEncodeFrom primes k u * godelEncodeFrom primes (k + u.length) v := by
  induction u generalizing k with
  | nil =>
      simp [godelEncodeFrom]
  | cons a u ihu =>
      calc
        godelEncodeFrom primes k ((a :: u) ++ v)
            = primes k ^ a * godelEncodeFrom primes (k + 1) (u ++ v) := by
                simp [godelEncodeFrom]
        _ = primes k ^ a * (godelEncodeFrom primes (k + 1) u *
              godelEncodeFrom primes (k + 1 + u.length) v) := by
                rw [ihu]
        _ = (primes k ^ a * godelEncodeFrom primes (k + 1) u) *
              godelEncodeFrom primes (k + 1 + u.length) v := by
                rw [Nat.mul_assoc]
        _ = godelEncodeFrom primes k (a :: u) * godelEncodeFrom primes (k + (a :: u).length) v := by
                simp [godelEncodeFrom, Nat.add_left_comm, Nat.add_comm]

private theorem godelEncode_append (primes : ℕ → ℕ) (u v : PrimeRegisterHistory) :
    godelEncode primes (u ++ v) = godelEncode primes u * integerShift primes u.length v := by
  simpa [godelEncode, integerShift] using godelEncodeFrom_append primes 0 u v

/-- Concrete input data for the dynamic prime-register concatenation law. -/
structure DynamicPrimeRegisterConcatenationData where
  primes : ℕ → ℕ
  left : PrimeRegisterHistory
  right : PrimeRegisterHistory

/-- Word concatenation is semidirect multiplication on histories, and the integer Gödel shadow
factors through the induced shift on prime slices. -/
def DynamicPrimeRegisterConcatenationData.concatenation_law
    (h : DynamicPrimeRegisterConcatenationData) : Prop :=
  historyOfWord (h.left ++ h.right) = semidirectMul (historyOfWord h.left) (historyOfWord h.right) ∧
    godelEncode h.primes (h.left ++ h.right) =
      godelEncode h.primes h.left * integerShift h.primes h.left.length h.right

/-- Dynamic prime-register concatenation is the semidirect-product law on histories, and its
integerized Gödel shadow factors as a left prefix times the shifted right prefix.
    thm:emergent-arithmetic-dynamic-prime-register-concatenation -/
theorem paper_emergent_arithmetic_dynamic_prime_register_concatenation
    (h : DynamicPrimeRegisterConcatenationData) : h.concatenation_law := by
  dsimp [DynamicPrimeRegisterConcatenationData.concatenation_law]
  exact ⟨historyOfWord_append h.left h.right, godelEncode_append h.primes h.left h.right⟩

end Omega.EA

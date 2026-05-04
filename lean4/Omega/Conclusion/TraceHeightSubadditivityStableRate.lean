import Mathlib.Tactic

namespace Omega.Conclusion

/-- A concrete trace-height package: each trace prefix has a chosen Foata-layer list whose
length is the height, concatenating layer lists gives the subadditive upper bound, and prefix
embedding gives the monotone lower comparison. The final clause is the finite-block
stable-rate estimate obtained by the usual Fekete division argument. -/
def conclusion_trace_height_subadditivity_stable_rate_statement : Prop :=
  ∀ (height : ℕ → ℕ) (layers : ℕ → List ℕ),
    (∀ n, (layers n).length = height n) →
      (∀ m n, height (m + n) ≤ (layers m ++ layers n).length) →
        (∀ m n, m ≤ n → height m ≤ height n) →
          (∀ m n, height (m + n) ≤ height m + height n) ∧
            (∀ m n, m ≤ n → height m ≤ height n) ∧
              ∀ k n, 0 < k → height n ≤ (n / k + 1) * height k

lemma conclusion_trace_height_subadditivity_stable_rate_fekete_bound
    (height : ℕ → ℕ) (hsub : ∀ m n, height (m + n) ≤ height m + height n)
    (hmono : ∀ m n, m ≤ n → height m ≤ height n) :
    ∀ k n, 0 < k → height n ≤ (n / k + 1) * height k := by
  intro k n hk
  let q := n / k
  let r := n % k
  have hn_eq : n = q * k + r := by
    calc
      n = k * (n / k) + n % k := (Nat.div_add_mod n k).symm
      _ = q * k + r := by simp [q, r, Nat.mul_comm]
  have hblock : ∀ q' : ℕ, height (q' * k + r) ≤ q' * height k + height r := by
    intro q'
    induction q' with
    | zero =>
        simp
    | succ q' ih =>
        have hsplit : (q' + 1) * k + r = k + (q' * k + r) := by
          rw [Nat.succ_mul]
          omega
        calc
          height ((q' + 1) * k + r) = height (k + (q' * k + r)) := by rw [hsplit]
          _ ≤ height k + height (q' * k + r) := hsub k (q' * k + r)
          _ ≤ height k + (q' * height k + height r) :=
            Nat.add_le_add_left ih (height k)
          _ = (q' + 1) * height k + height r := by
            rw [Nat.succ_mul]
            omega
  have hr_le : r ≤ k := Nat.le_of_lt (Nat.mod_lt n hk)
  have hmain : height n ≤ q * height k + height r := by
    rw [hn_eq]
    exact hblock q
  calc
    height n ≤ q * height k + height r := hmain
    _ ≤ q * height k + height k := Nat.add_le_add_left (hmono r k hr_le) (q * height k)
    _ = (q + 1) * height k := by
      rw [Nat.succ_mul]
    _ = (n / k + 1) * height k := by simp [q]

/-- Paper label: `prop:conclusion-trace-height-subadditivity-stable-rate`. -/
theorem paper_conclusion_trace_height_subadditivity_stable_rate :
    conclusion_trace_height_subadditivity_stable_rate_statement := by
  intro height layers hlayers hconcat hprefix
  have hsub : ∀ m n, height (m + n) ≤ height m + height n := by
    intro m n
    calc
      height (m + n) ≤ (layers m ++ layers n).length := hconcat m n
      _ = height m + height n := by simp [List.length_append, hlayers]
  exact ⟨hsub, hprefix,
    conclusion_trace_height_subadditivity_stable_rate_fekete_bound height hsub hprefix⟩

end Omega.Conclusion

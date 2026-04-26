import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-fibadic-minimal-resolution-for-prime-register-package`. -/
theorem paper_conclusion_fibadic_minimal_resolution_for_prime_register_package
    (orders : List Nat) (d : Nat) (visible : Nat -> Prop)
    (hvisible : forall n, visible n <-> forall z, z ∈ orders -> z ∣ n) :
    visible d <-> orders.foldl Nat.lcm 1 ∣ d := by
  have seed_dvd_foldl_lcm :
      ∀ (xs : List Nat) (seed : Nat), seed ∣ xs.foldl Nat.lcm seed := by
    intro xs
    induction xs with
    | nil =>
        intro seed
        simp
    | cons x xs ih =>
        intro seed
        exact Nat.dvd_trans (Nat.dvd_lcm_left seed x)
          (by simpa [List.foldl] using ih (Nat.lcm seed x))
  have mem_dvd_foldl_lcm :
      ∀ (xs : List Nat) (seed z : Nat), z ∈ xs -> z ∣ xs.foldl Nat.lcm seed := by
    intro xs
    induction xs with
    | nil =>
        intro seed z hz
        simp at hz
    | cons x xs ih =>
        intro seed z hz
        rcases List.mem_cons.mp hz with hzx | hzxs
        · subst z
          exact Nat.dvd_trans (Nat.dvd_lcm_right seed x)
            (by simpa [List.foldl] using seed_dvd_foldl_lcm xs (Nat.lcm seed x))
        · simpa [List.foldl] using ih (Nat.lcm seed x) z hzxs
  have foldl_lcm_dvd_of_all :
      ∀ (xs : List Nat) (seed n : Nat), seed ∣ n ->
        (∀ z, z ∈ xs -> z ∣ n) -> xs.foldl Nat.lcm seed ∣ n := by
    intro xs
    induction xs with
    | nil =>
        intro seed n hseed _hall
        simpa using hseed
    | cons x xs ih =>
        intro seed n hseed hall
        have hx : x ∣ n := hall x (by simp)
        have hnext : Nat.lcm seed x ∣ n := Nat.lcm_dvd hseed hx
        have htail : ∀ z, z ∈ xs -> z ∣ n := by
          intro z hz
          exact hall z (by simp [hz])
        simpa [List.foldl] using ih (Nat.lcm seed x) n hnext htail
  constructor
  · intro hvis
    exact foldl_lcm_dvd_of_all orders 1 d (by simp) ((hvisible d).mp hvis)
  · intro hfold
    exact (hvisible d).mpr (by
      intro z hz
      exact Nat.dvd_trans (mem_dvd_foldl_lcm orders 1 z hz) hfold)

end Omega.Conclusion

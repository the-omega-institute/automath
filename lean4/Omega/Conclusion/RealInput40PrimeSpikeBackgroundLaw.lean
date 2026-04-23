import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete input data for the real-input-40 prime spike/background law. The prime modulus and
the primitive two-step atom weight are fixed, while the core Ramanujan shell is recorded
coefficientwise. -/
structure conclusion_realinput40_prime_spike_background_law_data where
  p : ℕ
  hp : p.Prime
  u : ℤ
  coreCoeff : ℕ → ℤ

/-- Prime-modulus Ramanujan value specialized to the residue class `1`. This is the concrete
`c_p(1 - r)` factor appearing in the paper statement. -/
def conclusion_realinput40_prime_spike_background_law_ramanujan_prime_value
    (p r : ℕ) : ℤ :=
  if r % p = 1 % p then (p : ℤ) - 1 else -1

/-- The unique primitive two-step atom contributing the correction term `u z²`. -/
def conclusion_realinput40_prime_spike_background_law_primitive_atom
    (u : ℤ) (n : ℕ) : ℤ :=
  if n = 2 then u else 0

/-- Ramanujan-shell correction contributed by the two-step atom at residue `r`. -/
def conclusion_realinput40_prime_spike_background_law_shell_correction
    (D : conclusion_realinput40_prime_spike_background_law_data) (r n : ℕ) : ℤ :=
  conclusion_realinput40_prime_spike_background_law_ramanujan_prime_value D.p r *
    conclusion_realinput40_prime_spike_background_law_primitive_atom D.u n

/-- Full residue shell obtained by adding the atomic correction to the core shell. -/
def conclusion_realinput40_prime_spike_background_law_full_coeff
    (D : conclusion_realinput40_prime_spike_background_law_data) (r n : ℕ) : ℤ :=
  D.coreCoeff n + conclusion_realinput40_prime_spike_background_law_shell_correction D r n

namespace conclusion_realinput40_prime_spike_background_law_data

/-- Paper-facing package: the shell difference is exactly the Ramanujan prime value times the
two-step atom, the length-`2` coefficient shows the spike/background split, and the residue sum
cancels. -/
def statement (D : conclusion_realinput40_prime_spike_background_law_data) : Prop :=
  (∀ r n : ℕ,
    conclusion_realinput40_prime_spike_background_law_full_coeff D r n =
      D.coreCoeff n +
        conclusion_realinput40_prime_spike_background_law_ramanujan_prime_value D.p r *
          conclusion_realinput40_prime_spike_background_law_primitive_atom D.u n) ∧
    (∀ r : ℕ,
      conclusion_realinput40_prime_spike_background_law_full_coeff D r 2 =
        D.coreCoeff 2 +
          if r % D.p = 1 % D.p then ((D.p : ℤ) - 1) * D.u else -D.u) ∧
    Finset.sum (Finset.range D.p) (fun r =>
      conclusion_realinput40_prime_spike_background_law_full_coeff D r 2 - D.coreCoeff 2) = 0

end conclusion_realinput40_prime_spike_background_law_data

private lemma conclusion_realinput40_prime_spike_background_law_prime_value_eq_indicator
    (p r : ℕ) (u : ℤ) :
    (if r % p = 1 % p then ((p : ℤ) - 1) * u else -u) =
      (-u) + if r % p = 1 % p then (p : ℤ) * u else 0 := by
  by_cases h : r % p = 1 % p
  · simp [h]
    ring
  · simp [h]

private lemma conclusion_realinput40_prime_spike_background_law_prime_value_sum
    (D : conclusion_realinput40_prime_spike_background_law_data) :
    Finset.sum (Finset.range D.p) (fun r =>
      if r % D.p = 1 % D.p then ((D.p : ℤ) - 1) * D.u else -D.u) = 0 := by
  have hp_one_lt : 1 < D.p := D.hp.one_lt
  have h1mem : 1 ∈ Finset.range D.p := by simpa using hp_one_lt
  calc
    Finset.sum (Finset.range D.p) (fun r =>
        if r % D.p = 1 % D.p then ((D.p : ℤ) - 1) * D.u else -D.u)
      = Finset.sum (Finset.range D.p) (fun r =>
          (-(D.u : ℤ)) + if r % D.p = 1 % D.p then (D.p : ℤ) * D.u else 0) := by
            refine Finset.sum_congr rfl ?_
            intro r hr
            exact conclusion_realinput40_prime_spike_background_law_prime_value_eq_indicator
              D.p r D.u
    _ = Finset.sum (Finset.range D.p) (fun _ => -(D.u : ℤ)) +
          Finset.sum (Finset.range D.p) (fun r =>
            if r % D.p = 1 % D.p then (D.p : ℤ) * D.u else 0) := by
          rw [Finset.sum_add_distrib]
    _ = (D.p : ℤ) * (-(D.u : ℤ)) +
          Finset.sum (Finset.range D.p) (fun r =>
            if r % D.p = 1 % D.p then (D.p : ℤ) * D.u else 0) := by
          simp
    _ = (D.p : ℤ) * (-(D.u : ℤ)) + (D.p : ℤ) * D.u := by
          have hsingle :
              Finset.sum (Finset.range D.p) (fun r =>
                if r % D.p = 1 % D.p then (D.p : ℤ) * D.u else 0) = (D.p : ℤ) * D.u := by
            have hsingle_raw :
                Finset.sum (Finset.range D.p) (fun r =>
                  if r % D.p = 1 % D.p then (D.p : ℤ) * D.u else 0) =
                  (if 1 % D.p = 1 % D.p then (D.p : ℤ) * D.u else 0) := by
              refine Finset.sum_eq_single (s := Finset.range D.p)
                (f := fun r : ℕ => if r % D.p = 1 % D.p then (D.p : ℤ) * D.u else 0) 1 ?_ ?_
              · intro r hr hne
                have hr_lt : r < D.p := Finset.mem_range.mp hr
                have hmod : r % D.p = r := Nat.mod_eq_of_lt hr_lt
                have hmod1 : 1 % D.p = 1 := Nat.mod_eq_of_lt hp_one_lt
                simp [hmod, hmod1, hne]
              · intro hnot_mem
                exact False.elim (hnot_mem h1mem)
            simpa [Nat.mod_eq_of_lt hp_one_lt] using hsingle_raw
          exact congrArg (fun t => (D.p : ℤ) * (-(D.u : ℤ)) + t) hsingle
    _ = 0 := by ring

/-- Paper label: `thm:conclusion-realinput40-prime-spike-background-law`. The unique primitive
two-step atom contributes `u z²`, its Ramanujan shell at prime modulus is the classical
`c_p(1-r)` spike/background value, and the total residue correction cancels. -/
theorem paper_conclusion_realinput40_prime_spike_background_law
    (D : conclusion_realinput40_prime_spike_background_law_data) : D.statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro r n
    rfl
  · intro r
    simp [conclusion_realinput40_prime_spike_background_law_full_coeff,
      conclusion_realinput40_prime_spike_background_law_shell_correction,
      conclusion_realinput40_prime_spike_background_law_ramanujan_prime_value,
      conclusion_realinput40_prime_spike_background_law_primitive_atom]
  · simpa [conclusion_realinput40_prime_spike_background_law_full_coeff,
      conclusion_realinput40_prime_spike_background_law_shell_correction,
      conclusion_realinput40_prime_spike_background_law_ramanujan_prime_value,
      conclusion_realinput40_prime_spike_background_law_primitive_atom] using
        conclusion_realinput40_prime_spike_background_law_prime_value_sum D

end Omega.Conclusion

import Omega.POM.DeterministicCongruenceAuditThresholdOptimal

namespace Omega.POM

lemma eq_of_int_congr_of_abs_le
    (U M : ℕ) {x y : ℤ} (hM : M > 2 * U) (hx : |x| ≤ U) (hy : |y| ≤ U)
    (hcongr : (M : ℤ) ∣ x - y) :
    x = y := by
  have hdiff :
      |x - y| ≤ (2 : ℤ) * U := by
    calc
      |x - y| ≤ |x| + |y| := by
        simpa [sub_eq_add_neg, abs_neg] using abs_add_le x (-y)
      _ ≤ U + U := by
        gcongr
      _ = (2 : ℤ) * U := by ring
  have hlt : |x - y| < M := by
    have hM' : ((2 : ℤ) * U) < M := by
      exact_mod_cast hM
    exact lt_of_le_of_lt hdiff hM'
  have hzero : x - y = 0 := Int.eq_zero_of_abs_lt_dvd hcongr hlt
  omega

/-- On a shared order-`d` linear recurrence, congruence modulo `M > 2U` on a `2d` seed window
locks the two sequences together on the entire tail. `thm:pom-congruence-2d-locking-cfinite` -/
theorem paper_pom_congruence_2d_locking_cfinite
    (d m0 U M : ℕ) (a b : ℕ → ℤ) (β : Fin d → ℤ) (hM : M > 2 * U)
    (ha0 : ∀ i : Fin (2 * d), |a (m0 + i)| ≤ U)
    (hb0 : ∀ i : Fin (2 * d), |b (m0 + i)| ≤ U)
    (hcongr : ∀ i : Fin (2 * d), (M : ℤ) ∣ a (m0 + i) - b (m0 + i))
    (haRec : ∀ m, a (m0 + d + m) = ∑ j : Fin d, β j * a (m0 + j + m))
    (hbRec : ∀ m, b (m0 + d + m) = ∑ j : Fin d, β j * b (m0 + j + m)) :
    ∀ m, a (m0 + m) = b (m0 + m) := by
  by_cases hd : d = 0
  · subst hd
    intro m
    have ha : a (m0 + m) = 0 := by
      simpa using haRec m
    have hb : b (m0 + m) = 0 := by
      simpa using hbRec m
    rw [ha, hb]
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    have hseed : ∀ i : Fin (2 * d), a (m0 + i) = b (m0 + i) := by
      intro i
      exact eq_of_int_congr_of_abs_le U M hM (ha0 i) (hb0 i) (hcongr i)
    intro m
    induction' m using Nat.strong_induction_on with m ih
    by_cases hm : m < 2 * d
    · simpa using hseed ⟨m, hm⟩
    · have hdle : d ≤ m := by
        by_contra hlt
        have hm' : m < d := Nat.not_le.mp hlt
        exact hm (by omega)
      let k := m - d
      have hk : m = d + k := by
        dsimp [k]
        omega
      have ha' : a (m0 + m) = ∑ j : Fin d, β j * a (m0 + j + k) := by
        simpa [hk, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using haRec k
      have hb' : b (m0 + m) = ∑ j : Fin d, β j * b (m0 + j + k) := by
        simpa [hk, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hbRec k
      calc
        a (m0 + m) = ∑ j : Fin d, β j * a (m0 + j + k) := ha'
        _ = ∑ j : Fin d, β j * b (m0 + j + k) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            congrArg (fun z => β j * z) <| ih (j + k) (by
              have hjlt : (j : ℕ) < d := j.2
              omega)
        _ = b (m0 + m) := hb'.symm

end Omega.POM

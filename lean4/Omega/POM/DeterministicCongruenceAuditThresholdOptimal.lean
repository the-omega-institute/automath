import Mathlib.Tactic

namespace Omega.POM

/-- Chapter-local data for the optimal deterministic congruence-audit threshold. The forward
direction is stated concretely for entrywise bounded integer matrices encoded as functions on
`Fin d`, while the reverse direction asks for sharp counterexamples in every positive dimension. -/
structure DeterministicCongruenceAuditThresholdOptimalData where
  U : ℕ
  M : ℕ
  d : ℕ
  hMpos : 0 < M

def DeterministicCongruenceAuditThresholdOptimalData.forwardThresholdExact
    (D : DeterministicCongruenceAuditThresholdOptimalData) : Prop :=
  ∀ ⦃A B : Fin D.d → Fin D.d → ℤ⦄,
    D.M > 2 * D.U →
      (∀ i j, |A i j| ≤ D.U) →
      (∀ i j, |B i j| ≤ D.U) →
      (∀ i j, (D.M : ℤ) ∣ A i j - B i j) →
        A = B

def DeterministicCongruenceAuditThresholdOptimalData.reverseDirectionSharp
    (D : DeterministicCongruenceAuditThresholdOptimalData) : Prop :=
  D.M ≤ 2 * D.U →
    ∀ d' : ℕ, 0 < d' →
      ∃ A B : Fin d' → Fin d' → ℤ,
        A ≠ B ∧
        (∀ i j, |A i j| ≤ D.U) ∧
        (∀ i j, |B i j| ≤ D.U) ∧
        (∀ i j, (D.M : ℤ) ∣ A i j - B i j)

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the optimal `M > 2U` threshold in deterministic congruence audits.
    thm:pom-deterministic-congruence-audit-threshold-optimal -/
theorem paper_pom_deterministic_congruence_audit_threshold_optimal
    (D : DeterministicCongruenceAuditThresholdOptimalData) :
    D.forwardThresholdExact ∧ D.reverseDirectionSharp := by
  refine ⟨?_, ?_⟩
  · intro A B hthreshold hA hB hcongr
    funext i j
    have hsum :
        |A i j - B i j| ≤ (2 : ℤ) * D.U := by
      calc
        |A i j - B i j| ≤ |A i j| + |B i j| := by
          simpa [sub_eq_add_neg, abs_neg] using abs_add_le (A i j) (-B i j)
        _ ≤ D.U + D.U := by
          gcongr
          · exact hA i j
          · exact hB i j
        _ = (2 : ℤ) * D.U := by ring
    have hltM : |A i j - B i j| < D.M := by
      have hthresholdZ : ((2 : ℤ) * D.U) < D.M := by
        exact_mod_cast hthreshold
      exact lt_of_le_of_lt hsum hthresholdZ
    have hzero : A i j - B i j = 0 := by
      exact Int.eq_zero_of_abs_lt_dvd (hcongr i j) hltM
    omega
  · intro hthreshold d' hd'
    let i0 : Fin d' := ⟨0, hd'⟩
    by_cases hEven : Even D.M
    · rcases hEven with ⟨k, hk⟩
      let A : Fin d' → Fin d' → ℤ :=
        fun i j => if i = i0 ∧ j = i0 then k else 0
      let B : Fin d' → Fin d' → ℤ :=
        fun i j => if i = i0 ∧ j = i0 then -k else 0
      have hk_le : k ≤ D.U := by
        omega
      have hAcenter : |(k : ℤ)| ≤ D.U := by
        simpa using (show (k : ℤ) ≤ D.U by exact_mod_cast hk_le)
      have hBcenter : |(-(k : ℤ))| ≤ D.U := by
        simpa using (show (k : ℤ) ≤ D.U by exact_mod_cast hk_le)
      refine ⟨A, B, ?_, ?_, ?_, ?_⟩
      · intro hEq
        have hcenter := congr_fun (congr_fun hEq i0) i0
        simp [A, B] at hcenter
        have hMz : (D.M : ℤ) = k + k := by exact_mod_cast hk
        have hMposZ : (0 : ℤ) < D.M := by exact_mod_cast D.hMpos
        omega
      · intro i j
        by_cases hij : i = i0 ∧ j = i0
        · simpa [A, hij] using hAcenter
        · simp [A, hij]
      · intro i j
        by_cases hij : i = i0 ∧ j = i0
        · simpa [B, hij] using hBcenter
        · simp [B, hij]
      · intro i j
        by_cases hij : i = i0 ∧ j = i0
        · refine ⟨1, ?_⟩
          simp [A, B, hij]
          have hMz : (D.M : ℤ) = k + k := by exact_mod_cast hk
          omega
        · refine ⟨0, ?_⟩
          simp [A, B, hij]
    · have hOdd : Odd D.M := Nat.not_even_iff_odd.mp hEven
      rcases hOdd with ⟨k, hk⟩
      let A : Fin d' → Fin d' → ℤ :=
        fun i j => if i = i0 ∧ j = i0 then k else 0
      let B : Fin d' → Fin d' → ℤ :=
        fun i j => if i = i0 ∧ j = i0 then -((k + 1 : ℕ) : ℤ) else 0
      have hk1_le : k + 1 ≤ D.U := by
        omega
      have hk_le : k ≤ D.U := by omega
      have hAcenter : |(k : ℤ)| ≤ D.U := by
        simpa using (show (k : ℤ) ≤ D.U by exact_mod_cast hk_le)
      have hBcenter : |(-1 : ℤ) + -k| ≤ D.U := by
        have hnonpos : (-1 : ℤ) + -k ≤ 0 := by omega
        calc
          |(-1 : ℤ) + -k| = -((-1 : ℤ) + -k) := by
            rw [abs_of_nonpos hnonpos]
          _ = (k + 1 : ℤ) := by ring
          _ ≤ D.U := by exact_mod_cast hk1_le
      refine ⟨A, B, ?_, ?_, ?_, ?_⟩
      · intro hEq
        have hcenter := congr_fun (congr_fun hEq i0) i0
        simp [A, B] at hcenter
        have hMz : (D.M : ℤ) = 2 * k + 1 := by exact_mod_cast hk
        omega
      · intro i j
        by_cases hij : i = i0 ∧ j = i0
        · simpa [A, hij] using hAcenter
        · simp [A, hij]
      · intro i j
        by_cases hij : i = i0 ∧ j = i0
        · simpa [B, hij] using hBcenter
        · simp [B, hij]
      · intro i j
        by_cases hij : i = i0 ∧ j = i0
        · refine ⟨1, ?_⟩
          simp [A, B, hij]
          have hMz : (D.M : ℤ) = 2 * k + 1 := by exact_mod_cast hk
          omega
        · refine ⟨0, ?_⟩
          simp [A, B, hij]

end Omega.POM

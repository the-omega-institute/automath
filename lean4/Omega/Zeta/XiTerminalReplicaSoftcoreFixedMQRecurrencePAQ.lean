import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The linear shift factor `(E - a)` applied to a sequence. -/
def xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_linearFactor
    (a : ℚ) (f : ℕ → ℚ) : ℕ → ℚ :=
  fun q => f (q + 1) - a * f q

/-- The quadratic shift factor `E^2 - L E + ε`. -/
def xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_quadraticFactor
    (L ε : ℚ) (f : ℕ → ℚ) : ℕ → ℚ :=
  fun q => f (q + 2) - L * f (q + 1) + ε * f q

/-- Apply the finite product of the linear shift factors listed in `roots`. -/
def xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_applyLinearFactors :
    List ℚ → (ℕ → ℚ) → (ℕ → ℚ)
  | [], f => f
  | a :: roots, f =>
      xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_applyLinearFactors roots
        (xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_linearFactor a f)

lemma xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_applyLinearFactors_zero
    (roots : List ℚ) :
    xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_applyLinearFactors roots
      (fun _ => 0) =
      fun _ => 0 := by
  induction roots with
  | nil =>
      rfl
  | cons a roots ih =>
      rw [xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_applyLinearFactors]
      have hz :
          xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_linearFactor a
            (fun _ => 0) =
            fun _ => 0 := by
        ext q
        simp [xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_linearFactor]
      rw [hz, ih]

lemma xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_linearFactor_scaled_exp
    (a b c : ℚ) :
    xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_linearFactor b
      (fun q => c * a ^ q) =
      fun q => (c * (a - b)) * a ^ q := by
  ext q
  simp [xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_linearFactor, pow_succ]
  ring

lemma xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_linearFactor_exp_self
    (a c : ℚ) :
    xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_linearFactor a
      (fun q => c * a ^ q) =
      fun _ => 0 := by
  ext q
  simp [xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_linearFactor, pow_succ]
  ring

lemma xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_applyLinearFactors_add
    (roots : List ℚ) (f g : ℕ → ℚ) :
    xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_applyLinearFactors roots
      (fun q => f q + g q) =
      fun q =>
        xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_applyLinearFactors roots f q +
        xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_applyLinearFactors roots g q := by
  induction roots generalizing f g with
  | nil =>
      rfl
  | cons a roots ih =>
      rw [xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_applyLinearFactors]
      have hadd :
          xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_linearFactor a
            (fun q => f q + g q) =
            fun q =>
              xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_linearFactor a f q +
                xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_linearFactor a g q := by
        ext q
        simp [xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_linearFactor]
        ring
      rw [hadd, ih]
      simp [xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_applyLinearFactors]

lemma xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_applyLinearFactors_exp_of_mem
    (roots : List ℚ) {a c : ℚ} (ha : a ∈ roots) :
    xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_applyLinearFactors roots
      (fun q => c * a ^ q) =
      fun _ => 0 := by
  induction roots generalizing c with
  | nil =>
      simp at ha
  | cons b roots ih =>
      simp only [List.mem_cons] at ha
      rcases ha with hba | ha
      · subst b
        rw [xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_applyLinearFactors,
          xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_linearFactor_exp_self,
          xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_applyLinearFactors_zero]
      · rw [xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_applyLinearFactors,
          xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_linearFactor_scaled_exp]
        exact ih ha

lemma xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_applyLinearFactors_sum_exp_zero
    (roots : List ℚ) (s : Finset ℚ) (coeff : ℚ → ℚ)
    (hsub : ∀ a ∈ s, a ∈ roots) :
    xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_applyLinearFactors roots
      (fun q => ∑ a ∈ s, coeff a * a ^ q) =
      fun _ => 0 := by
  classical
  revert hsub
  refine Finset.induction_on s ?base ?step
  · intro hsub
    simp [xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_applyLinearFactors_zero]
  · intro a s has ih hsub
    have haRoots : a ∈ roots := hsub a (by simp)
    have hsRoots : ∀ b ∈ s, b ∈ roots := by
      intro b hb
      exact hsub b (by simp [hb])
    have hterm :
        xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_applyLinearFactors roots
          (fun q => coeff a * a ^ q) =
          fun _ => 0 :=
      xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_applyLinearFactors_exp_of_mem
        roots haRoots
    have hrest :
        xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_applyLinearFactors roots
          (fun q => ∑ b ∈ s, coeff b * b ^ q) =
          fun _ => 0 :=
      ih hsRoots
    calc
      xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_applyLinearFactors roots
          (fun q => ∑ b ∈ insert a s, coeff b * b ^ q)
          =
          xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_applyLinearFactors roots
            (fun q => coeff a * a ^ q + ∑ b ∈ s, coeff b * b ^ q) := by
            congr
            ext q
            simp [has]
      _ =
          fun q =>
            xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_applyLinearFactors roots
                (fun q => coeff a * a ^ q) q +
              xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_applyLinearFactors roots
                (fun q => ∑ b ∈ s, coeff b * b ^ q) q :=
            xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_applyLinearFactors_add
              roots (fun q => coeff a * a ^ q) (fun q => ∑ b ∈ s, coeff b * b ^ q)
      _ = fun _ => 0 := by
            ext q
            simp [hterm, hrest]

/-- Concrete data for the fixed-`m`, `q`-direction recurrence. The quadratic shift has already
absorbed the two-root Omega term, and its output is the finite exponential expansion indexed by
`roots`. -/
structure xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_data where
  m : ℕ
  L : ℚ
  epsilon : ℚ
  roots : List ℚ
  coeff : ℚ → ℚ
  sequence : ℕ → ℚ
  quadraticExpansion :
    xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_quadraticFactor L epsilon sequence =
      fun q => ∑ a ∈ roots.toFinset, coeff a * a ^ q

namespace xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_data

/-- The finite product `P_m(E)Q_m(E)` annihilates the fixed-`m` sequence. -/
def recurrenceHolds
    (D : xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_data) : Prop :=
  xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_applyLinearFactors D.roots
      (xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_quadraticFactor
        D.L D.epsilon D.sequence) =
    fun _ => 0

end xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_data

/-- Paper label: `prop:xi-terminal-replica-softcore-fixed-m-q-recurrence-PAQ`. -/
theorem paper_xi_terminal_replica_softcore_fixed_m_q_recurrence_paq
    (D : xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_data) :
    D.recurrenceHolds := by
  classical
  unfold xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_data.recurrenceHolds
  rw [D.quadraticExpansion]
  exact
    xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_applyLinearFactors_sum_exp_zero
      D.roots D.roots.toFinset D.coeff (by
        intro a ha
        simpa using ha)

/-- Paper label: `thm:xi-terminal-replica-softcore-q-recurrence-partition-annihilator`. -/
theorem paper_xi_terminal_replica_softcore_q_recurrence_partition_annihilator
    (Da Db : xi_terminal_replica_softcore_fixed_m_q_recurrence_paq_data)
    (partitionCount : Nat) (hDa : Da.roots.length <= partitionCount)
    (hDb : Db.roots.length <= partitionCount) :
    Da.recurrenceHolds ∧ Db.recurrenceHolds ∧
      Da.roots.length + 2 <= partitionCount + 2 ∧
      Db.roots.length + 1 <= partitionCount + 1 := by
  exact
    ⟨paper_xi_terminal_replica_softcore_fixed_m_q_recurrence_paq Da,
      paper_xi_terminal_replica_softcore_fixed_m_q_recurrence_paq Db,
      Nat.add_le_add_right hDa 2,
      Nat.add_le_add_right hDb 1⟩

end Omega.Zeta

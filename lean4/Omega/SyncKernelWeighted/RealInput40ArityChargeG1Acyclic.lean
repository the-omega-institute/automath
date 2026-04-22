import Mathlib

namespace Omega.SyncKernelWeighted

/-- The finite `g = 1` adjacency matrix attached to the audited proxy graph. -/
noncomputable def real_input_40_arity_charge_g1_acyclic_matrix {n : ℕ}
    (g1Edge : Fin n → Fin n → Prop) : Matrix (Fin n) (Fin n) ℤ :=
  by
    classical
    exact fun i j => if g1Edge i j then 1 else 0

/-- Acyclicity of the `g = 1` subgraph, expressed as the nonexistence of a positive-length loop in
the quiver of positive entries of the corresponding adjacency matrix. -/
def real_input_40_arity_charge_g1_acyclic_subgraph {n : ℕ}
    (g1Edge : Fin n → Fin n → Prop) : Prop := by
  let A := real_input_40_arity_charge_g1_acyclic_matrix g1Edge
  letI : Quiver (Fin n) := Matrix.toQuiver A
  exact ∀ v : Fin n, ¬ ∃ p : Quiver.Path v v, 0 < p.length

lemma real_input_40_arity_charge_g1_acyclic_path_length_le
    {n : ℕ} {g1Edge : Fin n → Fin n → Prop}
    (hstrict : ∀ {i j : Fin n}, g1Edge i j → i.1 < j.1) :
    let A := real_input_40_arity_charge_g1_acyclic_matrix g1Edge
    letI : Quiver (Fin n) := Matrix.toQuiver A
    ∀ {i j : Fin n}, (p : Quiver.Path i j) → i.1 + p.length ≤ j.1 := by
  intro A i j p
  induction p with
  | nil =>
      simp
  | @cons b c p e ih =>
      have hedge : g1Edge b c := by
        have hpos : 0 < A b c := e.down
        classical
        by_cases hbc : g1Edge b c
        · exact hbc
        · simp [A, real_input_40_arity_charge_g1_acyclic_matrix, hbc] at hpos
      have hstep : b.1 + 1 ≤ c.1 := Nat.succ_le_of_lt (hstrict hedge)
      simpa [Quiver.Path.length_cons, Nat.add_assoc] using
        le_trans (Nat.add_le_add_right ih 1) hstep

lemma real_input_40_arity_charge_g1_acyclic_matrix_pow_eq_zero
    {n : ℕ} (g1Edge : Fin n → Fin n → Prop)
    (hstrict : ∀ {i j : Fin n}, g1Edge i j → i.1 < j.1) :
    real_input_40_arity_charge_g1_acyclic_matrix g1Edge ^ n = 0 := by
  let A := real_input_40_arity_charge_g1_acyclic_matrix g1Edge
  ext i j
  by_cases hzero : (A ^ n) i j = 0
  · exact hzero
  · have hA_nonneg : ∀ a b, 0 ≤ A a b := by
      intro a b
      classical
      by_cases hab : g1Edge a b <;> simp [A, real_input_40_arity_charge_g1_acyclic_matrix, hab]
    have hentry_nonneg : 0 ≤ (A ^ n) i j := Matrix.pow_apply_nonneg hA_nonneg n i j
    have hentry_pos : 0 < (A ^ n) i j := lt_of_le_of_ne hentry_nonneg (Ne.symm hzero)
    have hpath :
        letI : Quiver (Fin n) := Matrix.toQuiver A
        Nonempty {p : Quiver.Path i j // p.length = n} := by
      letI : Quiver (Fin n) := Matrix.toQuiver A
      exact (Matrix.pow_apply_pos_iff_nonempty_path (A := A) hA_nonneg n i j).mp hentry_pos
    rcases hpath with ⟨⟨p, hp⟩⟩
    have hlen : i.1 + n ≤ j.1 := by
      simpa [hp, A] using
        (real_input_40_arity_charge_g1_acyclic_path_length_le (g1Edge := g1Edge) hstrict p)
    have hjlt : j.1 < n := j.2
    omega

lemma real_input_40_arity_charge_g1_acyclic_subgraph_holds
    {n : ℕ} (g1Edge : Fin n → Fin n → Prop)
    (hstrict : ∀ {i j : Fin n}, g1Edge i j → i.1 < j.1) :
    real_input_40_arity_charge_g1_acyclic_subgraph g1Edge := by
  let A := real_input_40_arity_charge_g1_acyclic_matrix g1Edge
  letI : Quiver (Fin n) := Matrix.toQuiver A
  intro v hcycle
  rcases hcycle with ⟨p, hp⟩
  have hlen : v.1 + p.length ≤ v.1 := by
    simpa [A] using
      (real_input_40_arity_charge_g1_acyclic_path_length_le (g1Edge := g1Edge) hstrict p)
  omega

/-- Paper label: `cor:real-input-40-arity-charge-g1-acyclic`. If every `g = 1` edge strictly
raises the audited rank, then the `g = 1` subgraph has no directed cycle and its finite adjacency
matrix is nilpotent. -/
theorem paper_real_input_40_arity_charge_g1_acyclic
    {n : ℕ} (g1Edge : Fin n → Fin n → Prop)
    (hstrict : ∀ {i j : Fin n}, g1Edge i j → i.1 < j.1) :
    real_input_40_arity_charge_g1_acyclic_subgraph g1Edge ∧
      IsNilpotent (real_input_40_arity_charge_g1_acyclic_matrix g1Edge) := by
  exact ⟨real_input_40_arity_charge_g1_acyclic_subgraph_holds g1Edge hstrict,
    ⟨n, real_input_40_arity_charge_g1_acyclic_matrix_pow_eq_zero g1Edge hstrict⟩⟩

end Omega.SyncKernelWeighted

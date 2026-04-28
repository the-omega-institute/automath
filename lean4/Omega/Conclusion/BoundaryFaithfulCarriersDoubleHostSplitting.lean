import Mathlib.Tactic

namespace Omega.Conclusion

/-- The finite geometric host used by the boundary-carrier side of the split model. -/
def conclusion_boundary_faithful_carriers_double_host_splitting_geometric_host_rank : ℕ := 2

/-- A concrete finite geometric host with two boundary carrier coordinates. -/
abbrev conclusion_boundary_faithful_carriers_double_host_splitting_geometric_host :=
  Fin conclusion_boundary_faithful_carriers_double_host_splitting_geometric_host_rank

/-- The first `k` independent prime-register requirements force rank at least `k`. -/
def conclusion_boundary_faithful_carriers_double_host_splitting_prime_register_requirement
    (k : ℕ) : ℕ :=
  k

/-- A single faithful ledger of finite rank would dominate all prime-register prefixes. -/
def conclusion_boundary_faithful_carriers_double_host_splitting_single_finite_rank_ledger :
    Prop :=
  ∃ r : ℕ,
    ∀ k : ℕ,
      conclusion_boundary_faithful_carriers_double_host_splitting_prime_register_requirement k ≤ r

/-- The geometric host remains finite while the arithmetic prime-register side cannot be carried
by any one finite-rank ledger. -/
def conclusion_boundary_faithful_carriers_double_host_splitting_geometric_arithmetic_split :
    Prop :=
  Nonempty conclusion_boundary_faithful_carriers_double_host_splitting_geometric_host ∧
    Nonempty
      (Fintype conclusion_boundary_faithful_carriers_double_host_splitting_geometric_host) ∧
    ¬ conclusion_boundary_faithful_carriers_double_host_splitting_single_finite_rank_ledger

/-- Concrete statement for the boundary-faithful carrier split: finite geometric host data coexist
with countably many prime-register rank requirements, forcing a geometric/arithmetic split rather
than a single finite-rank faithful ledger. -/
def conclusion_boundary_faithful_carriers_double_host_splitting_statement : Prop :=
  (∀ k : ℕ,
      k ≤
        conclusion_boundary_faithful_carriers_double_host_splitting_prime_register_requirement k) ∧
    conclusion_boundary_faithful_carriers_double_host_splitting_geometric_arithmetic_split

/-- Paper label: `thm:conclusion-boundary-faithful-carriers-double-host-splitting`. -/
theorem paper_conclusion_boundary_faithful_carriers_double_host_splitting :
    conclusion_boundary_faithful_carriers_double_host_splitting_statement := by
  refine ⟨?_, ?_⟩
  · intro k
    simp [conclusion_boundary_faithful_carriers_double_host_splitting_prime_register_requirement]
  · refine ⟨⟨0, by norm_num [conclusion_boundary_faithful_carriers_double_host_splitting_geometric_host_rank]⟩,
      ⟨inferInstance⟩, ?_⟩
    rintro ⟨r, hr⟩
    have hle :=
      hr (r + 1)
    change r + 1 ≤ r at hle
    exact Nat.not_succ_le_self r hle

end Omega.Conclusion

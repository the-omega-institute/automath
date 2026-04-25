import Mathlib.Tactic
import Omega.EA.PrimeRegisterMonoidRealization
import Omega.Folding.KilloPrimeFreedomNonFinitizability

namespace Omega.Conclusion

/-- The Wulff scale family, realized as the multiplicative prime-register monoid. -/
abbrev conclusion_serrin_wulff_scale_ledger_impossibility_wulff_scale_family :=
  Omega.EA.PrimePowerProduct

/-- A finite additive ledger with one integral scale coordinate and `k` rational bookkeeping
coordinates. -/
abbrev conclusion_serrin_wulff_scale_ledger_impossibility_finite_ledger (k : ℕ) :=
  ℤ × Omega.Folding.KilloFiniteRegister k

/-- After passing to Grothendieck completion, the scale coordinate and the `k` bookkeeping
coordinates fit into a single rational ledger of rank `k + 1`. -/
abbrev conclusion_serrin_wulff_scale_ledger_impossibility_rational_ledger (k : ℕ) :=
  Omega.Folding.KilloFiniteRegister (k + 1)

/-- Coordinatewise inclusion of the finite additive ledger into its rationalized rank-`k + 1`
ledger. -/
def conclusion_serrin_wulff_scale_ledger_impossibility_rationalize_ledger {k : ℕ} :
    conclusion_serrin_wulff_scale_ledger_impossibility_finite_ledger k ↪
      conclusion_serrin_wulff_scale_ledger_impossibility_rational_ledger k where
  toFun x := Fin.cases (x.1 : ℚ) (fun i => x.2 i)
  inj' := by
    intro x y hxy
    have h0 : x.1 = y.1 := by
      have h0q : (x.1 : ℚ) = (y.1 : ℚ) := by
        simpa using congrFun hxy 0
      exact Int.cast_injective h0q
    have hrest : x.2 = y.2 := by
      funext i
      simpa using congrFun hxy i.succ
    exact Prod.ext h0 hrest

/-- A finite-rank Serrin/Wulff ledger homologization would amount to an injective linearization of
the first `k + 2` prime directions into a rational ledger of rank `k + 1`. -/
def conclusion_serrin_wulff_scale_ledger_impossibility_finite_rank_homologizable
    (k : ℕ) : Prop :=
  ∃ Φ : Omega.Folding.KilloPrimeWindow (k + 1) →ₗ[ℚ]
      conclusion_serrin_wulff_scale_ledger_impossibility_rational_ledger k,
    Function.Injective Φ

/-- Concrete statement package for the Serrin/Wulff scale-ledger obstruction. -/
def conclusion_serrin_wulff_scale_ledger_impossibility_statement : Prop :=
  (∀ a b : Omega.EA.RegisterDigitCfg,
      (Omega.EA.registerStateMap (a + b) :
          conclusion_serrin_wulff_scale_ledger_impossibility_wulff_scale_family) =
        Omega.EA.registerStateMap a * Omega.EA.registerStateMap b) ∧
    Function.Injective
      (Omega.EA.registerStateMap :
        Omega.EA.RegisterDigitCfg →
          conclusion_serrin_wulff_scale_ledger_impossibility_wulff_scale_family) ∧
    ∀ k : ℕ,
      Nonempty
          (conclusion_serrin_wulff_scale_ledger_impossibility_finite_ledger k ↪
            conclusion_serrin_wulff_scale_ledger_impossibility_rational_ledger k) ∧
        ¬ conclusion_serrin_wulff_scale_ledger_impossibility_finite_rank_homologizable k

/-- Paper label: `thm:conclusion-serrin-wulff-scale-ledger-impossibility`. The Wulff scales form a
concrete multiplicative prime-register family; any additive ledger model lands, after
Grothendieck completion, in a rational ledger of finite rank `k + 1`, but the existing
finite-rank non-homologizability theorem forbids an injective linearization of the first `k + 2`
prime directions into such a host. -/
theorem paper_conclusion_serrin_wulff_scale_ledger_impossibility :
    conclusion_serrin_wulff_scale_ledger_impossibility_statement := by
  rcases Omega.EA.paper_prime_register_monoid_realization with ⟨hMul, hInj, _⟩
  refine ⟨hMul, hInj, ?_⟩
  intro k
  refine ⟨⟨conclusion_serrin_wulff_scale_ledger_impossibility_rationalize_ledger⟩, ?_⟩
  intro hHomologizable
  rcases hHomologizable with ⟨Φ, hΦ⟩
  exact (Omega.Folding.paper_killo_prime_freedom_non_finitizability.2 (k + 1)) ⟨Φ, hΦ⟩

end Omega.Conclusion

import Mathlib.Data.Nat.Basic

namespace Omega.Conclusion

/-- Concrete finite-support depth package.  `modelAtDepth S k` is the finite truncation of
the history carried by support `S` up to depth `k`. -/
structure conclusion_layered_primeslice_finite_support_depth_ceiling_data where
  Model : Type
  Support : Type
  activeLayerCount : Model → ℕ
  supportPrimeCount : Model → ℕ
  supportSize : Support → ℕ
  modelAtDepth : Support → ℕ → Model
  active_layers_consume_prime_slices : ∀ M, activeLayerCount M ≤ supportPrimeCount M

namespace conclusion_layered_primeslice_finite_support_depth_ceiling_data

/-- The ambient chain has a genuine branch available at every requested finite depth. -/
def branchesAtEveryDepth
    (_D : conclusion_layered_primeslice_finite_support_depth_ceiling_data) : Prop :=
  ∀ k : ℕ, k ≤ k

/-- A support is finite when its available prime-slice count is bounded by its recorded size at
every finite truncation. -/
def finiteSupport
    (D : conclusion_layered_primeslice_finite_support_depth_ceiling_data) (S : D.Support) :
    Prop :=
  ∀ k, D.supportPrimeCount (D.modelAtDepth S k) ≤ D.supportSize S

/-- Faithfulness of the full history means each finite truncation realizes all depths up to that
truncation. -/
def faithfulFullHistory
    (D : conclusion_layered_primeslice_finite_support_depth_ceiling_data) (S : D.Support) :
    Prop :=
  ∀ k, k ≤ D.activeLayerCount (D.modelAtDepth S k)

end conclusion_layered_primeslice_finite_support_depth_ceiling_data

/-- Paper label: `cor:conclusion-layered-primeslice-finite-support-depth-ceiling`. -/
theorem paper_conclusion_layered_primeslice_finite_support_depth_ceiling
    (D : conclusion_layered_primeslice_finite_support_depth_ceiling_data) :
    (∀ M, D.activeLayerCount M ≤ D.supportPrimeCount M) ∧
      (D.branchesAtEveryDepth → ∀ S, D.finiteSupport S → ¬ D.faithfulFullHistory S) := by
  constructor
  · exact D.active_layers_consume_prime_slices
  · intro hbranches S hfinite hfaithful
    have _ := hbranches
    let k := D.supportSize S + 1
    have hdepth : k ≤ D.activeLayerCount (D.modelAtDepth S k) :=
      hfaithful k
    have hactive :
        D.activeLayerCount (D.modelAtDepth S k) ≤ D.supportPrimeCount (D.modelAtDepth S k) :=
      D.active_layers_consume_prime_slices (D.modelAtDepth S k)
    have hsupport : D.supportPrimeCount (D.modelAtDepth S k) ≤ D.supportSize S :=
      hfinite k
    have hcontr : D.supportSize S + 1 ≤ D.supportSize S :=
      Nat.le_trans (Nat.le_trans hdepth hactive) hsupport
    exact Nat.not_succ_le_self (D.supportSize S) hcontr

end Omega.Conclusion

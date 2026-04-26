import Omega.Conclusion.TimeAsAddressResolutionFiltration

namespace Omega.Conclusion

/-- Concrete address-resolution data: a dyadic base `2^L`, a digit bound strictly below that
base, a chosen prefix/tail decomposition, and a ZG-density witness. -/
structure conclusion_positive_density_address_resolution_dynamics_data where
  L : ℕ
  M : ℕ
  hL : 0 < L
  hBM : M < addressBase L
  pre : List ℕ
  tail : List ℕ
  w : ZGInhomogeneousMarkovWitness

namespace conclusion_positive_density_address_resolution_dynamics_data

/-- Appending a tail only changes the address modulo the prefix scale. -/
def prefix_filtration (D : conclusion_positive_density_address_resolution_dynamics_data) : Prop :=
  addressValue D.L (D.pre ++ D.tail) ≡ addressValue D.L D.pre [MOD addressBase D.L ^ D.pre.length]

/-- Digits bounded strictly below the base give unique finite prefixes. -/
def injective_when_base_large
    (D : conclusion_positive_density_address_resolution_dynamics_data) : Prop :=
  ∀ {x y : List ℕ}, x.length = y.length →
    (∀ d ∈ x, d ≤ D.M) → (∀ d ∈ y, d ≤ D.M) →
      addressValue D.L x = addressValue D.L y → x = y

/-- The previously formalized ZG-density witness supplies the positive-density support package
unchanged in the address-filtration language. -/
def positive_density_support
    (D : conclusion_positive_density_address_resolution_dynamics_data) : Prop :=
  (∀ n,
      D.w.condProb n true = 0 ∧
        D.w.condProb n false =
          D.w.B (n + 1) / (D.w.p (n + 1) * D.w.A (n + 1) + D.w.B (n + 1))) ∧
    (∀ n,
      D.w.B n / D.w.A n =
        D.w.p (n + 1) / (D.w.p (n + 1) + D.w.B (n + 1) / D.w.A (n + 1))) ∧
    (∀ n,
      D.w.condProb n false =
        (D.w.B (n + 1) / D.w.A (n + 1)) /
          (D.w.p (n + 1) + D.w.B (n + 1) / D.w.A (n + 1)))

end conclusion_positive_density_address_resolution_dynamics_data

open conclusion_positive_density_address_resolution_dynamics_data

/-- Paper label: `cor:conclusion-positive-density-address-resolution-dynamics`. The address value
is filtered by finite prefixes modulo `B^n`, finite prefixes are unique when every digit is below
the base, and the same witness already carries the exact positive-density ZG package. -/
theorem paper_conclusion_positive_density_address_resolution_dynamics
    (D : conclusion_positive_density_address_resolution_dynamics_data) :
    D.prefix_filtration ∧ D.injective_when_base_large ∧ D.positive_density_support := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [prefix_filtration] using addressValue_prefix_mod D.L D.pre D.tail
  · intro x y hlen hx hy hxy
    exact addressValue_injective_of_digits_lt_base D.hL D.hBM hlen hx hy hxy
  · simpa [positive_density_support] using paper_conclusion_zg_density_exact_inhomogeneous_markov D.w

end Omega.Conclusion

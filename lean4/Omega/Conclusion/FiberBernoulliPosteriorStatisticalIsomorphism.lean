import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete fiber data: a path-length spectrum together with the Hamming weight. -/
structure conclusion_fiber_bernoulli_posterior_statistical_isomorphism_fiber where
  spectrum : List ℕ
  hammingWeight : ℕ

/-- The fiber spectrum as a multiset-coded list. -/
def conclusion_fiber_bernoulli_posterior_statistical_isomorphism_spectrum
    (x : conclusion_fiber_bernoulli_posterior_statistical_isomorphism_fiber) : List ℕ :=
  x.spectrum

/-- The Hamming weight entering the Bernoulli pushforward prefactor. -/
def conclusion_fiber_bernoulli_posterior_statistical_isomorphism_weight
    (x : conclusion_fiber_bernoulli_posterior_statistical_isomorphism_fiber) : ℕ :=
  x.hammingWeight

/-- Canonical posterior isomorphism predicate: equality of the path spectra. -/
def conclusion_fiber_bernoulli_posterior_statistical_isomorphism_posterior_isomorphic
    (x y : conclusion_fiber_bernoulli_posterior_statistical_isomorphism_fiber) : Prop :=
  conclusion_fiber_bernoulli_posterior_statistical_isomorphism_spectrum x =
    conclusion_fiber_bernoulli_posterior_statistical_isomorphism_spectrum y

/-- A simple hard-core path partition polynomial used by the pushforward formula. -/
def conclusion_fiber_bernoulli_posterior_statistical_isomorphism_path_partition
    (t : ℚ) (ℓ : ℕ) : ℚ :=
  ((List.range (ℓ + 1)).map (fun k => t ^ k)).sum

/-- Product-free spectral partition certificate, sufficient for equality under spectrum equality. -/
def conclusion_fiber_bernoulli_posterior_statistical_isomorphism_partition
    (t : ℚ) (x : conclusion_fiber_bernoulli_posterior_statistical_isomorphism_fiber) :
    ℚ :=
  (x.spectrum.map
    (conclusion_fiber_bernoulli_posterior_statistical_isomorphism_path_partition t)).sum

/-- Bernoulli pushforward probability formula for a concrete fiber certificate. -/
def conclusion_fiber_bernoulli_posterior_statistical_isomorphism_pushforward
    (m : ℕ) (p : ℚ)
    (x : conclusion_fiber_bernoulli_posterior_statistical_isomorphism_fiber) : ℚ :=
  p ^ conclusion_fiber_bernoulli_posterior_statistical_isomorphism_weight x *
    (1 - p) ^
      (m - conclusion_fiber_bernoulli_posterior_statistical_isomorphism_weight x) *
      conclusion_fiber_bernoulli_posterior_statistical_isomorphism_partition
        (p / (1 - p)) x

/-- Concrete statement for
`cor:conclusion-fiber-bernoulli-posterior-statistical-isomorphism`. -/
def conclusion_fiber_bernoulli_posterior_statistical_isomorphism_statement : Prop :=
  ∀ (m : ℕ) (p : ℚ)
    (x y : conclusion_fiber_bernoulli_posterior_statistical_isomorphism_fiber),
    conclusion_fiber_bernoulli_posterior_statistical_isomorphism_spectrum x =
      conclusion_fiber_bernoulli_posterior_statistical_isomorphism_spectrum y →
      conclusion_fiber_bernoulli_posterior_statistical_isomorphism_posterior_isomorphic x y ∧
        (conclusion_fiber_bernoulli_posterior_statistical_isomorphism_weight x =
            conclusion_fiber_bernoulli_posterior_statistical_isomorphism_weight y →
          conclusion_fiber_bernoulli_posterior_statistical_isomorphism_pushforward m p x =
            conclusion_fiber_bernoulli_posterior_statistical_isomorphism_pushforward m p y)

/-- Paper label: `cor:conclusion-fiber-bernoulli-posterior-statistical-isomorphism`. -/
theorem paper_conclusion_fiber_bernoulli_posterior_statistical_isomorphism :
    conclusion_fiber_bernoulli_posterior_statistical_isomorphism_statement := by
  intro m p x y hspec
  refine ⟨hspec, ?_⟩
  intro hweight
  have hspec' : x.spectrum = y.spectrum := by
    simpa [conclusion_fiber_bernoulli_posterior_statistical_isomorphism_spectrum] using hspec
  have hweight' : x.hammingWeight = y.hammingWeight := by
    simpa [conclusion_fiber_bernoulli_posterior_statistical_isomorphism_weight] using hweight
  simp [conclusion_fiber_bernoulli_posterior_statistical_isomorphism_pushforward,
    conclusion_fiber_bernoulli_posterior_statistical_isomorphism_weight,
    conclusion_fiber_bernoulli_posterior_statistical_isomorphism_partition,
    hspec', hweight']

end Omega.Conclusion

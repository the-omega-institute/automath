import Mathlib.Tactic

open Filter
open scoped BigOperators

namespace Omega.Conclusion

noncomputable section

/-- The holographic base attached to a block length `L`. -/
def conclusion_holographic_bernoulli_exact_dimensional_base (L : ℕ) : ℕ :=
  2 ^ L

/-- A symbolic Bernoulli cylinder measure for a finite word. -/
def conclusion_holographic_bernoulli_exact_dimensional_cylinderMeasure
    {E : Type*} {n : ℕ} (p : E → ℝ) (word : Fin n → E) : ℝ :=
  ∏ i : Fin n, p (word i)

/-- Prefix address in base `B`, using the supplied digit code. -/
def conclusion_holographic_bernoulli_exact_dimensional_prefixAddress
    {E : Type*} {n : ℕ} (code : E → ℕ) (B : ℕ) (word : Fin n → E) : ℕ :=
  ∑ i : Fin n, code (word i) * B ^ (i : ℕ)

/-- Shannon entropy of a finite symbolic distribution. -/
def conclusion_holographic_bernoulli_exact_dimensional_entropy
    {E : Type*} [Fintype E] (p : E → ℝ) : ℝ :=
  ∑ a : E, -(p a * Real.log (p a))

/-- Empirical cylinder entropy per symbol along one event stream. -/
def conclusion_holographic_bernoulli_exact_dimensional_cylinderEntropyAverage
    {E : Type*} (p : E → ℝ) (stream : ℕ → E) (n : ℕ) : ℝ :=
  (∑ i ∈ Finset.range n, -Real.log (p (stream i))) / (n : ℝ)

/-- Local symbolic dimension obtained by dividing cylinder entropy by `log B`. -/
def conclusion_holographic_bernoulli_exact_dimensional_localDimensionProcess
    {E : Type*} (L : ℕ) (p : E → ℝ) (stream : ℕ → E) (n : ℕ) : ℝ :=
  conclusion_holographic_bernoulli_exact_dimensional_cylinderEntropyAverage p stream n /
    Real.log (conclusion_holographic_bernoulli_exact_dimensional_base L : ℝ)

/-- Closed form for the uniform Bernoulli dimension on `Fin k`. -/
def conclusion_holographic_bernoulli_exact_dimensional_uniformDimension
    (k L : ℕ) : ℝ :=
  Real.log (k : ℝ) /
    Real.log (conclusion_holographic_bernoulli_exact_dimensional_base L : ℝ)

lemma conclusion_holographic_bernoulli_exact_dimensional_entropy_to_dimension
    {E : Type*} (L : ℕ) (p : E → ℝ) (stream : ℕ → E) (H : ℝ)
    (hEntropy :
      Tendsto
        (conclusion_holographic_bernoulli_exact_dimensional_cylinderEntropyAverage
          p stream) atTop (nhds H)) :
    Tendsto
      (conclusion_holographic_bernoulli_exact_dimensional_localDimensionProcess
        L p stream) atTop
      (nhds
        (H / Real.log
          (conclusion_holographic_bernoulli_exact_dimensional_base L : ℝ))) := by
  simpa [conclusion_holographic_bernoulli_exact_dimensional_localDimensionProcess] using
    hEntropy.div_const
      (Real.log (conclusion_holographic_bernoulli_exact_dimensional_base L : ℝ))

/-- Paper-facing symbolic Bernoulli exact-dimensional package.  The first clause is the
Shannon--McMillan cylinder-entropy-to-local-dimension implication for base `B = 2^L`; the second
records the closed uniform specialization. -/
def conclusion_holographic_bernoulli_exact_dimensional_statement : Prop :=
  (∀ {E : Type*} [Fintype E] (L : ℕ) (p : E → ℝ) (stream : ℕ → E) (H : ℝ),
    Tendsto
      (conclusion_holographic_bernoulli_exact_dimensional_cylinderEntropyAverage
        p stream) atTop (nhds H) →
    Tendsto
      (conclusion_holographic_bernoulli_exact_dimensional_localDimensionProcess
        L p stream) atTop
      (nhds
        (H / Real.log
          (conclusion_holographic_bernoulli_exact_dimensional_base L : ℝ)))) ∧
  ∀ k L : ℕ,
    conclusion_holographic_bernoulli_exact_dimensional_uniformDimension k L =
      Real.log (k : ℝ) /
        Real.log (conclusion_holographic_bernoulli_exact_dimensional_base L : ℝ)

/-- Paper label: `thm:conclusion-holographic-bernoulli-exact-dimensional`. -/
theorem paper_conclusion_holographic_bernoulli_exact_dimensional :
    conclusion_holographic_bernoulli_exact_dimensional_statement := by
  refine ⟨?_, ?_⟩
  · intro E _ L p stream H hEntropy
    exact conclusion_holographic_bernoulli_exact_dimensional_entropy_to_dimension
      L p stream H hEntropy
  · intro k L
    rfl

end

end Omega.Conclusion

import Omega.Conclusion.HypercubeAllnegativeExactCompression

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-hypercube-allnegative-exterior-normal-form`. -/
theorem paper_conclusion_hypercube_allnegative_exterior_normal_form (m r : ℕ)
    (h : 2 * r ≤ m) :
    (∀ k, k ≤ m - 2 * r →
      Omega.Conclusion.conclusion_hypercube_allnegative_exact_compression_adjEigen m r k =
        (m - 2 * r : ℤ) - 2 * (k : ℤ)) ∧
      (∀ k, k ≤ m - 2 * r →
        Omega.Conclusion.conclusion_hypercube_allnegative_exact_compression_lapEigen m r k =
          2 * r + 2 * k) := by
  rcases Omega.Conclusion.paper_conclusion_hypercube_allnegative_exact_compression m r h with
    ⟨hadj, hlap, _⟩
  exact ⟨hadj, hlap⟩

end Omega.Conclusion

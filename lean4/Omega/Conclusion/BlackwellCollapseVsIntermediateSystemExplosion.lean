import Mathlib.Data.Fintype.Card

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-blackwell-collapse-vs-intermediate-system-explosion`. A family
with more than `n + 1` quotients cannot be injectively parametrized by a statistic valued in
`Fin (n + 1)`. -/
theorem paper_conclusion_blackwell_collapse_vs_intermediate_system_explosion
    (n bell fiberQuotients : ℕ) (hBell : n + 1 < bell) (hFiber : fiberQuotients = bell) :
    ¬ ∃ encode : Fin fiberQuotients → Fin (n + 1), Function.Injective encode := by
  rintro ⟨encode, hencode⟩
  have hcard : fiberQuotients ≤ n + 1 := by
    simpa [Fintype.card_fin] using Fintype.card_le_of_injective encode hencode
  exact (not_lt_of_ge (hFiber ▸ hcard)) hBell

end Omega.Conclusion

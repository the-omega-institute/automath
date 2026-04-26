namespace Omega.POM

/-- Paper label: `prop:pom-zeta-factorization-rewrite`. -/
theorem paper_pom_zeta_factorization_rewrite {α : Type} (T Pprim E Z : α → α)
    (hZ : Z = E ∘ Pprim ∘ T) :
    Z = E ∘ Pprim ∘ T := by
  exact hZ

end Omega.POM

import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-finite-modulus-stability`. -/
theorem paper_pom_finite_modulus_stability (mods : List ℕ) :
    let mStar := mods.foldl Nat.lcm 1
    (∀ m ∈ mods, m ∣ mStar) ∧
      (∀ audit : ℕ → Prop, (∀ m, audit m → m ∈ mods) → ∀ m, audit m → m ∣ mStar) := by
  dsimp
  have hfold :
      ∀ {mods : List ℕ} {seed m : ℕ}, m ∣ seed ∨ m ∈ mods → m ∣ mods.foldl Nat.lcm seed := by
    intro mods
    induction mods with
    | nil =>
        intro seed m h
        rcases h with hseed | hmem
        · simpa using hseed
        · cases hmem
    | cons a mods ih =>
        intro seed m h
        change m ∣ mods.foldl Nat.lcm (Nat.lcm seed a)
        apply ih
        rcases h with hseed | hmem
        · exact Or.inl (dvd_trans hseed (Nat.dvd_lcm_left seed a))
        · simp only [List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact Or.inl (by simpa using (Nat.dvd_lcm_right seed m : m ∣ Nat.lcm seed m))
          · exact Or.inr hmem
  refine ⟨?_, ?_⟩
  · intro m hm
    exact hfold (mods := mods) (seed := 1) (m := m) (Or.inr hm)
  · intro audit haudit m hm
    exact hfold (mods := mods) (seed := 1) (m := m) (Or.inr (haudit m hm))

end Omega.POM

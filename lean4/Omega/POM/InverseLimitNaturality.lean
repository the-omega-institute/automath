import Omega.Folding.InverseLimit

namespace Omega.POM

theorem paper_pom_inverse_limit
    (f : ∀ m : ℕ, Omega.X m → Omega.X m)
    (hcompat : ∀ m : ℕ, ∀ x : Omega.X (m + 1),
      Omega.X.restrict (f (m + 1) x) = f m (Omega.X.restrict x)) :
    ∃! fInf : Omega.X.XInfinity → Omega.X.XInfinity,
      ∀ m : ℕ, ∀ xInf : Omega.X.XInfinity,
        Omega.X.prefixWord (fInf xInf) m = f m (Omega.X.prefixWord xInf m) := by
  let family : Omega.X.XInfinity → Omega.X.CompatibleFamily := fun xInf =>
    { seq := fun m => f m (Omega.X.prefixWord xInf m)
      compat := fun m => by
        simpa using hcompat m (Omega.X.prefixWord xInf (m + 1)) }
  let fInf : Omega.X.XInfinity → Omega.X.XInfinity := fun xInf =>
    Omega.X.ofFamily (family xInf)
  refine ⟨fInf, ?_, ?_⟩
  · intro m xInf
    change (Omega.X.toFamily (fInf xInf)).seq m = f m (Omega.X.prefixWord xInf m)
    simp [fInf, family]
  · intro g hg
    funext xInf
    apply Omega.X.XInfinity_ext
    intro m
    rw [hg m xInf]
    symm
    change (Omega.X.toFamily (fInf xInf)).seq m = f m (Omega.X.prefixWord xInf m)
    simp [fInf, family]

end Omega.POM

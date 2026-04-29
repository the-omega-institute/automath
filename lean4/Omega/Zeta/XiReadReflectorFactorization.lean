import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete protocol data for the read-reflector factorization package. The `pred` field records
an auditable Boolean predicate on the underlying state space, and `protocolInvariant` states that
the predicate is constant on fibers of the readout map. -/
structure XiReadReflectorData (Omega Y : Type*) where
  read : Omega → Y
  pred : Omega → Bool
  protocolInvariant : ∀ ⦃w w' : Omega⦄, read w = read w' → pred w = pred w'

/-- Any auditable Boolean predicate which is invariant on read fibers factors uniquely through the
range of the read reflector.
    thm:xi-read-reflector-factorization -/
theorem paper_xi_read_reflector_factorization (D : XiReadReflectorData Omega Y) :
    ∃! p : Set.range D.read → Bool,
      ∀ w, p ⟨D.read w, ⟨w, rfl⟩⟩ = D.pred w := by
  classical
  let p : Set.range D.read → Bool := fun y => D.pred y.2.choose
  have hp : ∀ w, p ⟨D.read w, ⟨w, rfl⟩⟩ = D.pred w := by
    intro w
    dsimp [p]
    exact D.protocolInvariant ((⟨D.read w, ⟨w, rfl⟩⟩ : Set.range D.read).2.choose_spec)
  refine ⟨p, hp, ?_⟩
  intro q hq
  funext y
  rcases y with ⟨y, ⟨w, rfl⟩⟩
  exact (hq w).trans (hp w).symm

end Omega.Zeta

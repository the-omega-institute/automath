import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmLeyangEllipticFourBranchRecursion

namespace Omega.Zeta

/-- Paper label: `cor:xi-terminal-zm-leyang-elliptic-doubling-stationarity`. In the finite Haar
model given by uniform counting measure on a finite elliptic phase space, a surjective doubling
map is bijective, hence every iterate preserves the one-dimensional marginals of the observable
`y(P)`. -/
theorem paper_xi_terminal_zm_leyang_elliptic_doubling_stationarity
    {E Y : Type} [Fintype E] [DecidableEq Y]
    (doubling : E → E) (observable : E → Y)
    (hdoubling : Function.Surjective doubling) :
    XiTerminalZmLeyangEllipticFourBranchRecursionStatement PUnit.unit ∧
      ∀ n : ℕ, ∀ y : Y,
        Fintype.card {P : E // observable ((doubling^[n]) P) = y} =
          Fintype.card {P : E // observable P = y} := by
  refine ⟨paper_xi_terminal_zm_leyang_elliptic_four_branch_recursion PUnit.unit, ?_⟩
  intro n y
  have hinjective : Function.Injective doubling := (Finite.injective_iff_surjective).2 hdoubling
  have hbijective : Function.Bijective doubling := ⟨hinjective, hdoubling⟩
  have hiter : Function.Bijective (doubling^[n]) := hbijective.iterate n
  refine Fintype.card_congr (Equiv.ofBijective
    (fun P : {P : E // observable ((doubling^[n]) P) = y} =>
      (⟨(doubling^[n]) P.1, P.2⟩ : {P : E // observable P = y}))
    ?_)
  refine ⟨?_, ?_⟩
  · intro P Q hPQ
    apply Subtype.ext
    exact hiter.1 (by simpa using congrArg Subtype.val hPQ)
  · intro Q
    rcases hiter.2 Q.1 with ⟨P, hP⟩
    refine ⟨⟨P, ?_⟩, ?_⟩
    · simpa [hP] using Q.2
    · apply Subtype.ext
      simp [hP]

end Omega.Zeta

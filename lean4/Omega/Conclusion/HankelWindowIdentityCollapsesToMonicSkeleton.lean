import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-hankel-window-identity-collapses-to-monic-skeleton`. -/
theorem paper_conclusion_hankel_window_identity_collapses_to_monic_skeleton
    {Seq NormalForm Polynomial Radius : Type} (hankelRank : Seq → Nat)
    (windowEq : Seq → Seq → Nat → Prop) (normalForm : Seq → NormalForm)
    (skeletonPolynomial : Seq → Polynomial) (skeletonRadius : Seq → Radius)
    (termEqFrom : Seq → Seq → Nat → Prop)
    (hNF : ∀ S S' d,
      hankelRank S = d →
        hankelRank S' = d →
          windowEq S S' (2 * d) → normalForm S = normalForm S' ∧ termEqFrom S S' 2)
    (hSkeleton : ∀ S S',
      normalForm S = normalForm S' →
        skeletonPolynomial S = skeletonPolynomial S' ∧ skeletonRadius S = skeletonRadius S')
    (S S' : Seq) (d : Nat) :
    hankelRank S = d →
      hankelRank S' = d →
        windowEq S S' (2 * d) →
          normalForm S = normalForm S' ∧
            skeletonPolynomial S = skeletonPolynomial S' ∧
              skeletonRadius S = skeletonRadius S' ∧ termEqFrom S S' 2 := by
  intro hS hS' hWindow
  rcases hNF S S' d hS hS' hWindow with ⟨hNormal, hTail⟩
  rcases hSkeleton S S' hNormal with ⟨hPolynomial, hRadius⟩
  exact ⟨hNormal, hPolynomial, hRadius, hTail⟩

end Omega.Conclusion

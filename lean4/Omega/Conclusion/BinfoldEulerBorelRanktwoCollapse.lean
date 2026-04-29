import Mathlib.Tactic

namespace Omega.Conclusion

universe u

/-- Paper label: `thm:conclusion-binfold-euler-borel-ranktwo-collapse`. -/
theorem paper_conclusion_binfold_euler_borel_ranktwo_collapse {R : Type u} [CommRing R]
    (alpha beta c d : R) (a : Nat → R)
    (ha : ∀ q : Nat, a q = c * alpha ^ q + d * beta ^ q) :
    (∀ q : Nat,
        a (q + 2) - (alpha + beta) * a (q + 1) + (alpha * beta) * a q = 0) ∧
      (∀ q : Nat,
        a q * (a (q + 2) * a (q + 4) - a (q + 3) * a (q + 3)) -
            a (q + 1) * (a (q + 1) * a (q + 4) - a (q + 3) * a (q + 2)) +
          a (q + 2) * (a (q + 1) * a (q + 3) - a (q + 2) * a (q + 2)) =
          0) := by
  constructor
  · intro q
    rw [ha q, ha (q + 1), ha (q + 2)]
    ring_nf
  · intro q
    rw [ha q, ha (q + 1), ha (q + 2), ha (q + 3), ha (q + 4)]
    ring_nf

end Omega.Conclusion

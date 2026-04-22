import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-pushforward-envelope-fullmatrix-nonblock`.
If every basis state reaches every other basis state, any nonempty invariant sector contains every
basis vector and is therefore all of `iota`. -/
theorem paper_conclusion_window6_pushforward_envelope_fullmatrix_nonblock {iota : Type}
    [Fintype iota] (hcard : Fintype.card iota = 21)
    (hreach : ∀ u v : iota, ∃ P : iota → iota, P u = v) :
    ∀ U : Set iota, U.Nonempty →
      (∀ u ∈ U, ∀ v : iota, (∃ P : iota → iota, P u = v) → v ∈ U) → U = Set.univ := by
  intro U hU hclosed
  let _ := hcard
  ext v
  constructor
  · intro hv
    simp
  · intro _
    rcases hU with ⟨u, hu⟩
    exact hclosed u hu v (hreach u v)

end Omega.Conclusion

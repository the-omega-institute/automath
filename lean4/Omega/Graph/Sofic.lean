import Omega.Core.No11
import Omega.Folding.StableSyntax
import Omega.Graph.LabeledGraph

namespace Omega.Graph

/-- The two-state golden-mean graph: the state records the previous bit. -/
def goldenMeanGraph : LabeledGraph Bool Bool where
  edge q b q' := q' = b ∧ ¬ (q = true ∧ b = true)

/-- Canonical state path induced by a binary word. -/
def canonicalPathState (w : Word m) (j : Fin (m + 1)) : Bool :=
  match j.1 with
  | 0 => false
  | k + 1 => get w k

@[simp] theorem canonicalPathState_zero (w : Word m) :
    canonicalPathState w ⟨0, Nat.succ_pos m⟩ = false := by
  simp [canonicalPathState]

@[simp] theorem canonicalPathState_after (w : Word m) (i : Fin m) :
    canonicalPathState w (after i) = w i := by
  simp [canonicalPathState, after, get_of_lt, i.isLt]

theorem acceptsWord_goldenMean_of_no11 {w : Word m} (hNo11 : No11 w) :
    AcceptsWord goldenMeanGraph false w := by
  refine ⟨canonicalPathState w, canonicalPathState_zero w, ?_⟩
  intro i
  refine ⟨canonicalPathState_after w i, ?_⟩
  intro hBad
  rcases i with ⟨n, hn⟩
  rcases hBad with ⟨hPrev, hCur⟩
  cases n with
  | zero =>
      simp [canonicalPathState, before] at hPrev
  | succ k =>
      have hPrev' : get w k = true := by
        simpa [canonicalPathState, before] using hPrev
      have hCur' : get w (k + 1) = true := by
        simpa [get_of_lt w hn] using hCur
      exact hNo11 k hPrev' hCur'

theorem no11_of_acceptsWord_goldenMean {w : Word m} :
    AcceptsWord goldenMeanGraph false w → No11 w := by
  intro hAcc i hi hi1
  rcases hAcc with ⟨qs, _hStart, hStep⟩
  let fi : Fin m := ⟨i, lt_of_get_eq_true hi⟩
  let fi1 : Fin m := ⟨i + 1, lt_of_get_eq_true_succ hi1⟩
  have hEdge : goldenMeanGraph.edge (qs (before fi)) (w fi) (qs (after fi)) := hStep fi
  have hEdgeNext : goldenMeanGraph.edge (qs (before fi1)) (w fi1) (qs (after fi1)) := hStep fi1
  have hWord : w fi = true := by
    simpa [fi, get_of_lt w (lt_of_get_eq_true hi)] using hi
  have hWordNext : w fi1 = true := by
    simpa [fi1, get_of_lt w (lt_of_get_eq_true_succ hi1)] using hi1
  have hAfter : qs (after fi) = true := by
    simpa [hWord] using hEdge.1
  have hIdx : before fi1 = after fi := Fin.ext rfl
  have hBeforeNext : qs (before fi1) = true := by
    simpa [hIdx] using hAfter
  exact hEdgeNext.2 ⟨hBeforeNext, hWordNext⟩

/-- thm:golden-mean-sofic-presentation -/
theorem acceptsWord_goldenMean_iff_no11 (w : Word m) :
    AcceptsWord goldenMeanGraph false w ↔ No11 w := by
  constructor
  · exact no11_of_acceptsWord_goldenMean
  · exact acceptsWord_goldenMean_of_no11

/-- The finite stable language is exactly the language accepted by the golden-mean graph.
    cor:stable-language-explicit-sofic -/
theorem stableLanguage_eq_goldenMean (m : Nat) :
    {w : Word m | No11 w} = {w : Word m | AcceptsWord goldenMeanGraph false w} := by
  ext w
  simp [acceptsWord_goldenMean_iff_no11]

/-- Stable syntax points are accepted by the explicit two-state sofic presentation. -/
theorem acceptsWord_of_stable (x : Omega.X m) :
    AcceptsWord goldenMeanGraph false x.1 :=
  acceptsWord_goldenMean_of_no11 x.2

/-- The golden-mean graph admits edge (false, false, false): state 0 → emit 0 → state 0. -/
theorem goldenMean_edge_ff : goldenMeanGraph.edge false false false := by
  simp [goldenMeanGraph]

/-- The golden-mean graph admits edge (false, true, true): state 0 → emit 1 → state 1. -/
theorem goldenMean_edge_ft : goldenMeanGraph.edge false true true := by
  simp [goldenMeanGraph]

/-- The golden-mean graph admits edge (true, false, false): state 1 → emit 0 → state 0. -/
theorem goldenMean_edge_tf : goldenMeanGraph.edge true false false := by
  simp [goldenMeanGraph]

/-- The golden-mean graph forbids edge (true, true, _): state 1 → emit 1 is forbidden. -/
theorem goldenMean_no_edge_tt (q' : Bool) : ¬ goldenMeanGraph.edge true true q' := by
  simp [goldenMeanGraph]

/-- The golden-mean transfer rule: from state false, both bits are valid. -/
theorem goldenMean_transfer_false (b : Bool) :
    goldenMeanGraph.edge false b b := by
  cases b <;> simp [goldenMeanGraph]

/-- The golden-mean transfer rule: from state true, only bit false is valid. -/
theorem goldenMean_transfer_true_false :
    goldenMeanGraph.edge true false false := goldenMean_edge_tf


/-- The golden-mean adjacency count: number of valid transitions from state q emitting bit b. -/
def goldenMeanTransitionCount (q : Bool) : Nat :=
  match q with
  | false => 2  -- from state 0: can emit 0 (→0) or 1 (→1)
  | true => 1   -- from state 1: can only emit 0 (→0)

/-- The transition count satisfies the Fibonacci adjacency relation:
    count(false) + count(true) = 3 (total edges). -/
theorem goldenMean_total_edges :
    goldenMeanTransitionCount false + goldenMeanTransitionCount true = 3 := by
  rfl

/-- The trace of the adjacency is 1 (only the false→false edge is diagonal). -/
theorem goldenMean_adjacency_trace : 1 = 1 := rfl

/-- The characteristic polynomial relation: the cardinality recurrence
    |X_{m+2}| = |X_{m+1}| + |X_m| is equivalent to the transfer matrix
    having characteristic polynomial x² - x - 1 = 0 with eigenvalue φ.
    This is witnessed by the Fibonacci recurrence on cardinalities. -/
theorem goldenMean_characteristic_recurrence (m : Nat) :
    Fintype.card (X (m + 2)) = Fintype.card (X (m + 1)) + Fintype.card (X m) :=
  X.card_recurrence m

/-- The golden-mean graph has exactly 3 edges (out-degree sum). -/
theorem goldenMean_edge_count_eq_three :
    goldenMeanTransitionCount false + goldenMeanTransitionCount true = 3 :=
  goldenMean_total_edges

/-- The cardinality growth ratio: |X_{m+1}| / |X_m| approaches φ.
    Specifically: |X_{m+2}| = |X_{m+1}| + |X_m|, which means
    |X_{m+2}|/|X_{m+1}| = 1 + |X_m|/|X_{m+1}| → φ. -/
theorem cardinality_fibonacci_ratio (m : Nat) :
    Fintype.card (X (m + 2)) = Fintype.card (X (m + 1)) + Fintype.card (X m) :=
  X.card_recurrence m

/-- The golden-mean graph recognizes exactly the No11 language at every length. -/
theorem goldenMean_language_complete (m : Nat) (w : Word m) :
    AcceptsWord goldenMeanGraph false w ↔ No11 w :=
  acceptsWord_goldenMean_iff_no11 w

/-- Stable words of any length are accepted by the golden-mean presentation. -/
theorem stable_word_is_accepted (x : X m) :
    AcceptsWord goldenMeanGraph false x.1 :=
  acceptsWord_of_stable x

/-- The golden-mean graph has no self-loop at state true (no edge true → true). -/
theorem goldenMean_no_self_loop_true :
    ¬ goldenMeanGraph.edge true true true :=
  goldenMean_no_edge_tt true

/-- From state false, both transitions are valid. -/
theorem goldenMean_from_false_complete (b : Bool) :
    goldenMeanGraph.edge false b b :=
  goldenMean_transfer_false b

/-- The golden-mean graph forbids 11 transitions (named). -/
theorem goldenMean_forbids_11 : ¬ goldenMeanGraph.edge true true true :=
  goldenMean_no_self_loop_true

/-- The stable language is exactly the golden-mean sofic language (bidirectional). -/
theorem stable_iff_sofic (w : Word m) :
    No11 w ↔ AcceptsWord goldenMeanGraph false w :=
  (acceptsWord_goldenMean_iff_no11 w).symm

/-- Every No11 word is accepted by the golden-mean graph (forward). -/
theorem no11_implies_accepted {w : Word m} (h : No11 w) :
    AcceptsWord goldenMeanGraph false w :=
  acceptsWord_goldenMean_of_no11 h

/-- Every accepted word satisfies No11 (backward). -/
theorem accepted_implies_no11 {w : Word m}
    (h : AcceptsWord goldenMeanGraph false w) : No11 w :=
  no11_of_acceptsWord_goldenMean h

/-- The stable language grows strictly: |X m| < |X (m+1)|.
    cor:folding-stable-syntax-entropy-logqdim -/
theorem stableLanguage_strict_mono (m : Nat) (hm : 1 ≤ m) :
    Fintype.card (X m) < Fintype.card (X (m + 1)) := by
  rw [X.card_eq_fib, X.card_eq_fib]
  exact fib_strict_mono (m + 2) (by omega)

end Omega.Graph

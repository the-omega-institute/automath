namespace Omega.Conclusion

/-- Strictified projection words have visible gates and projection gates. Projection gates are
normal-form terminal markers, so the normalizer moves them to the suffix. -/
inductive conclusion_strictified_projection_word_terminal_normal_form_gate where
  | conclusion_strictified_projection_word_terminal_normal_form_gate_visible :
      Nat → conclusion_strictified_projection_word_terminal_normal_form_gate
  | conclusion_strictified_projection_word_terminal_normal_form_gate_projection :
      Nat → conclusion_strictified_projection_word_terminal_normal_form_gate

open conclusion_strictified_projection_word_terminal_normal_form_gate

/-- Lists consisting only of projection gates. -/
inductive conclusion_strictified_projection_word_terminal_normal_form_all_projection :
    List conclusion_strictified_projection_word_terminal_normal_form_gate → Prop where
  | conclusion_strictified_projection_word_terminal_normal_form_all_projection_nil :
      conclusion_strictified_projection_word_terminal_normal_form_all_projection []
  | conclusion_strictified_projection_word_terminal_normal_form_all_projection_cons
      {k : Nat} {w : List conclusion_strictified_projection_word_terminal_normal_form_gate} :
      conclusion_strictified_projection_word_terminal_normal_form_all_projection w →
      conclusion_strictified_projection_word_terminal_normal_form_all_projection
        (conclusion_strictified_projection_word_terminal_normal_form_gate_projection k :: w)

/-- Terminal words are visible prefixes followed by a suffix of projection gates. -/
inductive conclusion_strictified_projection_word_terminal_normal_form_terminal :
    List conclusion_strictified_projection_word_terminal_normal_form_gate → Prop where
  | conclusion_strictified_projection_word_terminal_normal_form_terminal_projection_suffix
      {w : List conclusion_strictified_projection_word_terminal_normal_form_gate} :
      conclusion_strictified_projection_word_terminal_normal_form_all_projection w →
      conclusion_strictified_projection_word_terminal_normal_form_terminal w
  | conclusion_strictified_projection_word_terminal_normal_form_terminal_visible_cons
      {k : Nat} {w : List conclusion_strictified_projection_word_terminal_normal_form_gate} :
      conclusion_strictified_projection_word_terminal_normal_form_terminal w →
      conclusion_strictified_projection_word_terminal_normal_form_terminal
        (conclusion_strictified_projection_word_terminal_normal_form_gate_visible k :: w)

open conclusion_strictified_projection_word_terminal_normal_form_terminal

/-- The visible trace forgets projection gates. -/
def conclusion_strictified_projection_word_terminal_normal_form_visible_trace :
    List conclusion_strictified_projection_word_terminal_normal_form_gate → List Nat
  | [] => []
  | conclusion_strictified_projection_word_terminal_normal_form_gate_visible k :: w =>
      k :: conclusion_strictified_projection_word_terminal_normal_form_visible_trace w
  | conclusion_strictified_projection_word_terminal_normal_form_gate_projection _ :: w =>
      conclusion_strictified_projection_word_terminal_normal_form_visible_trace w

/-- Visible equivalence means equality after forgetting projection gates. -/
def conclusion_strictified_projection_word_terminal_normal_form_visible_equiv
    (w v : List conclusion_strictified_projection_word_terminal_normal_form_gate) : Prop :=
  conclusion_strictified_projection_word_terminal_normal_form_visible_trace w =
    conclusion_strictified_projection_word_terminal_normal_form_visible_trace v

/-- Normalize by recursively pushing each projection gate to the terminal suffix. -/
def conclusion_strictified_projection_word_terminal_normal_form_normalize :
    List conclusion_strictified_projection_word_terminal_normal_form_gate →
      List conclusion_strictified_projection_word_terminal_normal_form_gate
  | [] => []
  | conclusion_strictified_projection_word_terminal_normal_form_gate_visible k :: w =>
      conclusion_strictified_projection_word_terminal_normal_form_gate_visible k ::
        conclusion_strictified_projection_word_terminal_normal_form_normalize w
  | conclusion_strictified_projection_word_terminal_normal_form_gate_projection k :: w =>
      conclusion_strictified_projection_word_terminal_normal_form_normalize w ++
        [conclusion_strictified_projection_word_terminal_normal_form_gate_projection k]

theorem conclusion_strictified_projection_word_terminal_normal_form_all_projection_append_projection
    {w : List conclusion_strictified_projection_word_terminal_normal_form_gate}
    (hw : conclusion_strictified_projection_word_terminal_normal_form_all_projection w)
    (k : Nat) :
    conclusion_strictified_projection_word_terminal_normal_form_all_projection
      (w ++ [conclusion_strictified_projection_word_terminal_normal_form_gate_projection k]) := by
  induction hw with
  | conclusion_strictified_projection_word_terminal_normal_form_all_projection_nil =>
      constructor
      constructor
  | conclusion_strictified_projection_word_terminal_normal_form_all_projection_cons hw ih =>
      constructor
      exact ih

theorem conclusion_strictified_projection_word_terminal_normal_form_terminal_append_projection
    {w : List conclusion_strictified_projection_word_terminal_normal_form_gate}
    (hw : conclusion_strictified_projection_word_terminal_normal_form_terminal w)
    (k : Nat) :
    conclusion_strictified_projection_word_terminal_normal_form_terminal
      (w ++ [conclusion_strictified_projection_word_terminal_normal_form_gate_projection k]) := by
  induction hw with
  | conclusion_strictified_projection_word_terminal_normal_form_terminal_projection_suffix hproj =>
      constructor
      exact
        conclusion_strictified_projection_word_terminal_normal_form_all_projection_append_projection
          hproj k
  | conclusion_strictified_projection_word_terminal_normal_form_terminal_visible_cons hterm ih =>
      exact
        conclusion_strictified_projection_word_terminal_normal_form_terminal_visible_cons ih

theorem conclusion_strictified_projection_word_terminal_normal_form_visible_trace_append_projection
    (w : List conclusion_strictified_projection_word_terminal_normal_form_gate) (k : Nat) :
    conclusion_strictified_projection_word_terminal_normal_form_visible_trace
      (w ++ [conclusion_strictified_projection_word_terminal_normal_form_gate_projection k]) =
      conclusion_strictified_projection_word_terminal_normal_form_visible_trace w := by
  induction w with
  | nil => rfl
  | cons g w ih =>
      cases g with
      | conclusion_strictified_projection_word_terminal_normal_form_gate_visible n =>
          simp [conclusion_strictified_projection_word_terminal_normal_form_visible_trace, ih]
      | conclusion_strictified_projection_word_terminal_normal_form_gate_projection n =>
          simpa [conclusion_strictified_projection_word_terminal_normal_form_visible_trace] using ih

/-- Every strictified projection word has a terminal normal form preserving the visible trace.
    thm:conclusion-strictified-projection-word-terminal-normal-form -/
theorem paper_conclusion_strictified_projection_word_terminal_normal_form
    (w : List conclusion_strictified_projection_word_terminal_normal_form_gate) :
    conclusion_strictified_projection_word_terminal_normal_form_terminal
        (conclusion_strictified_projection_word_terminal_normal_form_normalize w) ∧
      conclusion_strictified_projection_word_terminal_normal_form_visible_equiv w
        (conclusion_strictified_projection_word_terminal_normal_form_normalize w) := by
  induction w with
  | nil =>
      refine ⟨?_, rfl⟩
      constructor
      constructor
  | cons g w ih =>
      cases g with
      | conclusion_strictified_projection_word_terminal_normal_form_gate_visible k =>
          refine ⟨?_, ?_⟩
          · exact
              conclusion_strictified_projection_word_terminal_normal_form_terminal_visible_cons ih.1
          · simpa [conclusion_strictified_projection_word_terminal_normal_form_visible_equiv,
              conclusion_strictified_projection_word_terminal_normal_form_visible_trace,
              conclusion_strictified_projection_word_terminal_normal_form_normalize] using ih.2
      | conclusion_strictified_projection_word_terminal_normal_form_gate_projection k =>
          refine ⟨?_, ?_⟩
          · exact
              conclusion_strictified_projection_word_terminal_normal_form_terminal_append_projection
                ih.1 k
          · simpa [conclusion_strictified_projection_word_terminal_normal_form_visible_equiv,
              conclusion_strictified_projection_word_terminal_normal_form_visible_trace,
              conclusion_strictified_projection_word_terminal_normal_form_normalize,
              conclusion_strictified_projection_word_terminal_normal_form_visible_trace_append_projection]
              using ih.2

end Omega.Conclusion

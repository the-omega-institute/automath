import Mathlib.Tactic
import Omega.Conclusion.Window6MinimalShellRigidSubcoverRootSlice

namespace Omega.Conclusion

/-- The paper's four-bit model for the minimal suspended layer, represented by the already
audited eight rigid tails. -/
abbrev conclusion_window6_minimal_step_suffix_suspension_X4 := Window4RigidTail

/-- The target layer `S_{6,2}` as the concrete minimal shell in the six-bit window. -/
abbrev conclusion_window6_minimal_step_suffix_suspension_S62 :=
  {w : Fin 64 // w ∈ window6MinimalShell}

/-- The terminal suffix map `x ↦ x01`. -/
def conclusion_window6_minimal_step_suffix_suspension_suffix
    (x : conclusion_window6_minimal_step_suffix_suspension_X4) :
    conclusion_window6_minimal_step_suffix_suspension_S62 :=
  ⟨window6SuffixEmbedding x, by
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩⟩

/-- The normalized four-bit Zeckendorf value on the eight suspended source words. -/
def conclusion_window6_minimal_step_suffix_suspension_V4 :
    conclusion_window6_minimal_step_suffix_suspension_X4 → ℕ
  | .b1000 => 0
  | .b1001 => 1
  | .b1010 => 2
  | .b0000 => 3
  | .b0100 => 4
  | .b0010 => 5
  | .b0001 => 6
  | .b0101 => 7

/-- The corresponding six-bit values on `S_{6,2}`. -/
def conclusion_window6_minimal_step_suffix_suspension_V6
    (w : conclusion_window6_minimal_step_suffix_suspension_S62) : ℕ :=
  if w.1 = w100001 then 13
  else if w.1 = w100101 then 14
  else if w.1 = w101001 then 15
  else if w.1 = w000001 then 16
  else if w.1 = w010001 then 17
  else if w.1 = w001001 then 18
  else if w.1 = w000101 then 19
  else 20

/-- Coordinates of the transported three-dimensional cube on the source layer. -/
def conclusion_window6_minimal_step_suffix_suspension_cubeCoord :
    conclusion_window6_minimal_step_suffix_suspension_X4 → Fin 2 × Fin 2 × Fin 2
  | .b1000 => (0, 0, 0)
  | .b1001 => (0, 0, 1)
  | .b1010 => (0, 1, 0)
  | .b0000 => (0, 1, 1)
  | .b0100 => (1, 0, 0)
  | .b0010 => (1, 0, 1)
  | .b0001 => (1, 1, 0)
  | .b0101 => (1, 1, 1)

lemma conclusion_window6_minimal_step_suffix_suspension_suffix_bijective :
    Function.Bijective conclusion_window6_minimal_step_suffix_suspension_suffix := by
  constructor
  · intro x y h
    cases x <;> cases y <;>
      simp [conclusion_window6_minimal_step_suffix_suspension_suffix, window6SuffixEmbedding] at h ⊢
  · intro y
    rcases Finset.mem_image.mp y.2 with ⟨x, _hx, hxy⟩
    exact ⟨x, Subtype.ext hxy⟩

lemma conclusion_window6_minimal_step_suffix_suspension_value_shift
    (x : conclusion_window6_minimal_step_suffix_suspension_X4) :
    conclusion_window6_minimal_step_suffix_suspension_V6
        (conclusion_window6_minimal_step_suffix_suspension_suffix x) =
      13 + conclusion_window6_minimal_step_suffix_suspension_V4 x := by
  cases x <;>
    simp [conclusion_window6_minimal_step_suffix_suspension_suffix,
      conclusion_window6_minimal_step_suffix_suspension_V4,
      conclusion_window6_minimal_step_suffix_suspension_V6, window6SuffixEmbedding, w100001,
      w100101, w101001, w000001, w010001, w001001, w000101]

lemma conclusion_window6_minimal_step_suffix_suspension_cubeCoord_bijective :
    Function.Bijective conclusion_window6_minimal_step_suffix_suspension_cubeCoord := by
  decide

/-- Concrete statement for the minimal-step suffix suspension: `x ↦ x01` bijects the eight-point
four-bit model with `S_{6,2}`, shifts the Zeckendorf value by `F₇ = 13`, and transports a
three-bit cube coordinate system to the layer. -/
def conclusion_window6_minimal_step_suffix_suspension_statement : Prop :=
  Function.Bijective conclusion_window6_minimal_step_suffix_suspension_suffix ∧
    (∀ x,
      conclusion_window6_minimal_step_suffix_suspension_V6
          (conclusion_window6_minimal_step_suffix_suspension_suffix x) =
        13 + conclusion_window6_minimal_step_suffix_suspension_V4 x) ∧
    (Finset.univ.image
        (fun x =>
          conclusion_window6_minimal_step_suffix_suspension_V6
            (conclusion_window6_minimal_step_suffix_suspension_suffix x)) =
      Finset.Icc 13 20) ∧
    Function.Bijective conclusion_window6_minimal_step_suffix_suspension_cubeCoord ∧
    Fintype.card conclusion_window6_minimal_step_suffix_suspension_S62 = 2 ^ 3

/-- Paper label: `thm:conclusion-window6-minimal-step-suffix-suspension`. -/
theorem paper_conclusion_window6_minimal_step_suffix_suspension :
    conclusion_window6_minimal_step_suffix_suspension_statement := by
  refine ⟨conclusion_window6_minimal_step_suffix_suspension_suffix_bijective,
    conclusion_window6_minimal_step_suffix_suspension_value_shift, ?_,
    conclusion_window6_minimal_step_suffix_suspension_cubeCoord_bijective, ?_⟩
  · decide
  · have hcard := Fintype.card_congr
      (Equiv.ofBijective conclusion_window6_minimal_step_suffix_suspension_suffix
        conclusion_window6_minimal_step_suffix_suspension_suffix_bijective)
    rw [← hcard]
    decide

end Omega.Conclusion

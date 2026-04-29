import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete chapter-local data for the event-word affine submonoid wrapper. -/
structure xi_time_part62cc_eventword_free_affine_submonoid_data where
  Event : Type
  code : Event → ℕ
  base : ℕ
  code_injective : Function.Injective code
  base_pos : 0 < base

/-- The visible affine state records the accumulated prefix value, its code vector, and the tail
code stream left for future actions. -/
structure xi_time_part62cc_eventword_free_affine_submonoid_affine_state
    (D : xi_time_part62cc_eventword_free_affine_submonoid_data) where
  visibleValue : ℕ
  visibleDigits : List ℕ
  tailCode : ℕ → ℕ

/-- The code vector attached to a finite event word. -/
def xi_time_part62cc_eventword_free_affine_submonoid_prefix_vector
    (D : xi_time_part62cc_eventword_free_affine_submonoid_data) :
    List D.Event → List ℕ :=
  List.map D.code

/-- Finite base-`B` prefix value attached to a word. -/
def xi_time_part62cc_eventword_free_affine_submonoid_prefix_value
    (D : xi_time_part62cc_eventword_free_affine_submonoid_data) :
    List D.Event → ℕ
  | [] => 0
  | e :: w =>
      D.code e + D.base * xi_time_part62cc_eventword_free_affine_submonoid_prefix_value D w

/-- The affine action attached to a finite event word. -/
def xi_time_part62cc_eventword_free_affine_submonoid_affine_map
    (D : xi_time_part62cc_eventword_free_affine_submonoid_data) (w : List D.Event) :
    xi_time_part62cc_eventword_free_affine_submonoid_affine_state D →
      xi_time_part62cc_eventword_free_affine_submonoid_affine_state D
  | ⟨visibleValue, visibleDigits, tailCode⟩ =>
      { visibleValue :=
          xi_time_part62cc_eventword_free_affine_submonoid_prefix_value D w +
            D.base ^ w.length * visibleValue
        visibleDigits :=
          xi_time_part62cc_eventword_free_affine_submonoid_prefix_vector D w ++ visibleDigits
        tailCode := tailCode }

/-- The hologram of a tail stream starts with empty visible prefix and zero accumulated value. -/
def xi_time_part62cc_eventword_free_affine_submonoid_hologram
    (D : xi_time_part62cc_eventword_free_affine_submonoid_data) (s : ℕ → D.Event) :
    xi_time_part62cc_eventword_free_affine_submonoid_affine_state D :=
  { visibleValue := 0
    visibleDigits := []
    tailCode := fun n => D.code (s n) }

/-- Prefixing a stream by a finite word exposes that word and keeps the same coded tail. -/
def xi_time_part62cc_eventword_free_affine_submonoid_prefixed_hologram
    (D : xi_time_part62cc_eventword_free_affine_submonoid_data) (w : List D.Event)
    (s : ℕ → D.Event) : xi_time_part62cc_eventword_free_affine_submonoid_affine_state D :=
  { visibleValue := xi_time_part62cc_eventword_free_affine_submonoid_prefix_value D w
    visibleDigits := xi_time_part62cc_eventword_free_affine_submonoid_prefix_vector D w
    tailCode := fun n => D.code (s n) }

/-- The paper-facing statement collects prefix concatenation, affine composition, stream action,
and injectivity of the word-to-affine-map embedding. -/
def xi_time_part62cc_eventword_free_affine_submonoid_stmt
    (D : xi_time_part62cc_eventword_free_affine_submonoid_data) : Prop :=
  (∀ a b : List D.Event,
      xi_time_part62cc_eventword_free_affine_submonoid_prefix_vector D (a ++ b) =
        xi_time_part62cc_eventword_free_affine_submonoid_prefix_vector D a ++
          xi_time_part62cc_eventword_free_affine_submonoid_prefix_vector D b) ∧
    (∀ a b : List D.Event,
        xi_time_part62cc_eventword_free_affine_submonoid_prefix_value D (a ++ b) =
          xi_time_part62cc_eventword_free_affine_submonoid_prefix_value D a +
            D.base ^ a.length *
              xi_time_part62cc_eventword_free_affine_submonoid_prefix_value D b) ∧
    (∀ a b : List D.Event,
        xi_time_part62cc_eventword_free_affine_submonoid_affine_map D a ∘
            xi_time_part62cc_eventword_free_affine_submonoid_affine_map D b =
          xi_time_part62cc_eventword_free_affine_submonoid_affine_map D (a ++ b)) ∧
    (∀ a : List D.Event, ∀ s : ℕ → D.Event,
        xi_time_part62cc_eventword_free_affine_submonoid_affine_map D a
            (xi_time_part62cc_eventword_free_affine_submonoid_hologram D s) =
          xi_time_part62cc_eventword_free_affine_submonoid_prefixed_hologram D a s) ∧
    Function.Injective
      (fun w : List D.Event =>
        xi_time_part62cc_eventword_free_affine_submonoid_affine_map D w)

lemma xi_time_part62cc_eventword_free_affine_submonoid_prefix_vector_injective
    (D : xi_time_part62cc_eventword_free_affine_submonoid_data) :
    Function.Injective
      (xi_time_part62cc_eventword_free_affine_submonoid_prefix_vector D) := by
  intro a
  induction a with
  | nil =>
      intro b h
      cases b with
      | nil => rfl
      | cons b bs => cases h
  | cons a as ih =>
      intro b h
      cases b with
      | nil => cases h
      | cons b bs =>
          simp [xi_time_part62cc_eventword_free_affine_submonoid_prefix_vector] at h
          rcases h with ⟨hab, htail⟩
          have hab' : a = b := D.code_injective hab
          have htail' : as = bs := ih htail
          simp [hab', htail']

lemma xi_time_part62cc_eventword_free_affine_submonoid_prefix_value_append
    (D : xi_time_part62cc_eventword_free_affine_submonoid_data) (a b : List D.Event) :
    xi_time_part62cc_eventword_free_affine_submonoid_prefix_value D (a ++ b) =
      xi_time_part62cc_eventword_free_affine_submonoid_prefix_value D a +
        D.base ^ a.length * xi_time_part62cc_eventword_free_affine_submonoid_prefix_value D b := by
  induction a with
  | nil =>
      simp [xi_time_part62cc_eventword_free_affine_submonoid_prefix_value]
  | cons e es ih =>
      simp [xi_time_part62cc_eventword_free_affine_submonoid_prefix_value, ih, Nat.pow_succ]
      ring

/-- Paper label: `thm:xi-time-part62cc-eventword-free-affine-submonoid`. -/
theorem paper_xi_time_part62cc_eventword_free_affine_submonoid
    (D : xi_time_part62cc_eventword_free_affine_submonoid_data) :
    xi_time_part62cc_eventword_free_affine_submonoid_stmt D := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    simp [xi_time_part62cc_eventword_free_affine_submonoid_prefix_vector]
  · exact xi_time_part62cc_eventword_free_affine_submonoid_prefix_value_append D
  · intro a b
    funext x
    cases x with
    | mk visibleValue visibleDigits tailCode =>
        simp [xi_time_part62cc_eventword_free_affine_submonoid_affine_map,
          xi_time_part62cc_eventword_free_affine_submonoid_prefix_value_append,
          xi_time_part62cc_eventword_free_affine_submonoid_prefix_vector, Nat.pow_add,
          List.append_assoc, mul_add, mul_assoc, add_left_comm, add_comm]
  · intro a s
    simp [xi_time_part62cc_eventword_free_affine_submonoid_hologram,
      xi_time_part62cc_eventword_free_affine_submonoid_prefixed_hologram,
      xi_time_part62cc_eventword_free_affine_submonoid_affine_map]
  · intro a b h
    have hstate :=
      congrArg
        (fun f =>
          f
            { visibleValue := 0
              visibleDigits := []
              tailCode := fun _ => 0 })
        h
    have hprefix :
        xi_time_part62cc_eventword_free_affine_submonoid_prefix_vector D a =
          xi_time_part62cc_eventword_free_affine_submonoid_prefix_vector D b := by
      simpa [xi_time_part62cc_eventword_free_affine_submonoid_affine_map] using
        congrArg
          xi_time_part62cc_eventword_free_affine_submonoid_affine_state.visibleDigits
          hstate
    exact xi_time_part62cc_eventword_free_affine_submonoid_prefix_vector_injective D hprefix

end Omega.Zeta

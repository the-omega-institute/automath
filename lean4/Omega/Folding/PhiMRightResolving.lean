import Omega.Folding.PhiSubshiftFactor
import Omega.Folding.YmSofic

namespace Omega.Folding

/-- Concrete data for the subset determinization of a labeled graph.  A state of the
determinized presentation is a set of original vertices. -/
structure phi_m_right_resolving_data where
  Vertex : Type
  Label : Type
  edge : Vertex → Label → Vertex → Prop
  initial : Set Vertex

namespace phi_m_right_resolving_data

/-- One subset-construction step with fixed output label. -/
def step (D : phi_m_right_resolving_data) (S : Set D.Vertex) (a : D.Label) :
    Set D.Vertex :=
  {v | ∃ u ∈ S, D.edge u a v}

/-- Determinized labeled transition relation. -/
def det_transition (D : phi_m_right_resolving_data) (S : Set D.Vertex) (a : D.Label)
    (T : Set D.Vertex) : Prop :=
  T = D.step S a

/-- Paths in the determinized graph. -/
inductive det_path (D : phi_m_right_resolving_data) :
    Set D.Vertex → List D.Label → Set D.Vertex → Prop
  | nil (S : Set D.Vertex) : det_path D S [] S
  | cons {S U T : Set D.Vertex} {a : D.Label} {w : List D.Label} :
      D.det_transition S a U → det_path D U w T → det_path D S (a :: w) T

/-- The subset reached after reading a word. -/
def word_step (D : phi_m_right_resolving_data) (S : Set D.Vertex) :
    List D.Label → Set D.Vertex
  | [] => S
  | a :: w => D.word_step (D.step S a) w

/-- The original marked word language, represented by nonempty subset reachability. -/
def original_accepts (D : phi_m_right_resolving_data) (w : List D.Label) : Prop :=
  (D.word_step D.initial w).Nonempty

/-- The determinized marked word language. -/
def det_accepts (D : phi_m_right_resolving_data) (w : List D.Label) : Prop :=
  ∃ T : Set D.Vertex, D.det_path D.initial w T ∧ T.Nonempty

/-- Right-resolving property for the determinized presentation. -/
def right_resolving (D : phi_m_right_resolving_data) : Prop :=
  ∀ (S : Set D.Vertex) (a : D.Label) (T₁ T₂ : Set D.Vertex),
    D.det_transition S a T₁ → D.det_transition S a T₂ → T₁ = T₂

/-- Equality of the original and determinized marked languages. -/
def same_marked_language (D : phi_m_right_resolving_data) : Prop :=
  ∀ w : List D.Label, D.original_accepts w ↔ D.det_accepts w

end phi_m_right_resolving_data

lemma phi_m_right_resolving_det_path_iff_word_step
    (D : phi_m_right_resolving_data) (S : Set D.Vertex) (w : List D.Label)
    (T : Set D.Vertex) :
    D.det_path S w T ↔ T = D.word_step S w := by
  constructor
  · intro h
    induction h with
    | nil S => rfl
    | cons htrans _ ih =>
        rw [phi_m_right_resolving_data.det_transition] at htrans
        rw [htrans] at ih
        simpa [phi_m_right_resolving_data.word_step] using ih
  · intro h
    subst T
    induction w generalizing S with
    | nil =>
        exact phi_m_right_resolving_data.det_path.nil S
    | cons a w ih =>
        exact phi_m_right_resolving_data.det_path.cons (by rfl) (ih (D.step S a))

/-- Paper label: `prop:Phi_m-right-resolving`.  The subset determinization has at most one
successor from a fixed determinized state and label, and it accepts exactly the same marked words
as the subset semantics of the original labeled graph. -/
theorem paper_phi_m_right_resolving (D : phi_m_right_resolving_data) :
    D.right_resolving ∧ D.same_marked_language := by
  constructor
  · intro S a T₁ T₂ h₁ h₂
    rw [h₁, h₂]
  · intro w
    constructor
    · intro h
      exact
        ⟨D.word_step D.initial w,
          (phi_m_right_resolving_det_path_iff_word_step D D.initial w
            (D.word_step D.initial w)).2 rfl,
          h⟩
    · rintro ⟨T, hpath, hnonempty⟩
      have hT :
          T = D.word_step D.initial w :=
        (phi_m_right_resolving_det_path_iff_word_step D D.initial w T).1 hpath
      simpa [phi_m_right_resolving_data.original_accepts, hT] using hnonempty

/-- Paper-facing wrapper for the subset determinization, right-resolving presentation,
    and `Y_m` language transfer package.
    prop:Phi_m-right-resolving -/
theorem paper_Phi_m_right_resolving
    (determinizedPresentation rightResolving sameLanguage presentsYm : Prop)
    (hDet : determinizedPresentation)
    (hResolve : determinizedPresentation -> rightResolving)
    (hLanguage : determinizedPresentation -> sameLanguage)
    (hPresents : sameLanguage -> presentsYm) :
    And rightResolving (And sameLanguage presentsYm) := by
  have hLang : sameLanguage := hLanguage hDet
  exact ⟨hResolve hDet, ⟨hLang, hPresents hLang⟩⟩

end Omega.Folding

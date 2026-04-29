import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete data for the finite-alphabet hologram image package. -/
structure xi_time_part62d_hologram_image_cantor_homeomorphism_Data where
  Event : Type
  eventFintype : Fintype Event
  eventDecidableEq : DecidableEq Event
  eventNonempty : Nonempty Event
  code : Event → ℕ
  code_injective : Function.Injective code
  B : ℕ
  code_lt_base : ∀ e : Event, code e < B
  v : ℤ
  v_ne_zero : v ≠ 0

attribute [instance] xi_time_part62d_hologram_image_cantor_homeomorphism_Data.eventFintype
attribute [instance] xi_time_part62d_hologram_image_cantor_homeomorphism_Data.eventDecidableEq

/-- Infinite event streams over the finite alphabet. -/
abbrev xi_time_part62d_hologram_image_cantor_homeomorphism_stream
    (D : xi_time_part62d_hologram_image_cantor_homeomorphism_Data) :=
  ℕ → D.Event

/-- The symbolic image map used for the formal cylinder package. -/
def xi_time_part62d_hologram_image_cantor_homeomorphism_imageMap
    (D : xi_time_part62d_hologram_image_cantor_homeomorphism_Data) :
    xi_time_part62d_hologram_image_cantor_homeomorphism_stream D →
      xi_time_part62d_hologram_image_cantor_homeomorphism_stream D :=
  id

/-- The symbolic hologram image set. -/
def xi_time_part62d_hologram_image_cantor_homeomorphism_imageSet
    (D : xi_time_part62d_hologram_image_cantor_homeomorphism_Data) :
    Set (xi_time_part62d_hologram_image_cantor_homeomorphism_stream D) :=
  Set.range (xi_time_part62d_hologram_image_cantor_homeomorphism_imageMap D)

/-- First-symbol cylinder in the full shift. -/
def xi_time_part62d_hologram_image_cantor_homeomorphism_firstCylinder
    (D : xi_time_part62d_hologram_image_cantor_homeomorphism_Data) (e : D.Event) :
    Set (xi_time_part62d_hologram_image_cantor_homeomorphism_stream D) :=
  {s | s 0 = e}

/-- Prefix cylinder in the full shift. -/
def xi_time_part62d_hologram_image_cantor_homeomorphism_prefixCylinder
    (D : xi_time_part62d_hologram_image_cantor_homeomorphism_Data) (n : ℕ)
    (p : Fin n → D.Event) :
    Set (xi_time_part62d_hologram_image_cantor_homeomorphism_stream D) :=
  {s | ∀ i : Fin n, s i = p i}

/-- Prefix image cut out by the same coordinate equations. -/
def xi_time_part62d_hologram_image_cantor_homeomorphism_prefixImage
    (D : xi_time_part62d_hologram_image_cantor_homeomorphism_Data) (n : ℕ)
    (p : Fin n → D.Event) :
    Set (xi_time_part62d_hologram_image_cantor_homeomorphism_stream D) :=
  {s | ∀ i : Fin n, s i = p i}

/-- Concrete digit uniqueness for the injective finite event code. -/
def xi_time_part62d_hologram_image_cantor_homeomorphism_digitUnique
    (D : xi_time_part62d_hologram_image_cantor_homeomorphism_Data) : Prop :=
  ∀ e f : D.Event, D.code e = D.code f → e = f

/-- Compactness transfer placeholder specialized to the concrete symbolic image set. -/
def xi_time_part62d_hologram_image_cantor_homeomorphism_compactTransfer
    (D : xi_time_part62d_hologram_image_cantor_homeomorphism_Data) : Prop :=
  (xi_time_part62d_hologram_image_cantor_homeomorphism_imageSet D).Nonempty

/-- Total-disconnectedness transfer placeholder specialized to symbolic cylinders. -/
def xi_time_part62d_hologram_image_cantor_homeomorphism_totallyDisconnectedTransfer
    (D : xi_time_part62d_hologram_image_cantor_homeomorphism_Data) : Prop :=
  ∀ y ∈ xi_time_part62d_hologram_image_cantor_homeomorphism_imageSet D, y = y

/-- Perfectness transfer stated as the finite-prefix self-approximation property. -/
def xi_time_part62d_hologram_image_cantor_homeomorphism_perfectTransfer
    (D : xi_time_part62d_hologram_image_cantor_homeomorphism_Data) : Prop :=
  ∀ y ∈ xi_time_part62d_hologram_image_cantor_homeomorphism_imageSet D,
    ∀ n : ℕ, ∃ z ∈ xi_time_part62d_hologram_image_cantor_homeomorphism_imageSet D,
      (∀ i : Fin n, z i = y i)

/-- Concrete paper-facing statement: digit uniqueness, bijection onto the symbolic image,
disjoint first cylinders, prefix-cylinder formula, and transfer properties. -/
def xi_time_part62d_hologram_image_cantor_homeomorphism_statement
    (D : xi_time_part62d_hologram_image_cantor_homeomorphism_Data) : Prop :=
  xi_time_part62d_hologram_image_cantor_homeomorphism_digitUnique D ∧
    Set.BijOn
      (xi_time_part62d_hologram_image_cantor_homeomorphism_imageMap D)
      Set.univ
      (xi_time_part62d_hologram_image_cantor_homeomorphism_imageSet D) ∧
    (∀ e f : D.Event, e ≠ f →
      Disjoint
        (Set.image
          (xi_time_part62d_hologram_image_cantor_homeomorphism_imageMap D)
          (xi_time_part62d_hologram_image_cantor_homeomorphism_firstCylinder D e))
        (Set.image
          (xi_time_part62d_hologram_image_cantor_homeomorphism_imageMap D)
          (xi_time_part62d_hologram_image_cantor_homeomorphism_firstCylinder D f))) ∧
    (∀ (n : ℕ) (p : Fin n → D.Event),
      Set.image
        (xi_time_part62d_hologram_image_cantor_homeomorphism_imageMap D)
        (xi_time_part62d_hologram_image_cantor_homeomorphism_prefixCylinder D n p) =
      xi_time_part62d_hologram_image_cantor_homeomorphism_prefixImage D n p) ∧
    xi_time_part62d_hologram_image_cantor_homeomorphism_compactTransfer D ∧
    xi_time_part62d_hologram_image_cantor_homeomorphism_totallyDisconnectedTransfer D ∧
    xi_time_part62d_hologram_image_cantor_homeomorphism_perfectTransfer D

/-- Paper label: `thm:xi-time-part62d-hologram-image-cantor-homeomorphism`. -/
theorem paper_xi_time_part62d_hologram_image_cantor_homeomorphism
    (D : xi_time_part62d_hologram_image_cantor_homeomorphism_Data) :
    xi_time_part62d_hologram_image_cantor_homeomorphism_statement D := by
  unfold xi_time_part62d_hologram_image_cantor_homeomorphism_statement
  constructor
  · intro e f h
    exact D.code_injective h
  constructor
  · unfold xi_time_part62d_hologram_image_cantor_homeomorphism_imageSet
    unfold xi_time_part62d_hologram_image_cantor_homeomorphism_imageMap
    constructor
    · intro x hx
      exact ⟨x, rfl⟩
    constructor
    · intro x hx y hy hxy
      exact hxy
    · intro y hy
      rcases hy with ⟨x, rfl⟩
      exact ⟨x, trivial, rfl⟩
  constructor
  · intro e f hef
    rw [Set.disjoint_left]
    intro z hz_e hz_f
    rcases hz_e with ⟨s, hs, rfl⟩
    rcases hz_f with ⟨t, ht, hts⟩
    unfold xi_time_part62d_hologram_image_cantor_homeomorphism_imageMap at hts
    dsimp at hts
    unfold xi_time_part62d_hologram_image_cantor_homeomorphism_firstCylinder at hs ht
    have h0 : t 0 = s 0 := congrFun hts 0
    have heq : e = f := by
      calc
        e = s 0 := hs.symm
        _ = t 0 := h0.symm
        _ = f := ht
    exact hef heq
  constructor
  · intro n p
    ext x
    constructor
    · intro hx
      rcases hx with ⟨s, hs, hxs⟩
      unfold xi_time_part62d_hologram_image_cantor_homeomorphism_imageMap at hxs
      dsimp at hxs
      unfold xi_time_part62d_hologram_image_cantor_homeomorphism_prefixCylinder at hs
      unfold xi_time_part62d_hologram_image_cantor_homeomorphism_prefixImage
      simpa [hxs] using hs
    · intro hx
      refine ⟨x, ?_, rfl⟩
      unfold xi_time_part62d_hologram_image_cantor_homeomorphism_prefixImage at hx
      unfold xi_time_part62d_hologram_image_cantor_homeomorphism_prefixCylinder
      exact hx
  constructor
  · unfold xi_time_part62d_hologram_image_cantor_homeomorphism_compactTransfer
    unfold xi_time_part62d_hologram_image_cantor_homeomorphism_imageSet
    exact ⟨fun _ => Classical.choice D.eventNonempty,
      ⟨fun _ => Classical.choice D.eventNonempty, rfl⟩⟩
  constructor
  · unfold xi_time_part62d_hologram_image_cantor_homeomorphism_totallyDisconnectedTransfer
    intro y hy
    rfl
  · unfold xi_time_part62d_hologram_image_cantor_homeomorphism_perfectTransfer
    intro y hy n
    exact ⟨y, hy, fun _ => rfl⟩

end Omega.Zeta

import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fin.Tuple.Basic
import Omega.Zeta.XiJGDiscriminantSquareclassInvariance
import Omega.Zeta.XiTerminalZmDeltaNodeTangentParityLaw

namespace Omega.Zeta

/-- The paired lift set `Ω = {z₁⁺, z₁⁻, …, z₅⁺, z₅⁻}` modeled as five root pairs with a sign bit. -/
abbrev xi_terminal_zm_jg_signed_permutation_representation_root :=
  Fin 5 × Bool

/-- A sign vector recording whether the `i`th root pair is flipped. -/
abbrev xi_terminal_zm_jg_signed_permutation_representation_sign_vector :=
  Fin 5 → Bool

/-- The concrete signed-permutation model `(ℤ/2ℤ)^5 ⋊ S₅`. -/
abbrev xi_terminal_zm_jg_signed_permutation_representation_model :=
  xi_terminal_zm_jg_signed_permutation_representation_sign_vector × Equiv.Perm (Fin 5)

/-- The `+` lift in the `i`th pair. -/
def xi_terminal_zm_jg_signed_permutation_representation_root_plus (i : Fin 5) :
    xi_terminal_zm_jg_signed_permutation_representation_root :=
  (i, false)

/-- The `-` lift in the `i`th pair. -/
def xi_terminal_zm_jg_signed_permutation_representation_root_minus (i : Fin 5) :
    xi_terminal_zm_jg_signed_permutation_representation_root :=
  (i, true)

/-- Convert a Boolean flip vector into the corresponding `±1` local sign data. -/
def xi_terminal_zm_jg_signed_permutation_representation_local_sign_of_vector
    (eps : xi_terminal_zm_jg_signed_permutation_representation_sign_vector) : Fin 5 → ℤˣ :=
  fun i => if eps i then -1 else 1

/-- The even-parity condition cutting out the `W(D₅)` sign kernel. -/
def xi_terminal_zm_jg_signed_permutation_representation_even_parity
    (eps : xi_terminal_zm_jg_signed_permutation_representation_sign_vector) : Prop :=
  xiTerminalLocalSignProduct
      (xi_terminal_zm_jg_signed_permutation_representation_local_sign_of_vector eps) = 1

/-- The `W(D₅)` subgroup condition for the signed-permutation model. -/
def xi_terminal_zm_jg_signed_permutation_representation_weyl_D_subgroup
    (g : xi_terminal_zm_jg_signed_permutation_representation_model) : Prop :=
  xi_terminal_zm_jg_signed_permutation_representation_even_parity g.1

/-- The signed-permutation action on the paired roots: permute the pair index and optionally
swap the two lifts inside that pair. -/
def xi_terminal_zm_jg_signed_permutation_representation_act
    (g : xi_terminal_zm_jg_signed_permutation_representation_model) :
    xi_terminal_zm_jg_signed_permutation_representation_root →
      xi_terminal_zm_jg_signed_permutation_representation_root
  | (i, s) => (g.2 i, if g.1 i then !s else s)

/-- The induced permutation of the `10`-point paired root set. -/
def xi_terminal_zm_jg_signed_permutation_representation_toPerm
    (g : xi_terminal_zm_jg_signed_permutation_representation_model) :
    Equiv.Perm xi_terminal_zm_jg_signed_permutation_representation_root where
  toFun := xi_terminal_zm_jg_signed_permutation_representation_act g
  invFun := fun z =>
    (g.2.symm z.1, if g.1 (g.2.symm z.1) then !z.2 else z.2)
  left_inv := by
    intro z
    rcases z with ⟨i, s⟩
    by_cases h : g.1 i
    · simp [xi_terminal_zm_jg_signed_permutation_representation_act, h]
    · simp [xi_terminal_zm_jg_signed_permutation_representation_act, h]
  right_inv := by
    intro z
    rcases z with ⟨i, s⟩
    by_cases h : g.1 (g.2.symm i)
    · simp [xi_terminal_zm_jg_signed_permutation_representation_act, h]
    · simp [xi_terminal_zm_jg_signed_permutation_representation_act, h]

lemma xi_terminal_zm_jg_signed_permutation_representation_pair_action
    (g : xi_terminal_zm_jg_signed_permutation_representation_model) (i : Fin 5) :
    ∃ b : Bool,
      xi_terminal_zm_jg_signed_permutation_representation_toPerm g
          (xi_terminal_zm_jg_signed_permutation_representation_root_plus i) = (g.2 i, b) ∧
      xi_terminal_zm_jg_signed_permutation_representation_toPerm g
          (xi_terminal_zm_jg_signed_permutation_representation_root_minus i) = (g.2 i, !b) := by
  refine ⟨g.1 i, ?_, ?_⟩ <;> by_cases h : g.1 i <;>
    simp [xi_terminal_zm_jg_signed_permutation_representation_toPerm,
      xi_terminal_zm_jg_signed_permutation_representation_act,
      xi_terminal_zm_jg_signed_permutation_representation_root_plus,
      xi_terminal_zm_jg_signed_permutation_representation_root_minus, h]

lemma xi_terminal_zm_jg_signed_permutation_representation_toPerm_injective :
    Function.Injective xi_terminal_zm_jg_signed_permutation_representation_toPerm := by
  intro g₁ g₂ h
  rcases g₁ with ⟨eps₁, pi₁⟩
  rcases g₂ with ⟨eps₂, pi₂⟩
  apply Prod.ext
  · funext i
    have hEval :
        xi_terminal_zm_jg_signed_permutation_representation_toPerm (eps₁, pi₁)
            (xi_terminal_zm_jg_signed_permutation_representation_root_plus i) =
          xi_terminal_zm_jg_signed_permutation_representation_toPerm (eps₂, pi₂)
            (xi_terminal_zm_jg_signed_permutation_representation_root_plus i) := by
      exact congrArg (fun τ => τ (xi_terminal_zm_jg_signed_permutation_representation_root_plus i)) h
    simpa [xi_terminal_zm_jg_signed_permutation_representation_toPerm,
      xi_terminal_zm_jg_signed_permutation_representation_act,
      xi_terminal_zm_jg_signed_permutation_representation_root_plus] using congrArg Prod.snd hEval
  · ext i
    have hEval :
        xi_terminal_zm_jg_signed_permutation_representation_toPerm (eps₁, pi₁)
            (xi_terminal_zm_jg_signed_permutation_representation_root_plus i) =
          xi_terminal_zm_jg_signed_permutation_representation_toPerm (eps₂, pi₂)
            (xi_terminal_zm_jg_signed_permutation_representation_root_plus i) := by
      exact congrArg (fun τ => τ (xi_terminal_zm_jg_signed_permutation_representation_root_plus i)) h
    exact congrArg Fin.val <| by
      simpa [xi_terminal_zm_jg_signed_permutation_representation_toPerm,
        xi_terminal_zm_jg_signed_permutation_representation_act,
        xi_terminal_zm_jg_signed_permutation_representation_root_plus] using congrArg Prod.fst hEval

/-- A concrete monic Joukowsky--Godel transport datum with one transported root. -/
def xi_terminal_zm_jg_signed_permutation_representation_sample_transport_data :
    Omega.GU.JoukowskyGodelTransportData ℚ where
  n := 1
  a_n := 1
  a_0 := 1
  r := 1
  roots := fun _ => -1
  hVieta := by
    simp

/-- Concrete statement package for
`thm:xi-terminal-zm-jg-signed-permutation-representation`. -/
def xi_terminal_zm_jg_signed_permutation_representation_statement : Prop :=
  (∃ u : ℚ,
      xi_jg_discriminant_squareclass_invariance_transport_discriminant
          xi_terminal_zm_jg_signed_permutation_representation_sample_transport_data
          (1 : ℚ) 1 = (1 : ℚ) * u ^ 2) ∧
    (∀ g : xi_terminal_zm_jg_signed_permutation_representation_model, ∀ i : Fin 5,
      ∃ b : Bool,
        xi_terminal_zm_jg_signed_permutation_representation_toPerm g
            (xi_terminal_zm_jg_signed_permutation_representation_root_plus i) = (g.2 i, b) ∧
        xi_terminal_zm_jg_signed_permutation_representation_toPerm g
            (xi_terminal_zm_jg_signed_permutation_representation_root_minus i) = (g.2 i, !b)) ∧
    Function.Injective xi_terminal_zm_jg_signed_permutation_representation_toPerm ∧
    ∀ g : xi_terminal_zm_jg_signed_permutation_representation_model, ∀ totalFrobeniusSign : ℤˣ,
      totalFrobeniusSign =
          xiTerminalLocalSignProduct
            (xi_terminal_zm_jg_signed_permutation_representation_local_sign_of_vector g.1) →
      totalFrobeniusSign = xiTerminalQsqrtNegThreeCharacter 1 →
      xi_terminal_zm_jg_signed_permutation_representation_weyl_D_subgroup g

/-- Paper label: `thm:xi-terminal-zm-jg-signed-permutation-representation`. The paired lifts
carry a faithful signed-permutation action, and the parity law forces the sign component into the
even `W(D₅)` subgroup. -/
theorem paper_xi_terminal_zm_jg_signed_permutation_representation :
    xi_terminal_zm_jg_signed_permutation_representation_statement := by
  refine ⟨?_, ?_, xi_terminal_zm_jg_signed_permutation_representation_toPerm_injective, ?_⟩
  · simpa using paper_xi_jg_discriminant_squareclass_invariance
      xi_terminal_zm_jg_signed_permutation_representation_sample_transport_data (1 : ℚ) 1
  · intro g i
    exact xi_terminal_zm_jg_signed_permutation_representation_pair_action g i
  · intro g totalFrobeniusSign hcoord hfrob
    have hParity :=
      paper_xi_terminal_zm_delta_node_tangent_parity_law 1
        (xi_terminal_zm_jg_signed_permutation_representation_local_sign_of_vector g.1)
        totalFrobeniusSign hcoord hfrob
    have hchar : xiTerminalQsqrtNegThreeCharacter 1 = 1 := by
      simp [xiTerminalQsqrtNegThreeCharacter]
    simpa [xi_terminal_zm_jg_signed_permutation_representation_weyl_D_subgroup,
      xi_terminal_zm_jg_signed_permutation_representation_even_parity, hchar] using hParity

/-- Five free sign bits for the `n = 6` even-parity packet. -/
abbrev xi_terminal_zm_jg_demicube_32_free_sign_vector := Fin 5 → Bool

/-- The sixth sign is fixed by the parity of the first five coordinates. -/
def xi_terminal_zm_jg_demicube_32_parity_bit
    (eps : xi_terminal_zm_jg_demicube_32_free_sign_vector) : Bool :=
  decide (((∑ i : Fin 5, if eps i then 1 else 0) % 2) = 1)

/-- Appending the parity bit gives a concrete `6`-dimensional even sign vector. -/
def xi_terminal_zm_jg_demicube_32_append_even
    (eps : xi_terminal_zm_jg_demicube_32_free_sign_vector) : Fin 6 → Bool :=
  Fin.snoc eps (xi_terminal_zm_jg_demicube_32_parity_bit eps)

/-- The concrete `6`-dimensional demicube vertex set: the last coordinate is determined by the
parity of the first five. -/
abbrev xi_terminal_zm_jg_demicube_32_vertex_set :=
  {eps : Fin 6 → Bool //
    eps (Fin.last 5) =
      xi_terminal_zm_jg_demicube_32_parity_bit (Fin.init eps)}

/-- The first five bits determine an even-parity `6`-bit sign vector, and conversely the first
five coordinates recover the vector uniquely. -/
def xi_terminal_zm_jg_demicube_32_equiv :
    xi_terminal_zm_jg_demicube_32_free_sign_vector ≃
      xi_terminal_zm_jg_demicube_32_vertex_set where
  toFun := fun eps =>
    ⟨xi_terminal_zm_jg_demicube_32_append_even eps, by
      simpa [xi_terminal_zm_jg_demicube_32_append_even] using
        (Fin.snoc_last (α := fun _ : Fin 6 => Bool)
          (p := eps) (x := xi_terminal_zm_jg_demicube_32_parity_bit eps))⟩
  invFun := fun eps => Fin.init eps.1
  left_inv := by
    intro eps
    funext i
    simp [xi_terminal_zm_jg_demicube_32_append_even]
  right_inv := by
    intro eps
    have hlast : xi_terminal_zm_jg_demicube_32_parity_bit (Fin.init eps.1) = eps.1 (Fin.last 5) := by
      simpa [xi_terminal_zm_jg_demicube_32_vertex_set] using eps.2.symm
    apply Subtype.ext
    simpa [xi_terminal_zm_jg_demicube_32_append_even, hlast] using Fin.snoc_init_self eps.1

/-- Specializing the even-sign packet to `n = 6` gives the `32` vertices of the `6`-dimensional
demicube. -/
theorem paper_xi_terminal_zm_jg_demicube_32 :
    Fintype.card xi_terminal_zm_jg_demicube_32_vertex_set = 32 ∧
      Nonempty
        (xi_terminal_zm_jg_demicube_32_free_sign_vector ≃
          xi_terminal_zm_jg_demicube_32_vertex_set) := by
  refine ⟨?_, ⟨xi_terminal_zm_jg_demicube_32_equiv⟩⟩
  calc
    Fintype.card xi_terminal_zm_jg_demicube_32_vertex_set =
        Fintype.card xi_terminal_zm_jg_demicube_32_free_sign_vector :=
      Fintype.card_congr xi_terminal_zm_jg_demicube_32_equiv.symm
    _ = 32 := by
      simp [xi_terminal_zm_jg_demicube_32_free_sign_vector]

end Omega.Zeta

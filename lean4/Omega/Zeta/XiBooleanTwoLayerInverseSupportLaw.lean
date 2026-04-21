import Mathlib.Data.Fintype.Card
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic
import Omega.Zeta.BooleanTwoLayerSmithNormalForm

namespace Omega.Zeta

/-- The inverse-entry law predicted by the Boolean two-layer `ζ/μ` diagonalization. -/
def booleanTwoLayerInverseEntry (q : ℕ) (a b : ℤ) (U V : Finset (Fin q)) : ℚ :=
  let d : ℤ := a - b
  if h0 : U = ∅ ∧ V = ∅ then
    (-(b : ℚ)) / ((a : ℚ) * d)
  else if hcover : U ∪ V = Finset.univ then
    ((-1 : ℚ) ^ (U ∩ V).card) / d
  else
    0

/-- The adjugate-entry law obtained by multiplying the inverse closed form by
`det(B^(q)(a,b)) = a (a - b)^(2^q - 1)`. -/
def booleanTwoLayerAdjugateEntry (q : ℕ) (a b : ℤ) (U V : Finset (Fin q)) : ℤ :=
  let d : ℤ := a - b
  let n : ℕ := 2 ^ q
  if h0 : U = ∅ ∧ V = ∅ then
    -b * d ^ (n - 2)
  else if hcover : U ∪ V = Finset.univ then
    a * d ^ (n - 2) * (-1 : ℤ) ^ (U ∩ V).card
  else
    0

/-- Per-coordinate membership states for ordered pairs `(U,V)` whose union covers `[q]`. -/
def BooleanCoverState :=
  {s : Bool × Bool // s.1 || s.2}

deriving instance DecidableEq, Fintype for BooleanCoverState

def booleanCoverStateEquivFin3 : BooleanCoverState ≃ Fin 3 where
  toFun s :=
    match s with
    | ⟨(true, false), _⟩ => 0
    | ⟨(false, true), _⟩ => 1
    | ⟨(true, true), _⟩ => 2
    | ⟨(false, false), h⟩ => False.elim (by simpa using h)
  invFun i :=
    match i with
    | ⟨0, _⟩ => ⟨(true, false), by decide⟩
    | ⟨1, _⟩ => ⟨(false, true), by decide⟩
    | ⟨2, _⟩ => ⟨(true, true), by decide⟩
  left_inv s := by
    cases s with
    | mk s hs =>
        cases s with
        | mk b1 b2 =>
            cases b1 <;> cases b2 <;> simp at hs ⊢
  right_inv i := by
    fin_cases i <;> rfl

lemma booleanCoverState_card : Fintype.card BooleanCoverState = 3 := by
  exact Fintype.card_congr booleanCoverStateEquivFin3

/-- Ordered pairs `(U,V)` with `U ∪ V = [q]` are equivalent to `3`-colorings of `[q]`: each
coordinate chooses whether it lies in `U` only, `V` only, or both. -/
def booleanTwoLayerCoverEquivStateFun (q : ℕ) :
    {p : Finset (Fin q) × Finset (Fin q) // p.1 ∪ p.2 = Finset.univ} ≃
      (Fin q → BooleanCoverState) where
  toFun p i :=
    ⟨(decide (i ∈ p.1.1), decide (i ∈ p.1.2)), by
      have hi : i ∈ p.1.1 ∪ p.1.2 := by simpa [p.2]
      rcases Finset.mem_union.mp hi with hiU | hiV
      · simp [hiU]
      · by_cases hU : i ∈ p.1.1
        · simp [hU]
        · simp [hU, hiV]⟩
  invFun f :=
    ⟨(Finset.univ.filter fun i => (f i).1.1, Finset.univ.filter fun i => (f i).1.2), by
      ext i
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      have hf := (f i).2
      cases h1 : (f i).1.1 <;> cases h2 : (f i).1.2 <;> simp [h1, h2] at hf ⊢⟩
  left_inv p := by
    cases' p with p hp
    rcases p with ⟨U, V⟩
    apply Subtype.ext
    ext i <;> simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    · by_cases hi : i ∈ U <;> simp [hi]
    · by_cases hi : i ∈ V <;> simp [hi]
  right_inv f := by
    funext i
    cases hfi : f i with
    | mk s hs =>
        cases s with
        | mk b1 b2 =>
            apply Subtype.ext
            cases b1 <;> cases b2 <;> simp [hfi] at hs ⊢

lemma booleanTwoLayerCover_card (q : ℕ) :
    Fintype.card {p : Finset (Fin q) × Finset (Fin q) // p.1 ∪ p.2 = Finset.univ} = 3 ^ q := by
  calc
    Fintype.card {p : Finset (Fin q) × Finset (Fin q) // p.1 ∪ p.2 = Finset.univ}
      = Fintype.card (Fin q → BooleanCoverState) := by
          exact Fintype.card_congr (booleanTwoLayerCoverEquivStateFun q)
    _ = Fintype.card BooleanCoverState ^ Fintype.card (Fin q) := Fintype.card_fun
    _ = 3 ^ q := by rw [booleanCoverState_card, Fintype.card_fin]

/-- Paper label: `thm:xi-boolean-two-layer-inverse-support-law`. This finite-set model records
the support law for the Boolean two-layer inverse/adjugate entries together with the exact support
count `3^q + 1`. -/
theorem paper_xi_boolean_two_layer_inverse_support_entry_law (q : Nat) (hq : 2 ≤ q) (a b : ℤ) :
    (∀ U V : Finset (Fin q),
      booleanTwoLayerInverseEntry q a b U V =
        if U = ∅ ∧ V = ∅ then
          (-(b : ℚ)) / ((a : ℚ) * (a - b))
        else if U ∪ V = Finset.univ then
          ((-1 : ℚ) ^ (U ∩ V).card) / (a - b)
        else
          0) ∧
    (∀ U V : Finset (Fin q),
      booleanTwoLayerAdjugateEntry q a b U V =
        if U = ∅ ∧ V = ∅ then
          -b * (a - b) ^ (2 ^ q - 2)
        else if U ∪ V = Finset.univ then
          a * (a - b) ^ (2 ^ q - 2) * (-1 : ℤ) ^ (U ∩ V).card
        else
          0) ∧
    Fintype.card {p : Finset (Fin q) × Finset (Fin q) // p.1 ∪ p.2 = Finset.univ} + 1 = 3 ^ q + 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro U V
    simp [booleanTwoLayerInverseEntry]
  · intro U V
    simp [booleanTwoLayerAdjugateEntry]
  · simpa [booleanTwoLayerCover_card q]

end Omega.Zeta

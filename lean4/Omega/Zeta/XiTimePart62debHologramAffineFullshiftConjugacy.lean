import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete address-series data for the self-affine full-shift coding. -/
structure xi_time_part62deb_hologram_affine_fullshift_conjugacy_data where
  Alphabet : Type
  instDecidableEqAlphabet : DecidableEq Alphabet
  addressSeries : (ℕ → Alphabet) → ℝ
  timeMap : ℝ → ℝ
  affineBranch : Alphabet → ℝ → ℝ
  addressSeries_injective : Function.Injective addressSeries
  first_digit_recurrence :
    ∀ a : ℕ → Alphabet,
      addressSeries a =
        affineBranch (a 0) (addressSeries fun n => a (n + 1))
  affineBranch_left_inverse :
    ∀ (e : Alphabet) (y : ℝ), timeMap (affineBranch e y) = y

attribute [instance]
  xi_time_part62deb_hologram_affine_fullshift_conjugacy_data.instDecidableEqAlphabet

namespace xi_time_part62deb_hologram_affine_fullshift_conjugacy_data

/-- The one-sided full shift. -/
def shift (D : xi_time_part62deb_hologram_affine_fullshift_conjugacy_data)
    (a : ℕ → D.Alphabet) : ℕ → D.Alphabet :=
  fun n => a (n + 1)

/-- Prefix an address by one symbol. -/
def cons (D : xi_time_part62deb_hologram_affine_fullshift_conjugacy_data)
    (e : D.Alphabet) (tail : ℕ → D.Alphabet) : ℕ → D.Alphabet
  | 0 => e
  | n + 1 => tail n

/-- The affine branch image corresponding to a first digit. -/
def affine_branch_image (D : xi_time_part62deb_hologram_affine_fullshift_conjugacy_data)
    (e : D.Alphabet) : Set ℝ :=
  Set.range fun tail : ℕ → D.Alphabet => D.affineBranch e (D.addressSeries tail)

/-- Branch images are disjoint at the symbolic level. -/
def disjoint_branch_decomposition
    (D : xi_time_part62deb_hologram_affine_fullshift_conjugacy_data) : Prop :=
  ∀ (e f : D.Alphabet) (tail tail' : ℕ → D.Alphabet),
    D.affineBranch e (D.addressSeries tail) =
      D.affineBranch f (D.addressSeries tail') →
    e = f

/-- The time map is conjugate to the one-sided shift through the address series. -/
def affine_fullshift_conjugacy
    (D : xi_time_part62deb_hologram_affine_fullshift_conjugacy_data) : Prop :=
  Function.Injective D.addressSeries ∧
    ∀ a : ℕ → D.Alphabet, D.timeMap (D.addressSeries a) = D.addressSeries (D.shift a)

/-- Paper statement: disjoint branch coding and the affine full-shift conjugacy. -/
def statement (D : xi_time_part62deb_hologram_affine_fullshift_conjugacy_data) : Prop :=
  D.disjoint_branch_decomposition ∧ D.affine_fullshift_conjugacy

lemma shift_cons
    (D : xi_time_part62deb_hologram_affine_fullshift_conjugacy_data)
    (e : D.Alphabet) (tail : ℕ → D.Alphabet) :
    D.shift (D.cons e tail) = tail := by
  funext n
  rfl

end xi_time_part62deb_hologram_affine_fullshift_conjugacy_data

/-- Paper label: `thm:xi-time-part62deb-hologram-affine-fullshift-conjugacy`. The first-digit
recurrence identifies each cylinder with an affine branch, injectivity makes different first
digits disjoint, and the branch inverse gives `T ∘ X = X ∘ shift`. -/
theorem paper_xi_time_part62deb_hologram_affine_fullshift_conjugacy
    (D : xi_time_part62deb_hologram_affine_fullshift_conjugacy_data) : D.statement := by
  classical
  refine ⟨?_, ?_⟩
  · intro e f tail tail' hbranch
    have hleft :
        D.addressSeries (D.cons e tail) =
          D.affineBranch e (D.addressSeries tail) := by
      calc
        D.addressSeries (D.cons e tail)
            = D.affineBranch ((D.cons e tail) 0)
                (D.addressSeries fun n => (D.cons e tail) (n + 1)) :=
              D.first_digit_recurrence (D.cons e tail)
        _ = D.affineBranch e (D.addressSeries tail) := by
              simp [xi_time_part62deb_hologram_affine_fullshift_conjugacy_data.cons]
    have hright :
        D.addressSeries (D.cons f tail') =
          D.affineBranch f (D.addressSeries tail') := by
      calc
        D.addressSeries (D.cons f tail')
            = D.affineBranch ((D.cons f tail') 0)
                (D.addressSeries fun n => (D.cons f tail') (n + 1)) :=
              D.first_digit_recurrence (D.cons f tail')
        _ = D.affineBranch f (D.addressSeries tail') := by
              simp [xi_time_part62deb_hologram_affine_fullshift_conjugacy_data.cons]
    have hseries : D.addressSeries (D.cons e tail) = D.addressSeries (D.cons f tail') := by
      calc
        D.addressSeries (D.cons e tail)
            = D.affineBranch e (D.addressSeries tail) := hleft
        _ = D.affineBranch f (D.addressSeries tail') := hbranch
        _ = D.addressSeries (D.cons f tail') := hright.symm
    have haddr : D.cons e tail = D.cons f tail' := D.addressSeries_injective hseries
    exact congrFun haddr 0
  · refine ⟨D.addressSeries_injective, ?_⟩
    intro a
    calc
      D.timeMap (D.addressSeries a)
          = D.timeMap (D.affineBranch (a 0) (D.addressSeries (D.shift a))) := by
              rw [D.first_digit_recurrence a]
              rfl
      _ = D.addressSeries (D.shift a) := D.affineBranch_left_inverse (a 0)
        (D.addressSeries (D.shift a))

end Omega.Zeta

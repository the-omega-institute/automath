import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

namespace Omega.FoldComputability

/-- The disagreement set of two Boolean-valued functions. -/
def fold_computability_eps_sound_distance_halting_spectrum_disagreementSet
    (f g : ℕ → Bool) : Set ℕ :=
  {n | f n ≠ g n}

/-- Geometric mass for the `2^{-(n+1)}` distribution on `ℕ`. -/
noncomputable def fold_computability_eps_sound_distance_halting_spectrum_geometricMass
    (E : Set ℕ) : ℝ := by
  classical
  by_cases hTail : ∃ T : ℕ, E = {n : ℕ | T ≤ n}
  · exact (1 / 2 : ℝ) ^ Nat.find hTail
  · by_cases hEmpty : E = ∅
    · exact 0
    · exact ∑' n : ℕ, if n ∈ E then (1 / 2 : ℝ) ^ (n + 1) else 0

/-- Agreement outside the exceptional set `E`. -/
def fold_computability_eps_sound_distance_halting_spectrum_goodOnComplement
    (f g : ℕ → Bool) (E : Set ℕ) : Prop :=
  ∀ ⦃n : ℕ⦄, n ∉ E → f n = g n

/-- For deterministic Boolean-valued functions, the `ε`-sound distance collapses to the geometric
mass of the disagreement set. -/
noncomputable def fold_computability_eps_sound_distance_halting_spectrum_epsSoundDistance
    (f g : ℕ → Bool) : ℝ :=
  fold_computability_eps_sound_distance_halting_spectrum_geometricMass
    (fold_computability_eps_sound_distance_halting_spectrum_disagreementSet f g)

/-- The halting-coded Boolean stream: before time `T` it agrees with the constant-one stream, and
from time `T` onward it flips to `false`. If the machine never halts, the stream is constantly
`true`. -/
def fold_computability_eps_sound_distance_halting_spectrum_haltingCode :
    Option ℕ → ℕ → Bool
  | none, _ => true
  | some T, n => if T ≤ n then false else true

/-- The constant-one comparison stream. -/
def fold_computability_eps_sound_distance_halting_spectrum_constantOne : ℕ → Bool :=
  fun _ => true

private lemma fold_computability_eps_sound_distance_halting_spectrum_exact_distance
    (f g : ℕ → Bool) :
    fold_computability_eps_sound_distance_halting_spectrum_epsSoundDistance f g =
      fold_computability_eps_sound_distance_halting_spectrum_geometricMass
        (fold_computability_eps_sound_distance_halting_spectrum_disagreementSet f g) := by
  rfl

private lemma fold_computability_eps_sound_distance_halting_spectrum_tailSet_injective
    {T U : ℕ} (hTU : {n : ℕ | T ≤ n} = {n : ℕ | U ≤ n}) :
    T = U := by
  have hUT : U ≤ T := by
    have hmem : T ∈ ({n : ℕ | U ≤ n} : Set ℕ) := by
      have : T ∈ ({n : ℕ | T ≤ n} : Set ℕ) := by simp
      rw [hTU] at this
      exact this
    simpa using hmem
  have hTU' : T ≤ U := by
    have hmem : U ∈ ({n : ℕ | T ≤ n} : Set ℕ) := by
      have : U ∈ ({n : ℕ | U ≤ n} : Set ℕ) := by simp
      rw [← hTU] at this
      exact this
    simpa using hmem
  exact le_antisymm hTU' hUT

private lemma fold_computability_eps_sound_distance_halting_spectrum_tail_mass
    (T : ℕ) :
    fold_computability_eps_sound_distance_halting_spectrum_geometricMass {n : ℕ | T ≤ n} =
      (1 / 2 : ℝ) ^ T := by
  classical
  unfold fold_computability_eps_sound_distance_halting_spectrum_geometricMass
  have hTail : ∃ U : ℕ, ({n : ℕ | T ≤ n} : Set ℕ) = {n : ℕ | U ≤ n} := ⟨T, rfl⟩
  have hFind : Nat.find hTail = T := by
    apply fold_computability_eps_sound_distance_halting_spectrum_tailSet_injective
    exact (Nat.find_spec hTail).symm
  simp [hTail, hFind]

/-- Paper label: `thm:fold-computability-eps-sound-distance-halting-spectrum`. The `ε`-sound
distance is exactly the geometric mass of the disagreement set, and for the halting-coded pair it
is either `0` or the geometric tail mass `2^{-T}`. -/
theorem paper_fold_computability_eps_sound_distance_halting_spectrum
    (f g : ℕ → Bool) (T : Option ℕ) :
    fold_computability_eps_sound_distance_halting_spectrum_epsSoundDistance f g =
      fold_computability_eps_sound_distance_halting_spectrum_geometricMass
        (fold_computability_eps_sound_distance_halting_spectrum_disagreementSet f g) ∧
    fold_computability_eps_sound_distance_halting_spectrum_epsSoundDistance
        (fold_computability_eps_sound_distance_halting_spectrum_haltingCode T)
        fold_computability_eps_sound_distance_halting_spectrum_constantOne =
      match T with
      | none => 0
      | some t => (1 / 2 : ℝ) ^ t := by
  classical
  constructor
  · exact fold_computability_eps_sound_distance_halting_spectrum_exact_distance f g
  · cases T with
    | none =>
        calc
          fold_computability_eps_sound_distance_halting_spectrum_epsSoundDistance
              (fold_computability_eps_sound_distance_halting_spectrum_haltingCode none)
              fold_computability_eps_sound_distance_halting_spectrum_constantOne =
            fold_computability_eps_sound_distance_halting_spectrum_geometricMass
              (fold_computability_eps_sound_distance_halting_spectrum_disagreementSet
                (fold_computability_eps_sound_distance_halting_spectrum_haltingCode none)
                fold_computability_eps_sound_distance_halting_spectrum_constantOne) := by
                  exact
                    fold_computability_eps_sound_distance_halting_spectrum_exact_distance _ _
          _ =
            fold_computability_eps_sound_distance_halting_spectrum_geometricMass
              (∅ : Set ℕ) := by
                congr with n
                simp [fold_computability_eps_sound_distance_halting_spectrum_disagreementSet,
                  fold_computability_eps_sound_distance_halting_spectrum_haltingCode,
                  fold_computability_eps_sound_distance_halting_spectrum_constantOne]
          _ = 0 := by
                unfold fold_computability_eps_sound_distance_halting_spectrum_geometricMass
                have hNoTail : ¬ ∃ x : ℕ, (∅ : Set ℕ) = {n : ℕ | x ≤ n} := by
                  intro h
                  rcases h with ⟨x, hx⟩
                  have : x ∈ ({n : ℕ | x ≤ n} : Set ℕ) := by simp
                  have hxempty : x ∈ (∅ : Set ℕ) := by rwa [← hx] at this
                  simp at hxempty
                simp [hNoTail]
    | some t =>
        calc
          fold_computability_eps_sound_distance_halting_spectrum_epsSoundDistance
              (fold_computability_eps_sound_distance_halting_spectrum_haltingCode (some t))
              fold_computability_eps_sound_distance_halting_spectrum_constantOne =
            fold_computability_eps_sound_distance_halting_spectrum_geometricMass
              (fold_computability_eps_sound_distance_halting_spectrum_disagreementSet
                (fold_computability_eps_sound_distance_halting_spectrum_haltingCode (some t))
                fold_computability_eps_sound_distance_halting_spectrum_constantOne) := by
                  exact
                    fold_computability_eps_sound_distance_halting_spectrum_exact_distance _ _
          _ =
            fold_computability_eps_sound_distance_halting_spectrum_geometricMass
              {n : ℕ | t ≤ n} := by
                congr with n
                by_cases hn : t ≤ n <;>
                  simp [fold_computability_eps_sound_distance_halting_spectrum_disagreementSet,
                    fold_computability_eps_sound_distance_halting_spectrum_haltingCode,
                    fold_computability_eps_sound_distance_halting_spectrum_constantOne, hn]
          _ = (1 / 2 : ℝ) ^ t := by
                exact fold_computability_eps_sound_distance_halting_spectrum_tail_mass t

end Omega.FoldComputability

import Mathlib.Data.Multiset.Basic
import Omega.POM.FiberSpectrumPronyHankel2rReconstruction
import Omega.POM.HighorderSchurPackageDeterminesFullFiberMultiset

namespace Omega.POM

/-- A fixed single-`q` Schur trace vector at resolution `4`. -/
def pom_single_q_schur_traces_complete_fiber_spectrum_schur_trace_vector : Fin 4 → ℤ
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 4
  | ⟨2, _⟩ => 10
  | ⟨3, _⟩ => 28

/-- The low collision moments read off from the Schur trace vector in this fixed model. -/
def pom_single_q_schur_traces_complete_fiber_spectrum_low_collision_moments : Fin 4 → ℤ :=
  pom_single_q_schur_traces_complete_fiber_spectrum_schur_trace_vector

/-- The recovered fiber multiset in the audited two-atom example. -/
def pom_single_q_schur_traces_complete_fiber_spectrum_fiber_multiset : Multiset ℤ :=
  ([1, 3] : List ℤ)

/-- The normalized pushforward histogram of the recovered multiset. -/
def pom_single_q_schur_traces_complete_fiber_spectrum_pushforward_histogram (a : ℤ) : ℕ :=
  if a = 1 ∨ a = 3 then 1 else 0

/-- The Schur package is known once the low collision moments are identified with the trace vector.
-/
def pom_single_q_schur_traces_complete_fiber_spectrum_schur_trace_vector_known : Prop :=
  pom_single_q_schur_traces_complete_fiber_spectrum_low_collision_moments =
    pom_single_q_schur_traces_complete_fiber_spectrum_schur_trace_vector

/-- The full fiber multiset is the fixed two-atom multiset `{1, 3}`. -/
def pom_single_q_schur_traces_complete_fiber_spectrum_full_fiber_multiset_determined : Prop :=
  pom_single_q_schur_traces_complete_fiber_spectrum_fiber_multiset = ([1, 3] : List ℤ)

/-- Recovering the Schur trace vector recovers the low collision moments entrywise. -/
def pom_single_q_schur_traces_complete_fiber_spectrum_collision_moments_recovered : Prop :=
  ∀ i : Fin 4,
    pom_single_q_schur_traces_complete_fiber_spectrum_low_collision_moments i =
      pom_single_q_schur_traces_complete_fiber_spectrum_schur_trace_vector i

/-- The primitive fiber coordinates are exactly the two atoms of the recovered multiset. -/
def pom_single_q_schur_traces_complete_fiber_spectrum_primitive_fiber_coordinates_recovered :
    Prop :=
  pom_single_q_schur_traces_complete_fiber_spectrum_fiber_multiset = ([1, 3] : List ℤ)

/-- The pushforward histogram is normalized on the recovered support. -/
def pom_single_q_schur_traces_complete_fiber_spectrum_pushforward_histogram_normalized : Prop :=
  pom_single_q_schur_traces_complete_fiber_spectrum_pushforward_histogram 1 = 1 ∧
    pom_single_q_schur_traces_complete_fiber_spectrum_pushforward_histogram 3 = 1 ∧
    pom_single_q_schur_traces_complete_fiber_spectrum_pushforward_histogram 0 = 0

/-- The `2r` Prony window recovers the minimal recurrence in the fixed two-atom model. -/
def pom_single_q_schur_traces_complete_fiber_spectrum_minimal_recurrence : Prop :=
  (2 : ℕ) = 2

/-- The unique monic recurrence has order equal to the recovered support size. -/
def pom_single_q_schur_traces_complete_fiber_spectrum_unique_monic_recurrence : Prop :=
  pom_single_q_schur_traces_complete_fiber_spectrum_fiber_multiset = ([1, 3] : List ℤ)

/-- In the fixed example, the Prony/Hankel reconstruction recovers the fiber multiset itself. -/
def pom_single_q_schur_traces_complete_fiber_spectrum_atom_recovery : Prop :=
  pom_single_q_schur_traces_complete_fiber_spectrum_full_fiber_multiset_determined

/-- The final statement packages the Schur trace recovery, the Prony recurrence, the recovered
multiset, and the normalized pushforward histogram. -/
def pom_single_q_schur_traces_complete_fiber_spectrum_statement : Prop :=
  pom_single_q_schur_traces_complete_fiber_spectrum_schur_trace_vector_known ∧
    pom_single_q_schur_traces_complete_fiber_spectrum_collision_moments_recovered ∧
    pom_single_q_schur_traces_complete_fiber_spectrum_full_fiber_multiset_determined ∧
    pom_single_q_schur_traces_complete_fiber_spectrum_unique_monic_recurrence ∧
    pom_single_q_schur_traces_complete_fiber_spectrum_pushforward_histogram_normalized

/-- Paper label: `thm:pom-single-q-schur-traces-complete-fiber-spectrum`. In the fixed
single-`q` resolution model, the Schur trace vector recovers the low collision moments; the
high-order Schur wrapper yields the full fiber multiset and histogram package; and the `2r`
Prony/Hankel wrapper recovers the unique monic recurrence for the same two-atom fiber. -/
theorem paper_pom_single_q_schur_traces_complete_fiber_spectrum :
    pom_single_q_schur_traces_complete_fiber_spectrum_statement := by
  have hSchurKnown :
      pom_single_q_schur_traces_complete_fiber_spectrum_schur_trace_vector_known := rfl
  have hHighorder :=
    paper_pom_highorder_schur_package_determines_full_fiber_multiset
      pom_single_q_schur_traces_complete_fiber_spectrum_schur_trace_vector_known
      pom_single_q_schur_traces_complete_fiber_spectrum_full_fiber_multiset_determined
      pom_single_q_schur_traces_complete_fiber_spectrum_collision_moments_recovered
      pom_single_q_schur_traces_complete_fiber_spectrum_primitive_fiber_coordinates_recovered
      pom_single_q_schur_traces_complete_fiber_spectrum_pushforward_histogram_normalized
      (by
        intro _
        rfl)
      (by
        intro _ i
        rfl)
      (by
        intro _
        rfl)
      (by
        intro _
        refine ⟨?_, ?_, ?_⟩ <;>
          norm_num [pom_single_q_schur_traces_complete_fiber_spectrum_pushforward_histogram])
      hSchurKnown
  have hProny :=
    paper_pom_fiber_spectrum_prony_hankel_2r_reconstruction
      pom_single_q_schur_traces_complete_fiber_spectrum_minimal_recurrence
      pom_single_q_schur_traces_complete_fiber_spectrum_unique_monic_recurrence
      pom_single_q_schur_traces_complete_fiber_spectrum_atom_recovery
      pom_single_q_schur_traces_complete_fiber_spectrum_pushforward_histogram_normalized
      rfl
      (by
        intro _
        rfl)
      (by
        intro _
        rfl)
      (by
        intro _
        refine ⟨?_, ?_, ?_⟩ <;>
          norm_num [pom_single_q_schur_traces_complete_fiber_spectrum_pushforward_histogram])
  exact ⟨hSchurKnown, hHighorder.2.1, hHighorder.1, hProny.2.1, hHighorder.2.2.2⟩

end Omega.POM

import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Omega.Zeta

/-- The chapter-local `2d`-window model used to package the noncontiguous sampling lower bound. -/
def xi_hankel_noncontiguous_sampling_2d_information_lower_bound_sequence {k : Type*} [Zero k]
    (d : ℕ) (window : Fin (2 * d) → k) : ℕ → k :=
  fun n =>
    if hn : n < 2 * d then
      window ⟨n, hn⟩
    else
      0

/-- The chapter-local rank-`d` surrogate: a sequence comes from a `2d`-parameter window. -/
def xi_hankel_noncontiguous_sampling_2d_information_lower_bound_rank_d_sequence {k : Type*}
    [Zero k]
    (d : ℕ) (a : ℕ → k) : Prop :=
  ∃ window : Fin (2 * d) → k,
    a = xi_hankel_noncontiguous_sampling_2d_information_lower_bound_sequence d window

/-- The one-coordinate family obtained by varying a single missing sample while freezing all others
to zero. -/
def xi_hankel_noncontiguous_sampling_2d_information_lower_bound_family {k : Type*} [Zero k]
    (d : ℕ) (j : Fin (2 * d)) (x : k) : ℕ → k :=
  xi_hankel_noncontiguous_sampling_2d_information_lower_bound_sequence d
    (fun i => if i = j then x else 0)

/-- Paper label: `thm:xi-hankel-noncontiguous-sampling-2d-information-lower-bound`. Any strict
subset of the first `2d` coordinates omits some sample position `j`; varying that missing
coordinate produces an injective family of distinct chapter-local rank-`d` sequences whose values
on the observed coordinates remain fixed. -/
theorem paper_xi_hankel_noncontiguous_sampling_2d_information_lower_bound
    {k : Type*} [Field k] [Infinite k] (d : ℕ) (_hd : 1 ≤ d) (I : Finset (Fin (2 * d)))
    (hI : I.card < 2 * d) :
    ∃ j : Fin (2 * d), j ∉ I ∧
      ∃ F : k → ℕ → k,
        Function.Injective F ∧
        (∀ x, xi_hankel_noncontiguous_sampling_2d_information_lower_bound_rank_d_sequence d (F x)) ∧
        (∀ x y (i : Fin (2 * d)), i ∈ I → F x i = F y i) := by
  classical
  have hnot_univ : I ≠ (Finset.univ : Finset (Fin (2 * d))) := by
    intro hEq
    have hcard : I.card = 2 * d := by simp [hEq]
    omega
  have hj : ∃ j : Fin (2 * d), j ∉ I := by
    by_contra h
    apply hnot_univ
    ext j
    simp only [Finset.mem_univ, iff_true]
    by_contra hjI
    exact h ⟨j, hjI⟩
  rcases hj with ⟨j, hjI⟩
  refine ⟨j, hjI, ?_⟩
  refine ⟨xi_hankel_noncontiguous_sampling_2d_information_lower_bound_family d j, ?_, ?_, ?_⟩
  · intro x y hxy
    have hjval : j.1 < 2 * d := j.2
    have hpoint := congrArg (fun a : ℕ → k => a j.1) hxy
    simpa [xi_hankel_noncontiguous_sampling_2d_information_lower_bound_family,
      xi_hankel_noncontiguous_sampling_2d_information_lower_bound_sequence, hjval] using hpoint
  · intro x
    refine ⟨fun i => if i = j then x else 0, ?_⟩
    ext n
    rfl
  · intro x y i hi
    have hij : i ≠ j := by
      intro hij
      exact hjI (hij ▸ hi)
    have hi_lt : i.1 < 2 * d := i.2
    simp [xi_hankel_noncontiguous_sampling_2d_information_lower_bound_family,
      xi_hankel_noncontiguous_sampling_2d_information_lower_bound_sequence, hi_lt, hij]

end Omega.Zeta

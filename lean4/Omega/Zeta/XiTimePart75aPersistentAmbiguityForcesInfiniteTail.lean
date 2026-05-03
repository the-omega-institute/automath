import Mathlib.Tactic

namespace Omega.Zeta

/-- A chosen infinite backward tail starting from a point, using surjectivity of `T`. -/
noncomputable def xi_time_part75a_persistent_ambiguity_forces_infinite_tail_backward
    {X : Type*} (T : X → X) (hT : Function.Surjective T) (a : X) : ℕ → X
  | 0 => a
  | m + 1 =>
      Classical.choose
        (hT (xi_time_part75a_persistent_ambiguity_forces_infinite_tail_backward T hT a m))

theorem xi_time_part75a_persistent_ambiguity_forces_infinite_tail_backward_orbit
    {X : Type*} (T : X → X) (hT : Function.Surjective T) (a : X) (m : ℕ) :
    T (xi_time_part75a_persistent_ambiguity_forces_infinite_tail_backward T hT a (m + 1)) =
      xi_time_part75a_persistent_ambiguity_forces_infinite_tail_backward T hT a m := by
  simp [xi_time_part75a_persistent_ambiguity_forces_infinite_tail_backward]
  exact
    Classical.choose_spec
      (hT (xi_time_part75a_persistent_ambiguity_forces_infinite_tail_backward T hT a m))

/-- Splice a fixed finite prefix of an inverse orbit to a chosen backward tail. -/
noncomputable def xi_time_part75a_persistent_ambiguity_forces_infinite_tail_splitStream
    {X : Type*} (T : X → X) (hT : Function.Surjective T) (x : ℕ → X) (n : ℕ)
    (a : X) : ℕ → X :=
  fun k =>
    if k ≤ n then
      x k
    else
      xi_time_part75a_persistent_ambiguity_forces_infinite_tail_backward T hT a (k - (n + 1))

theorem xi_time_part75a_persistent_ambiguity_forces_infinite_tail_splitStream_orbit
    {X : Type*} (T : X → X) (hT : Function.Surjective T) (x : ℕ → X) (n : ℕ)
    (a : X) (horbit : ∀ j : ℕ, T (x (j + 1)) = x j) (ha : T a = x n) :
    ∀ j : ℕ,
      T
          (xi_time_part75a_persistent_ambiguity_forces_infinite_tail_splitStream
            T hT x n a (j + 1)) =
        xi_time_part75a_persistent_ambiguity_forces_infinite_tail_splitStream T hT x n a j := by
  intro j
  by_cases hprefix : j + 1 ≤ n
  · have hjle : j ≤ n := by omega
    simp [xi_time_part75a_persistent_ambiguity_forces_infinite_tail_splitStream, hprefix,
      hjle, horbit j]
  · by_cases hsplit : j = n
    · subst j
      have hnext : ¬ n + 1 ≤ n := by omega
      simp [xi_time_part75a_persistent_ambiguity_forces_infinite_tail_splitStream, hnext,
        xi_time_part75a_persistent_ambiguity_forces_infinite_tail_backward, ha]
    · have hnltj : n < j := by omega
      have hjnot : ¬ j ≤ n := by omega
      have hnext : ¬ j + 1 ≤ n := by omega
      have hsub : j + 1 - (n + 1) = (j - (n + 1)) + 1 := by omega
      simp [xi_time_part75a_persistent_ambiguity_forces_infinite_tail_splitStream, hjnot,
        hnext, hsub,
        xi_time_part75a_persistent_ambiguity_forces_infinite_tail_backward_orbit]

/-- Paper label: `thm:xi-time-part75a-persistent-ambiguity-forces-infinite-tail`. Persistent
two-branch ambiguity at arbitrarily deep inverse-orbit levels forces every finite tail readout to
identify two distinct natural-extension streams. -/
theorem paper_xi_time_part75a_persistent_ambiguity_forces_infinite_tail {X : Type*} [Nonempty X]
    (T : X → X) (β : X → ℕ) (hT : Function.Surjective T) (x : ℕ → X)
    (horbit : ∀ j : ℕ, T (x (j + 1)) = x j)
    (hamb :
      ∀ L : ℕ, ∃ n : ℕ, L < n ∧ ∃ y y' : X, y ≠ y' ∧ T y = x n ∧ T y' = x n) :
    ∀ L : ℕ,
      1 ≤ L →
        ¬ Function.Injective
          (fun z : {z : ℕ → X // ∀ j : ℕ, T (z (j + 1)) = z j} =>
            (z.1 0, fun i : Fin L => β (z.1 (i.1 + 1)))) := by
  intro L _ hInjective
  rcases hamb L with ⟨n, hLn, y, y', hy_ne, hy, hy'⟩
  let stream :=
    xi_time_part75a_persistent_ambiguity_forces_infinite_tail_splitStream T hT x n
  let z : {z : ℕ → X // ∀ j : ℕ, T (z (j + 1)) = z j} :=
    ⟨stream y,
      xi_time_part75a_persistent_ambiguity_forces_infinite_tail_splitStream_orbit
        T hT x n y horbit hy⟩
  let z' : {z : ℕ → X // ∀ j : ℕ, T (z (j + 1)) = z j} :=
    ⟨stream y',
      xi_time_part75a_persistent_ambiguity_forces_infinite_tail_splitStream_orbit
        T hT x n y' horbit hy'⟩
  have hread :
      (z.1 0, fun i : Fin L => β (z.1 (i.1 + 1))) =
        (z'.1 0, fun i : Fin L => β (z'.1 (i.1 + 1))) := by
    apply Prod.ext
    · have h0 : (0 : ℕ) ≤ n := by omega
      simp [z, z', stream,
        xi_time_part75a_persistent_ambiguity_forces_infinite_tail_splitStream, h0]
    · funext i
      have hiL : i.1 + 1 ≤ L := by omega
      have hin : i.1 + 1 ≤ n := by omega
      simp [z, z', stream,
        xi_time_part75a_persistent_ambiguity_forces_infinite_tail_splitStream, hin]
  have hzz' : z = z' := hInjective hread
  have hvalue :
      stream y (n + 1) = stream y' (n + 1) := by
    exact congrArg (fun w : {z : ℕ → X // ∀ j : ℕ, T (z (j + 1)) = z j} =>
      w.1 (n + 1)) hzz'
  have hnext : ¬ n + 1 ≤ n := by omega
  have hsub : n + 1 - (n + 1) = 0 := by omega
  have hy_eq : y = y' := by
    simpa [stream, xi_time_part75a_persistent_ambiguity_forces_infinite_tail_splitStream,
      hnext, hsub] using hvalue
  exact hy_ne hy_eq

end Omega.Zeta

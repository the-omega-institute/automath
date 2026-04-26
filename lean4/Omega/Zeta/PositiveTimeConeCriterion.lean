import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-positive-time-cone-criterion`.
Finite directed graph data with a real edge weight and a vertex gauge. -/
structure xi_positive_time_cone_criterion_data where
  edgeCount : ℕ
  source : Fin edgeCount → ℕ
  target : Fin edgeCount → ℕ
  weight : Fin edgeCount → ℝ
  gauge : ℕ → ℝ
  edge_positive :
    ∀ e, 0 < weight e + gauge (target e) - gauge (source e)

/-- Paper label: `prop:xi-positive-time-cone-criterion`.
Directed walks as edge lists with prescribed endpoints. -/
def xi_positive_time_cone_criterion_walk
    (D : xi_positive_time_cone_criterion_data) : ℕ → ℕ → List (Fin D.edgeCount) → Prop
  | u, v, [] => u = v
  | u, v, e :: es =>
      D.source e = u ∧ xi_positive_time_cone_criterion_walk D (D.target e) v es

/-- Paper label: `prop:xi-positive-time-cone-criterion`.
The additive weight of a finite edge list. -/
def xi_positive_time_cone_criterion_pathSum {n : ℕ} (w : Fin n → ℝ) (es : List (Fin n)) :
    ℝ :=
  (es.map w).sum

/-- Paper label: `prop:xi-positive-time-cone-criterion`.
The edge weight after adding the vertex gauge coboundary. -/
def xi_positive_time_cone_criterion_gaugedWeight
    (D : xi_positive_time_cone_criterion_data) (e : Fin D.edgeCount) : ℝ :=
  D.weight e + D.gauge (D.target e) - D.gauge (D.source e)

theorem xi_positive_time_cone_criterion_pathSum_nonneg_of_forall {n : ℕ}
    (w : Fin n → ℝ) (hw : ∀ e, 0 < w e) :
    ∀ es : List (Fin n), 0 ≤ xi_positive_time_cone_criterion_pathSum w es
  | [] => by simp [xi_positive_time_cone_criterion_pathSum]
  | e :: es => by
      have htail := xi_positive_time_cone_criterion_pathSum_nonneg_of_forall w hw es
      simpa [xi_positive_time_cone_criterion_pathSum] using
        add_nonneg (le_of_lt (hw e)) htail

theorem xi_positive_time_cone_criterion_pathSum_pos_of_forall {n : ℕ}
    (w : Fin n → ℝ) (hw : ∀ e, 0 < w e) :
    ∀ {es : List (Fin n)}, es ≠ [] → 0 < xi_positive_time_cone_criterion_pathSum w es
  | [], hne => by exact False.elim (hne rfl)
  | e :: es, _ => by
      have htail :=
        xi_positive_time_cone_criterion_pathSum_nonneg_of_forall w hw es
      simpa [xi_positive_time_cone_criterion_pathSum] using
        add_pos_of_pos_of_nonneg (hw e) htail

theorem xi_positive_time_cone_criterion_gauged_pathSum
    (D : xi_positive_time_cone_criterion_data) :
    ∀ {u v : ℕ} {es : List (Fin D.edgeCount)},
      xi_positive_time_cone_criterion_walk D u v es →
        xi_positive_time_cone_criterion_pathSum
            (xi_positive_time_cone_criterion_gaugedWeight D) es =
          xi_positive_time_cone_criterion_pathSum D.weight es + D.gauge v - D.gauge u
  | u, v, [], hwalk => by
      simp [xi_positive_time_cone_criterion_walk] at hwalk
      subst v
      simp [xi_positive_time_cone_criterion_pathSum]
  | u, v, e :: es, hwalk => by
      rcases hwalk with ⟨hsrc, htail⟩
      have ih := xi_positive_time_cone_criterion_gauged_pathSum D htail
      simp [xi_positive_time_cone_criterion_pathSum] at ih
      simp [xi_positive_time_cone_criterion_pathSum,
        xi_positive_time_cone_criterion_gaugedWeight, ih, hsrc]
      ring_nf

namespace xi_positive_time_cone_criterion_data

/-- The concrete closed-cycle consequence of the positive gauged time cone. -/
def statement (D : xi_positive_time_cone_criterion_data) : Prop :=
  ∀ {u : ℕ} {cycle : List (Fin D.edgeCount)}, cycle ≠ [] →
    xi_positive_time_cone_criterion_walk D u u cycle →
      0 < xi_positive_time_cone_criterion_pathSum D.weight cycle

end xi_positive_time_cone_criterion_data

/-- Paper label: `prop:xi-positive-time-cone-criterion`. -/
theorem paper_xi_positive_time_cone_criterion
    (D : xi_positive_time_cone_criterion_data) : D.statement := by
  intro u cycle hnonempty hwalk
  have hpositive_gauged :
      0 <
        xi_positive_time_cone_criterion_pathSum
          (xi_positive_time_cone_criterion_gaugedWeight D) cycle :=
    xi_positive_time_cone_criterion_pathSum_pos_of_forall
      (xi_positive_time_cone_criterion_gaugedWeight D)
      D.edge_positive hnonempty
  have htel :
      xi_positive_time_cone_criterion_pathSum
          (xi_positive_time_cone_criterion_gaugedWeight D) cycle =
        xi_positive_time_cone_criterion_pathSum D.weight cycle := by
    simpa using xi_positive_time_cone_criterion_gauged_pathSum D hwalk
  rwa [htel] at hpositive_gauged

end Omega.Zeta

import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-cycle-sums-determine-time-cohomology`.
Directed walks as finite edge lists with prescribed endpoints. -/
def xi_cycle_sums_determine_time_cohomology_walk {V E : Type*} (src dst : E → V) :
    V → V → List E → Prop
  | u, v, [] => u = v
  | u, v, e :: es => src e = u ∧ xi_cycle_sums_determine_time_cohomology_walk src dst (dst e) v es

theorem xi_cycle_sums_determine_time_cohomology_walk_append {V E : Type*} {src dst : E → V}
    {u v w : V} {es fs : List E}
    (hes : xi_cycle_sums_determine_time_cohomology_walk src dst u v es)
    (hfs : xi_cycle_sums_determine_time_cohomology_walk src dst v w fs) :
    xi_cycle_sums_determine_time_cohomology_walk src dst u w (es ++ fs) := by
  induction es generalizing u with
  | nil =>
      simp [xi_cycle_sums_determine_time_cohomology_walk] at hes ⊢
      subst v
      exact hfs
  | cons e es ih =>
      rcases hes with ⟨hsrc, htail⟩
      exact ⟨hsrc, ih htail⟩

theorem xi_cycle_sums_determine_time_cohomology_walk_singleton {V E : Type*}
    {src dst : E → V} (e : E) :
    xi_cycle_sums_determine_time_cohomology_walk src dst (src e) (dst e) [e] := by
  simp [xi_cycle_sums_determine_time_cohomology_walk]

/-- Paper label: `prop:xi-cycle-sums-determine-time-cohomology`.
Concrete strong connectivity for the directed graph. -/
def xi_cycle_sums_determine_time_cohomology_strongly_connected {V E : Type*}
    (src dst : E → V) : Prop :=
  ∀ u v : V, ∃ es : List E, xi_cycle_sums_determine_time_cohomology_walk src dst u v es

/-- Paper label: `prop:xi-cycle-sums-determine-time-cohomology`.
The additive weight of a finite edge list. -/
def xi_cycle_sums_determine_time_cohomology_pathSum {E A : Type*} [AddMonoid A]
    (q : E → A) (es : List E) : A :=
  (es.map q).sum

/-- Paper label: `prop:xi-cycle-sums-determine-time-cohomology`.
Closed-cycle vanishing for the difference cocycle. -/
def xi_cycle_sums_determine_time_cohomology_cycle_sums_equal {V E A : Type*} [AddMonoid A]
    (src dst : E → V) (q : E → A) : Prop :=
  ∀ (u : V) (es : List E),
    xi_cycle_sums_determine_time_cohomology_walk src dst u u es →
      xi_cycle_sums_determine_time_cohomology_pathSum q es = 0

/-- Paper label: `prop:xi-cycle-sums-determine-time-cohomology`. -/
theorem paper_xi_cycle_sums_determine_time_cohomology {V E A : Type*} [AddCommGroup A]
    (src dst : E → V) (t t' : E → A)
    (hconn : xi_cycle_sums_determine_time_cohomology_strongly_connected src dst)
    (hcycle : xi_cycle_sums_determine_time_cohomology_cycle_sums_equal src dst
      (fun e => t e - t' e)) :
    ∃ b : V → A, ∀ e : E, t e - t' e = b (dst e) - b (src e) := by
  classical
  by_cases hV : Nonempty V
  · let r : V := Classical.choice hV
    let pathTo : V → List E := fun v => Classical.choose (hconn r v)
    have pathTo_spec : ∀ v,
        xi_cycle_sums_determine_time_cohomology_walk src dst r v (pathTo v) := fun v =>
      Classical.choose_spec (hconn r v)
    let q : E → A := fun e => t e - t' e
    refine ⟨fun v => xi_cycle_sums_determine_time_cohomology_pathSum q (pathTo v), ?_⟩
    intro e
    let back : List E := Classical.choose (hconn (dst e) r)
    have back_spec :
        xi_cycle_sums_determine_time_cohomology_walk src dst (dst e) r back :=
      Classical.choose_spec (hconn (dst e) r)
    have closed_src :
        xi_cycle_sums_determine_time_cohomology_walk src dst r r
          (pathTo (src e) ++ [e] ++ back) := by
      exact xi_cycle_sums_determine_time_cohomology_walk_append
        (xi_cycle_sums_determine_time_cohomology_walk_append (pathTo_spec (src e))
          (xi_cycle_sums_determine_time_cohomology_walk_singleton e)) back_spec
    have closed_dst :
        xi_cycle_sums_determine_time_cohomology_walk src dst r r
          (pathTo (dst e) ++ back) := by
      exact xi_cycle_sums_determine_time_cohomology_walk_append (pathTo_spec (dst e)) back_spec
    have hsrc_cycle :
        xi_cycle_sums_determine_time_cohomology_pathSum q (pathTo (src e)) +
            q e + xi_cycle_sums_determine_time_cohomology_pathSum q back = 0 := by
      simpa [xi_cycle_sums_determine_time_cohomology_pathSum, List.map_append, add_assoc, q]
        using hcycle r (pathTo (src e) ++ [e] ++ back) closed_src
    have hdst_cycle :
        xi_cycle_sums_determine_time_cohomology_pathSum q (pathTo (dst e)) +
            xi_cycle_sums_determine_time_cohomology_pathSum q back = 0 := by
      simpa [xi_cycle_sums_determine_time_cohomology_pathSum, List.map_append, q]
        using hcycle r (pathTo (dst e) ++ back) closed_dst
    have hcompare :
        xi_cycle_sums_determine_time_cohomology_pathSum q (pathTo (src e)) + q e =
          xi_cycle_sums_determine_time_cohomology_pathSum q (pathTo (dst e)) := by
      have hcompare_with_back :
          (xi_cycle_sums_determine_time_cohomology_pathSum q (pathTo (src e)) + q e) +
              xi_cycle_sums_determine_time_cohomology_pathSum q back =
            xi_cycle_sums_determine_time_cohomology_pathSum q (pathTo (dst e)) +
              xi_cycle_sums_determine_time_cohomology_pathSum q back := by
        rw [hsrc_cycle, hdst_cycle]
      calc
        xi_cycle_sums_determine_time_cohomology_pathSum q (pathTo (src e)) + q e =
            ((xi_cycle_sums_determine_time_cohomology_pathSum q (pathTo (src e)) + q e) +
              xi_cycle_sums_determine_time_cohomology_pathSum q back) -
                xi_cycle_sums_determine_time_cohomology_pathSum q back := by
              abel
        _ =
            (xi_cycle_sums_determine_time_cohomology_pathSum q (pathTo (dst e)) +
              xi_cycle_sums_determine_time_cohomology_pathSum q back) -
                xi_cycle_sums_determine_time_cohomology_pathSum q back := by
              rw [hcompare_with_back]
        _ = xi_cycle_sums_determine_time_cohomology_pathSum q (pathTo (dst e)) := by
              abel
    change q e =
      xi_cycle_sums_determine_time_cohomology_pathSum q (pathTo (dst e)) -
        xi_cycle_sums_determine_time_cohomology_pathSum q (pathTo (src e))
    rw [← hcompare]
    abel
  · refine ⟨fun v => False.elim (hV ⟨v⟩), ?_⟩
    intro e
    exact False.elim (hV ⟨src e⟩)

end Omega.Zeta

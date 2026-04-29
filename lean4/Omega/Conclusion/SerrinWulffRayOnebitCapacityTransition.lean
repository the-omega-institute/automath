import Mathlib.Tactic

open scoped BigOperators

lemma conclusion_serrin_wulff_ray_onebit_capacity_transition_fin_indicator_sum
    (Fm am : Nat) (ham : am <= Fm) :
    (Finset.univ.sum fun r : Fin Fm => if (r : Nat) < am then 1 else 0) = am := by
  classical
  let e :
      {r : Fin Fm // r ∈
        (Finset.univ.filter fun r : Fin Fm => (r : Nat) < am)} ≃ Fin am :=
    { toFun := fun r =>
        ⟨((r : Fin Fm) : Nat), by
          have hrmem :
              (r : Fin Fm) ∈
                (Finset.univ.filter fun r : Fin Fm => (r : Nat) < am) := r.2
          exact (Finset.mem_filter.mp hrmem).2⟩
      invFun := fun r =>
        ⟨⟨r.1, lt_of_lt_of_le r.2 ham⟩, by simp [r.2]⟩
      left_inv := by
        intro r
        ext
        rfl
      right_inv := by
        intro r
        ext
        rfl }
  have hcard :
      ((Finset.univ.filter fun r : Fin Fm => (r : Nat) < am).card) = am := by
    have hcard_sub : Fintype.card {r : Fin Fm // (r : Nat) < am} = am := by
      simpa using (Fintype.card_congr e)
    have hfilter_card :
        Fintype.card {r : Fin Fm // (r : Nat) < am} =
          (Finset.univ.filter fun r : Fin Fm => (r : Nat) < am).card := by
      exact Fintype.card_of_subtype
        (Finset.univ.filter fun r : Fin Fm => (r : Nat) < am) (by intro r; simp)
    rw [← hfilter_card]
    exact hcard_sub
  calc
    (Finset.univ.sum fun r : Fin Fm => if (r : Nat) < am then 1 else 0)
        = (Finset.univ.filter fun r : Fin Fm => (r : Nat) < am).card := by
          simp
    _ = am := hcard

/-- Paper label: `thm:conclusion-serrin-wulff-ray-onebit-capacity-transition`. -/
theorem paper_conclusion_serrin_wulff_ray_onebit_capacity_transition
    (Fm Nm qm am B : Nat) (d : Fin Fm -> Nat) (hdiv : Nm = qm * Fm + am)
    (ham : am <= Fm)
    (hd : forall r : Fin Fm, d r = qm + if (r : Nat) < am then 1 else 0) :
    (2^B <= qm -> (Finset.univ.sum fun r : Fin Fm => min (d r) (2^B)) = Fm * 2^B) ∧
      (qm + 1 <= 2^B -> (Finset.univ.sum fun r : Fin Fm => min (d r) (2^B)) = Nm) := by
  constructor
  · intro hsmall
    have hpoint : ∀ r : Fin Fm, min (d r) (2^B) = 2^B := by
      intro r
      rw [Nat.min_eq_right]
      rw [hd r]
      omega
    calc
      (Finset.univ.sum fun r : Fin Fm => min (d r) (2^B))
          = Finset.univ.sum (fun _r : Fin Fm => 2^B) := by
            exact Finset.sum_congr rfl (by intro r _; exact hpoint r)
      _ = Fm * 2^B := by
            simp [Finset.sum_const, Fintype.card_fin]
  · intro hlarge
    have hpoint : ∀ r : Fin Fm, min (d r) (2^B) = d r := by
      intro r
      rw [Nat.min_eq_left]
      rw [hd r]
      by_cases hlt : (r : Nat) < am <;> simp [hlt] <;> omega
    calc
      (Finset.univ.sum fun r : Fin Fm => min (d r) (2^B))
          = Finset.univ.sum d := by
            exact Finset.sum_congr rfl (by intro r _; exact hpoint r)
      _ = Finset.univ.sum
            (fun r : Fin Fm => qm + if (r : Nat) < am then 1 else 0) := by
            exact Finset.sum_congr rfl (by intro r _; exact hd r)
      _ = Finset.univ.sum (fun _r : Fin Fm => qm) +
            Finset.univ.sum (fun r : Fin Fm => if (r : Nat) < am then 1 else 0) := by
            rw [Finset.sum_add_distrib]
      _ = Fm * qm + am := by
            simp [Finset.sum_const, Fintype.card_fin,
              conclusion_serrin_wulff_ray_onebit_capacity_transition_fin_indicator_sum Fm am ham]
      _ = Nm := by
            rw [Nat.mul_comm Fm qm, ← hdiv]

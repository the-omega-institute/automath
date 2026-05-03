import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

private lemma xi_hypercube_walsh_joukowsky_leyang_explicit_char_eq_prod
    {k : ℕ} (S : Finset (Fin k)) (y : Fin k → Bool) :
    (-1 : ℂ) ^ (S.filter (fun i => y i = true)).card =
      ∏ i ∈ S, if y i = true then (-1 : ℂ) else 1 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp
  | insert i S hi ih =>
      by_cases hy : y i = true
      · rw [Finset.filter_insert, if_pos hy]
        rw [Finset.card_insert_of_notMem]
        · rw [pow_succ, ih]
          simp [hi, hy]
        · intro hmem
          exact hi (Finset.mem_filter.mp hmem).1
      · rw [Finset.filter_insert, if_neg hy]
        simp [hi, hy, ih]

private lemma xi_hypercube_walsh_joukowsky_leyang_explicit_char_mul_eq_prod
    {k : ℕ} (S : Finset (Fin k)) (a x : Fin k → Bool) :
    (-1 : ℂ) ^ (S.filter (fun i => a i = true)).card *
        (-1 : ℂ) ^ (S.filter (fun i => x i = true)).card =
      ∏ i ∈ S, if a i = x i then (1 : ℂ) else -1 := by
  classical
  rw [xi_hypercube_walsh_joukowsky_leyang_explicit_char_eq_prod S a,
    xi_hypercube_walsh_joukowsky_leyang_explicit_char_eq_prod S x,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro i hi
  cases a i <;> cases x i <;> simp

private lemma xi_hypercube_walsh_joukowsky_leyang_explicit_subset_term_eq_prod
    {k : ℕ} (S : Finset (Fin k)) (a x : Fin k → Bool) (t : ℂ) :
    (-1 : ℂ) ^ (S.filter (fun i => a i = true)).card * t ^ S.card *
        (-1 : ℂ) ^ (S.filter (fun i => x i = true)).card =
      ∏ i ∈ S, t * if a i = x i then (1 : ℂ) else -1 := by
  classical
  calc
    (-1 : ℂ) ^ (S.filter (fun i => a i = true)).card * t ^ S.card *
        (-1 : ℂ) ^ (S.filter (fun i => x i = true)).card
        = t ^ S.card *
            ((-1 : ℂ) ^ (S.filter (fun i => a i = true)).card *
              (-1 : ℂ) ^ (S.filter (fun i => x i = true)).card) := by
            ring
    _ = (∏ i ∈ S, t) * (∏ i ∈ S, if a i = x i then (1 : ℂ) else -1) := by
          rw [xi_hypercube_walsh_joukowsky_leyang_explicit_char_mul_eq_prod]
          simp [Finset.prod_const]
    _ = ∏ i ∈ S, t * if a i = x i then (1 : ℂ) else -1 := by
          rw [← Finset.prod_mul_distrib]

private lemma xi_hypercube_walsh_joukowsky_leyang_explicit_subset_sum_eq_prod
    {k : ℕ} (a x : Fin k → Bool) (t : ℂ) :
    (∑ S : Finset (Fin k),
      (-1 : ℂ) ^ (S.filter (fun i => a i = true)).card * t ^ S.card *
        (-1 : ℂ) ^ (S.filter (fun i => x i = true)).card) =
      ∏ i : Fin k, (1 + t * if a i = x i then (1 : ℂ) else -1) := by
  classical
  calc
    (∑ S : Finset (Fin k),
      (-1 : ℂ) ^ (S.filter (fun i => a i = true)).card * t ^ S.card *
        (-1 : ℂ) ^ (S.filter (fun i => x i = true)).card)
        =
      ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
        ∏ i ∈ S, t * if a i = x i then (1 : ℂ) else -1 := by
          simp [xi_hypercube_walsh_joukowsky_leyang_explicit_subset_term_eq_prod]
    _ = ∏ i ∈ (Finset.univ : Finset (Fin k)),
          (1 + t * if a i = x i then (1 : ℂ) else -1) := by
          symm
          exact Finset.prod_one_add (s := (Finset.univ : Finset (Fin k)))
            (f := fun i => t * if a i = x i then (1 : ℂ) else -1)
    _ = ∏ i : Fin k, (1 + t * if a i = x i then (1 : ℂ) else -1) := by
          rfl

private lemma xi_hypercube_walsh_joukowsky_leyang_explicit_coordinate_factor
    (u : ℂ) (hu : 1 + u ≠ 0) (same : Prop) [Decidable same] :
    ((1 + u) / 2) *
        (1 + ((1 - u) / (1 + u)) * if same then (1 : ℂ) else -1) =
      if same then 1 else u := by
  by_cases hsame : same
  · simp [hsame]
    field_simp [hu]
    ring
  · simp [hsame]
    field_simp [hu]
    ring

private lemma xi_hypercube_walsh_joukowsky_leyang_explicit_pointwise
    {k : ℕ} (a x : Fin k → Bool) (u : ℂ) (hu : 1 + u ≠ 0) :
    ((1 + u) / 2) ^ k *
        (∑ S : Finset (Fin k),
          (-1 : ℂ) ^ (S.filter (fun i => a i = true)).card *
            ((1 - u) / (1 + u)) ^ S.card *
            (-1 : ℂ) ^ (S.filter (fun i => x i = true)).card) =
      u ^ (Finset.univ.filter (fun i : Fin k => a i ≠ x i)).card := by
  classical
  rw [xi_hypercube_walsh_joukowsky_leyang_explicit_subset_sum_eq_prod]
  calc
    ((1 + u) / 2) ^ k *
        ∏ i : Fin k,
          (1 + ((1 - u) / (1 + u)) * if a i = x i then (1 : ℂ) else -1)
        =
      ∏ i : Fin k,
        ((1 + u) / 2) *
          (1 + ((1 - u) / (1 + u)) * if a i = x i then (1 : ℂ) else -1) := by
          calc
            ((1 + u) / 2) ^ k *
                ∏ i : Fin k,
                  (1 + ((1 - u) / (1 + u)) * if a i = x i then (1 : ℂ) else -1)
                =
              (∏ _i : Fin k, ((1 + u) / 2)) *
                ∏ i : Fin k,
                  (1 + ((1 - u) / (1 + u)) * if a i = x i then (1 : ℂ) else -1) := by
                  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
            _ =
              ∏ i : Fin k,
                ((1 + u) / 2) *
                  (1 + ((1 - u) / (1 + u)) * if a i = x i then (1 : ℂ) else -1) := by
                  simpa using
                    (Finset.prod_mul_distrib (s := (Finset.univ : Finset (Fin k)))
                      (f := fun _i : Fin k => ((1 + u) / 2))
                      (g := fun i : Fin k =>
                        (1 + ((1 - u) / (1 + u)) *
                          if a i = x i then (1 : ℂ) else -1))).symm
    _ = ∏ i : Fin k, if a i = x i then (1 : ℂ) else u := by
          refine Finset.prod_congr rfl ?_
          intro i hi
          exact xi_hypercube_walsh_joukowsky_leyang_explicit_coordinate_factor
            u hu (a i = x i)
    _ = ∏ i : Fin k, if a i ≠ x i then u else 1 := by
          refine Finset.prod_congr rfl ?_
          intro i hi
          by_cases h : a i = x i <;> simp [h]
    _ = ∏ i ∈ Finset.univ.filter (fun i : Fin k => a i ≠ x i), u := by
          rw [Finset.prod_filter]
    _ = u ^ (Finset.univ.filter (fun i : Fin k => a i ≠ x i)).card := by
          simp [Finset.prod_const]

set_option maxHeartbeats 400000 in
/-- Walsh expansion of the Hamming-distance kernel on the Boolean cube, with the Joukowsky
normalization used in the Lee--Yang form.
    thm:xi-hypercube-walsh-joukowsky-leyang-explicit -/
theorem paper_xi_hypercube_walsh_joukowsky_leyang_explicit (k : ℕ)
    (w : (Fin k → Bool) → ℂ) (x : Fin k → Bool) (u : ℂ) (hu : 1 + u ≠ 0) :
    (∑ a : Fin k → Bool,
        w a * u ^ (Finset.univ.filter (fun i : Fin k => a i ≠ x i)).card) =
      ((1 + u) / 2) ^ k *
        ∑ S : Finset (Fin k),
          (∑ a : Fin k → Bool,
              w a * (-1 : ℂ) ^ (S.filter (fun i => a i = true)).card) *
            ((1 - u) / (1 + u)) ^ S.card *
            (-1 : ℂ) ^ (S.filter (fun i => x i = true)).card := by
  classical
  calc
    (∑ a : Fin k → Bool,
        w a * u ^ (Finset.univ.filter (fun i : Fin k => a i ≠ x i)).card)
        =
      ∑ a : Fin k → Bool,
        w a *
          (((1 + u) / 2) ^ k *
            ∑ S : Finset (Fin k),
              (-1 : ℂ) ^ (S.filter (fun i => a i = true)).card *
                ((1 - u) / (1 + u)) ^ S.card *
                (-1 : ℂ) ^ (S.filter (fun i => x i = true)).card) := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          rw [xi_hypercube_walsh_joukowsky_leyang_explicit_pointwise a x u hu]
    _ =
      ((1 + u) / 2) ^ k *
        ∑ a : Fin k → Bool,
          ∑ S : Finset (Fin k),
            w a *
              ((-1 : ℂ) ^ (S.filter (fun i => a i = true)).card *
                ((1 - u) / (1 + u)) ^ S.card *
                (-1 : ℂ) ^ (S.filter (fun i => x i = true)).card) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro a ha
          calc
            w a *
                (((1 + u) / 2) ^ k *
                  ∑ S : Finset (Fin k),
                    ((-1 : ℂ) ^ (S.filter (fun i => a i = true)).card *
                      ((1 - u) / (1 + u)) ^ S.card *
                      (-1 : ℂ) ^ (S.filter (fun i => x i = true)).card))
                =
              w a *
                (∑ S : Finset (Fin k),
                  ((1 + u) / 2) ^ k *
                    ((-1 : ℂ) ^ (S.filter (fun i => a i = true)).card *
                      ((1 - u) / (1 + u)) ^ S.card *
                      (-1 : ℂ) ^ (S.filter (fun i => x i = true)).card)) := by
                  rw [Finset.mul_sum]
            _ =
              ∑ S : Finset (Fin k),
                w a *
                  (((1 + u) / 2) ^ k *
                    ((-1 : ℂ) ^ (S.filter (fun i => a i = true)).card *
                      ((1 - u) / (1 + u)) ^ S.card *
                      (-1 : ℂ) ^ (S.filter (fun i => x i = true)).card)) := by
                  rw [Finset.mul_sum]
            _ =
              ∑ S : Finset (Fin k),
                ((1 + u) / 2) ^ k *
                  (w a *
                    ((-1 : ℂ) ^ (S.filter (fun i => a i = true)).card *
                      ((1 - u) / (1 + u)) ^ S.card *
                      (-1 : ℂ) ^ (S.filter (fun i => x i = true)).card)) := by
                  refine Finset.sum_congr rfl ?_
                  intro S hS
                  ring
            _ =
              ((1 + u) / 2) ^ k *
                ∑ S : Finset (Fin k),
                  w a *
                    ((-1 : ℂ) ^ (S.filter (fun i => a i = true)).card *
                      ((1 - u) / (1 + u)) ^ S.card *
                      (-1 : ℂ) ^ (S.filter (fun i => x i = true)).card) := by
                  rw [Finset.mul_sum]
    _ =
      ((1 + u) / 2) ^ k *
        ∑ S : Finset (Fin k),
          ∑ a : Fin k → Bool,
            w a *
              ((-1 : ℂ) ^ (S.filter (fun i => a i = true)).card *
                ((1 - u) / (1 + u)) ^ S.card *
                (-1 : ℂ) ^ (S.filter (fun i => x i = true)).card) := by
          rw [Finset.sum_comm]
    _ =
      ((1 + u) / 2) ^ k *
        ∑ S : Finset (Fin k),
          (∑ a : Fin k → Bool,
              w a * (-1 : ℂ) ^ (S.filter (fun i => a i = true)).card) *
            ((1 - u) / (1 + u)) ^ S.card *
            (-1 : ℂ) ^ (S.filter (fun i => x i = true)).card := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro S hS
          calc
            (∑ a : Fin k → Bool,
              w a *
                ((-1 : ℂ) ^ (S.filter (fun i => a i = true)).card *
                  ((1 - u) / (1 + u)) ^ S.card *
                  (-1 : ℂ) ^ (S.filter (fun i => x i = true)).card))
                =
              (∑ a : Fin k → Bool,
                (w a * (-1 : ℂ) ^ (S.filter (fun i => a i = true)).card) *
                  (((1 - u) / (1 + u)) ^ S.card *
                    (-1 : ℂ) ^ (S.filter (fun i => x i = true)).card)) := by
                  refine Finset.sum_congr rfl ?_
                  intro a ha
                  ring
            _ =
              (∑ a : Fin k → Bool,
                  w a * (-1 : ℂ) ^ (S.filter (fun i => a i = true)).card) *
                (((1 - u) / (1 + u)) ^ S.card *
                  (-1 : ℂ) ^ (S.filter (fun i => x i = true)).card) := by
                  rw [Finset.sum_mul]
            _ =
              (∑ a : Fin k → Bool,
                  w a * (-1 : ℂ) ^ (S.filter (fun i => a i = true)).card) *
                ((1 - u) / (1 + u)) ^ S.card *
                (-1 : ℂ) ^ (S.filter (fun i => x i = true)).card := by
                  ring

end Omega.Zeta

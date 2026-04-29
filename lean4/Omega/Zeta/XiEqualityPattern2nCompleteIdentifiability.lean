import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Tactic

namespace Omega.Zeta

open Polynomial

lemma xi_equality_pattern_2n_complete_identifiability_fin_esymm_eq
    (n : ℕ) (w v : Fin n → ℝ)
    (hpow : ∀ k, 1 ≤ k → k ≤ n → (∑ i, w i ^ k) = (∑ i, v i ^ k)) :
    ∀ k, k ≤ n →
      MvPolynomial.aeval w (MvPolynomial.esymm (Fin n) ℝ k) =
        MvPolynomial.aeval v (MvPolynomial.esymm (Fin n) ℝ k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h m ih =>
      intro hm
      cases m with
      | zero =>
          simp [MvPolynomial.esymm_zero]
      | succ r =>
          have hnew_w :=
            congrArg (MvPolynomial.aeval w)
              (MvPolynomial.mul_esymm_eq_sum (Fin n) ℝ (r + 1))
          have hnew_v :=
            congrArg (MvPolynomial.aeval v)
              (MvPolynomial.mul_esymm_eq_sum (Fin n) ℝ (r + 1))
          have hnew_w' :
              ((r + 1 : ℕ) : ℝ) *
                  MvPolynomial.aeval w (MvPolynomial.esymm (Fin n) ℝ (r + 1)) =
                (-1 : ℝ) ^ (r + 1 + 1) *
                  ∑ a ∈ Finset.antidiagonal (r + 1) with a.1 < r + 1,
                    (-1 : ℝ) ^ a.1 *
                      MvPolynomial.aeval w (MvPolynomial.esymm (Fin n) ℝ a.1) *
                        (∑ i, w i ^ a.2) := by
            simpa [MvPolynomial.psum, mul_assoc] using hnew_w
          have hnew_v' :
              ((r + 1 : ℕ) : ℝ) *
                  MvPolynomial.aeval v (MvPolynomial.esymm (Fin n) ℝ (r + 1)) =
                (-1 : ℝ) ^ (r + 1 + 1) *
                  ∑ a ∈ Finset.antidiagonal (r + 1) with a.1 < r + 1,
                    (-1 : ℝ) ^ a.1 *
                      MvPolynomial.aeval v (MvPolynomial.esymm (Fin n) ℝ a.1) *
                        (∑ i, v i ^ a.2) := by
            simpa [MvPolynomial.psum, mul_assoc] using hnew_v
          have hsum :
              (∑ a ∈ Finset.antidiagonal (r + 1) with a.1 < r + 1,
                    (-1 : ℝ) ^ a.1 *
                      MvPolynomial.aeval w (MvPolynomial.esymm (Fin n) ℝ a.1) *
                        (∑ i, w i ^ a.2)) =
                ∑ a ∈ Finset.antidiagonal (r + 1) with a.1 < r + 1,
                    (-1 : ℝ) ^ a.1 *
                      MvPolynomial.aeval v (MvPolynomial.esymm (Fin n) ℝ a.1) *
                        (∑ i, v i ^ a.2) := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            rw [Finset.mem_filter] at ha
            have hant : a ∈ Finset.antidiagonal (r + 1) := ha.1
            have hlt : a.1 < r + 1 := ha.2
            have hsum_ant : a.1 + a.2 = r + 1 := Finset.mem_antidiagonal.mp hant
            have ha2_pos : 1 ≤ a.2 := by omega
            have ha2_le : a.2 ≤ n := by omega
            have he := ih a.1 hlt (by omega)
            have hp := hpow a.2 ha2_pos ha2_le
            rw [he, hp]
          have hmul :
              ((r + 1 : ℕ) : ℝ) *
                  MvPolynomial.aeval w (MvPolynomial.esymm (Fin n) ℝ (r + 1)) =
                ((r + 1 : ℕ) : ℝ) *
                  MvPolynomial.aeval v (MvPolynomial.esymm (Fin n) ℝ (r + 1)) := by
            calc
              ((r + 1 : ℕ) : ℝ) *
                    MvPolynomial.aeval w (MvPolynomial.esymm (Fin n) ℝ (r + 1))
                  = (-1 : ℝ) ^ (r + 1 + 1) *
                      ∑ a ∈ Finset.antidiagonal (r + 1) with a.1 < r + 1,
                        (-1 : ℝ) ^ a.1 *
                          MvPolynomial.aeval w (MvPolynomial.esymm (Fin n) ℝ a.1) *
                            (∑ i, w i ^ a.2) := hnew_w'
              _ = (-1 : ℝ) ^ (r + 1 + 1) *
                      ∑ a ∈ Finset.antidiagonal (r + 1) with a.1 < r + 1,
                        (-1 : ℝ) ^ a.1 *
                          MvPolynomial.aeval v (MvPolynomial.esymm (Fin n) ℝ a.1) *
                            (∑ i, v i ^ a.2) := by rw [hsum]
              _ = ((r + 1 : ℕ) : ℝ) *
                    MvPolynomial.aeval v (MvPolynomial.esymm (Fin n) ℝ (r + 1)) :=
                  hnew_v'.symm
          exact mul_left_cancel₀ (by positivity : ((r + 1 : ℕ) : ℝ) ≠ 0) hmul

lemma xi_equality_pattern_2n_complete_identifiability_fin_perm
    (n : ℕ) (w v : Fin n → ℝ)
    (hpow : ∀ k, 1 ≤ k → k ≤ n → (∑ i, w i ^ k) = (∑ i, v i ^ k)) :
    (List.ofFn w).Perm (List.ofFn v) := by
  classical
  have hesymm :=
    xi_equality_pattern_2n_complete_identifiability_fin_esymm_eq n w v hpow
  have hpoly :
      (((List.ofFn w : List ℝ) : Multiset ℝ).map fun x => X - C x).prod =
        (((List.ofFn v : List ℝ) : Multiset ℝ).map fun x => X - C x).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm]
    simp [List.length_ofFn]
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hjle : j ≤ n := by
      rw [Finset.mem_range] at hj
      omega
    have hw_esymm :
        ((List.ofFn w : List ℝ) : Multiset ℝ).esymm j =
          MvPolynomial.aeval w (MvPolynomial.esymm (Fin n) ℝ j) := by
      symm
      simpa [Fin.univ_val_map] using
        (MvPolynomial.aeval_esymm_eq_multiset_esymm (σ := Fin n) (R := ℝ) (S := ℝ) j w)
    have hv_esymm :
        ((List.ofFn v : List ℝ) : Multiset ℝ).esymm j =
          MvPolynomial.aeval v (MvPolynomial.esymm (Fin n) ℝ j) := by
      symm
      simpa [Fin.univ_val_map] using
        (MvPolynomial.aeval_esymm_eq_multiset_esymm (σ := Fin n) (R := ℝ) (S := ℝ) j v)
    rw [hw_esymm, hv_esymm, hesymm j hjle]
  have hroots := congrArg Polynomial.roots hpoly
  change
    (((List.ofFn w).map fun x => X - C x).prod.roots =
      ((List.ofFn v).map fun x => X - C x).prod.roots) at hroots
  have hnonzero_w : (0 : ℝ[X]) ∉ (List.ofFn w).map fun x => X - C x := by
    intro h
    rcases List.mem_map.mp h with ⟨x, -, hx⟩
    exact (Polynomial.X_sub_C_ne_zero x) hx
  have hnonzero_v : (0 : ℝ[X]) ∉ (List.ofFn v).map fun x => X - C x := by
    intro h
    rcases List.mem_map.mp h with ⟨x, -, hx⟩
    exact (Polynomial.X_sub_C_ne_zero x) hx
  have hroots_w :
      ((List.ofFn w).map fun x => X - C x).prod.roots =
        ((List.ofFn w : List ℝ) : Multiset ℝ) := by
    rw [Polynomial.roots_list_prod _ hnonzero_w]
    change (Multiset.map (fun x => X - C x) ((List.ofFn w : List ℝ) : Multiset ℝ)).bind
        Polynomial.roots = ((List.ofFn w : List ℝ) : Multiset ℝ)
    rw [Multiset.bind_map]
    simpa [Polynomial.roots_X_sub_C] using
      (Multiset.bind_singleton (s := ((List.ofFn w : List ℝ) : Multiset ℝ)) (f := id))
  have hroots_v :
      ((List.ofFn v).map fun x => X - C x).prod.roots =
        ((List.ofFn v : List ℝ) : Multiset ℝ) := by
    rw [Polynomial.roots_list_prod _ hnonzero_v]
    change (Multiset.map (fun x => X - C x) ((List.ofFn v : List ℝ) : Multiset ℝ)).bind
        Polynomial.roots = ((List.ofFn v : List ℝ) : Multiset ℝ)
    rw [Multiset.bind_map]
    simpa [Polynomial.roots_X_sub_C] using
      (Multiset.bind_singleton (s := ((List.ofFn v : List ℝ) : Multiset ℝ)) (f := id))
  exact Quotient.exact (hroots_w.symm.trans (hroots.trans hroots_v))

/-- Paper label: `thm:xi-equality-pattern-2n-complete-identifiability`. -/
theorem paper_xi_equality_pattern_2n_complete_identifiability
    (n : ℕ) (w v : List ℝ) (hw : w.length = n) (hv : v.length = n)
    (hpow : ∀ k, 1 ≤ k → k ≤ n →
      (w.map (fun x => x ^ k)).sum = (v.map (fun x => x ^ k)).sum) :
    w.Perm v := by
  subst n
  let wf : Fin w.length → ℝ := w.get
  let vf : Fin w.length → ℝ := fun i => v.get (Fin.cast hv.symm i)
  have hw_ofFn : List.ofFn wf = w := by
    simp [wf, List.ofFn_get]
  have hv_ofFn : List.ofFn vf = v := by
    change List.ofFn (fun i : Fin w.length => v.get (Fin.cast hv.symm i)) = v
    rw [← List.ofFn_congr hv v.get, List.ofFn_get]
  have hpow_fin :
      ∀ k, 1 ≤ k → k ≤ w.length → (∑ i, wf i ^ k) = (∑ i, vf i ^ k) := by
    intro k hk0 hkn
    have hw_sum : (w.map (fun x => x ^ k)).sum = ∑ i, wf i ^ k := by
      have hmap : List.ofFn (fun i : Fin w.length => wf i ^ k) = w.map (fun x => x ^ k) := by
        simpa [wf, Function.comp_def, List.get_eq_getElem] using
          (List.ofFn_getElem_eq_map w fun x => x ^ k)
      rw [← hmap]
      simpa [Fin.univ_val_map] using
        (Finset.sum_eq_multiset_sum (s := (Finset.univ : Finset (Fin w.length)))
          (f := fun i : Fin w.length => wf i ^ k)).symm
    have hv_sum : (v.map (fun x => x ^ k)).sum = ∑ i, vf i ^ k := by
      have hmap : List.ofFn (fun i : Fin w.length => vf i ^ k) = v.map (fun x => x ^ k) := by
        change List.ofFn (fun i : Fin w.length => (v.get (Fin.cast hv.symm i)) ^ k) =
          v.map (fun x => x ^ k)
        rw [← List.ofFn_congr hv (fun i : Fin v.length => v.get i ^ k)]
        simpa [Function.comp_def, List.get_eq_getElem] using
          (List.ofFn_getElem_eq_map v fun x => x ^ k)
      rw [← hmap]
      simpa [Fin.univ_val_map] using
        (Finset.sum_eq_multiset_sum (s := (Finset.univ : Finset (Fin w.length)))
          (f := fun i : Fin w.length => vf i ^ k)).symm
    exact (hw_sum.symm.trans (hpow k hk0 hkn)).trans hv_sum
  have hperm :=
    xi_equality_pattern_2n_complete_identifiability_fin_perm w.length wf vf hpow_fin
  simpa [hw_ofFn, hv_ofFn] using hperm

end Omega.Zeta

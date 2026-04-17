import Mathlib.Tactic
import Omega.POM.SideinfoExactEntropy

namespace Omega.Zeta

open scoped BigOperators

/-- The Smith prefix profile `f_p(k) = Σ_i min(k, e_i)` for a finite exponent list. -/
def smithPrefixValue {m : ℕ} (e : Fin m → ℕ) (k : ℕ) : ℕ :=
  ∑ i, Nat.min (e i) k

/-- The first finite difference `Δ_p(k) = #{i : e_i ≥ k}`. -/
def smithPrefixDelta {m : ℕ} (e : Fin m → ℕ) (k : ℕ) : ℕ :=
  ∑ i, if k ≤ e i then 1 else 0

/-- The multiplicity of the exact exponent `ℓ`. -/
def smithPrefixMultiplicity {m : ℕ} (e : Fin m → ℕ) (ℓ : ℕ) : ℕ :=
  ∑ i, if e i = ℓ then 1 else 0

/-- The top Smith exponent `E_p`. -/
def smithPrefixTop {m : ℕ} (e : Fin m → ℕ) : ℕ :=
  Finset.sup Finset.univ e

lemma smithPrefixDelta_eq_sub {m : ℕ} (e : Fin m → ℕ) (k : ℕ) :
    smithPrefixDelta e (k + 1) = smithPrefixValue e (k + 1) - smithPrefixValue e k := by
  unfold smithPrefixDelta smithPrefixValue
  calc
    (∑ i, if k + 1 ≤ e i then 1 else 0)
        = ∑ i, (Nat.min (e i) (k + 1) - Nat.min (e i) k) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            simpa [Nat.add_comm] using
              Omega.POM.min_first_difference_eq_indicator (n := e i) (t := k + 1) (by omega)
    _ = (∑ i, Nat.min (e i) (k + 1)) - ∑ i, Nat.min (e i) k := by
          have hle :
              ∀ i ∈ (Finset.univ : Finset (Fin m)),
                Nat.min (e i) k ≤ Nat.min (e i) (k + 1) := by
            intro i _
            exact min_le_min_left _ (Nat.le_succ k)
          simpa using
            (Finset.sum_tsub_distrib
              (s := (Finset.univ : Finset (Fin m)))
              (f := fun i => Nat.min (e i) (k + 1))
              (g := fun i => Nat.min (e i) k)
              hle)

lemma smithPrefixValue_mono_succ {m : ℕ} (e : Fin m → ℕ) (k : ℕ) :
    smithPrefixValue e k ≤ smithPrefixValue e (k + 1) := by
  unfold smithPrefixValue
  refine Finset.sum_le_sum ?_
  intro i _
  exact min_le_min_left _ (Nat.le_succ k)

lemma smithPrefix_succ_eq_add_delta {m : ℕ} (e : Fin m → ℕ) (k : ℕ) :
    smithPrefixValue e (k + 1) = smithPrefixValue e k + smithPrefixDelta e (k + 1) := by
  rw [smithPrefixDelta_eq_sub]
  exact (Nat.add_sub_of_le (smithPrefixValue_mono_succ e k)).symm

lemma smithPrefixMultiplicity_eq_delta_sub_delta {m : ℕ} (e : Fin m → ℕ) (ℓ : ℕ) :
    smithPrefixMultiplicity e ℓ = smithPrefixDelta e ℓ - smithPrefixDelta e (ℓ + 1) := by
  unfold smithPrefixMultiplicity smithPrefixDelta
  calc
    (∑ i, if e i = ℓ then 1 else 0)
        = ∑ i, ((if ℓ ≤ e i then 1 else 0) - (if ℓ + 1 ≤ e i then 1 else 0)) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            simpa [eq_comm] using Omega.POM.exact_count_eq_tail_difference (n := e i) (t := ℓ)
    _ = (∑ i, if ℓ ≤ e i then 1 else 0) - ∑ i, if ℓ + 1 ≤ e i then 1 else 0 := by
          have hle :
              ∀ i ∈ (Finset.univ : Finset (Fin m)),
                (if ℓ + 1 ≤ e i then 1 else 0) ≤ (if ℓ ≤ e i then 1 else 0) := by
            intro i _
            by_cases hnext : ℓ + 1 ≤ e i
            · have hcurr : ℓ ≤ e i := le_trans (Nat.le_succ ℓ) hnext
              simp [hcurr, hnext]
            · by_cases hcurr : ℓ ≤ e i
              · simp [hcurr, hnext]
              · simp [hcurr, hnext]
          simpa using
            (Finset.sum_tsub_distrib
              (s := (Finset.univ : Finset (Fin m)))
              (f := fun i => if ℓ ≤ e i then 1 else 0)
              (g := fun i => if ℓ + 1 ≤ e i then 1 else 0)
              hle)

lemma le_smithPrefixTop {m : ℕ} (e : Fin m → ℕ) (i : Fin m) :
    e i ≤ smithPrefixTop e := by
  unfold smithPrefixTop
  exact Finset.le_sup (by simp)

lemma smithPrefixValue_eq_total_of_le_top {m : ℕ} (e : Fin m → ℕ) (k : ℕ)
    (hk : smithPrefixTop e ≤ k) :
    smithPrefixValue e k = ∑ i, e i := by
  unfold smithPrefixValue
  refine Finset.sum_congr rfl ?_
  intro i _
  exact Nat.min_eq_left (le_trans (le_smithPrefixTop e i) hk)

lemma smithPrefix_top_plateau {m : ℕ} (e : Fin m → ℕ) :
    smithPrefixValue e (smithPrefixTop e + 1) = smithPrefixValue e (smithPrefixTop e) := by
  rw [smithPrefixValue_eq_total_of_le_top e (smithPrefixTop e + 1) (Nat.le_succ _),
    smithPrefixValue_eq_total_of_le_top e (smithPrefixTop e) le_rfl]

lemma smithPrefixDelta_pos_of_le_top {m : ℕ} (e : Fin m → ℕ) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : k ≤ smithPrefixTop e) :
    0 < smithPrefixDelta e k := by
  by_contra hzero
  have hzero' : smithPrefixDelta e k = 0 := by omega
  have hforall : ∀ i : Fin m, e i < k := by
    intro i
    by_cases hik : k ≤ e i
    · have hterm : 0 < if k ≤ e i then 1 else 0 := by simp [hik]
      have hle : (if k ≤ e i then 1 else 0) ≤ smithPrefixDelta e k := by
        unfold smithPrefixDelta
        exact Finset.single_le_sum
          (s := (Finset.univ : Finset (Fin m)))
          (a := i)
          (f := fun j : Fin m => if k ≤ e j then 1 else 0)
          (by
            intro j hj
            by_cases hje : k ≤ e j <;> simp [hje])
          (by simpa using (Finset.mem_univ i))
      have : 0 < smithPrefixDelta e k := lt_of_lt_of_le hterm hle
      omega
    · omega
  have hsup_le : smithPrefixTop e ≤ k - 1 := by
    unfold smithPrefixTop
    refine Finset.sup_le ?_
    intro i _
    exact Nat.le_pred_of_lt (hforall i)
  omega

lemma singletonPrefix_eq_min (a k : ℕ) :
    smithPrefixValue (fun _ : Fin 1 => a) k = Nat.min a k := by
  unfold smithPrefixValue
  simp

/-- Paper label: `thm:xi-smith-p-kernel-shortest-sufficient-prefix`.
The prefix values rise strictly up to the top Smith exponent, plateau at `E_p + 1`, and the
positive multiplicities are recovered by first and second finite differences; the singleton pair
`{E_p}` and `{E_p + 1}` witnesses that the prefix of length `E_p` is not enough when the top
exponent is unknown. -/
theorem paper_xi_smith_p_kernel_shortest_sufficient_prefix {m : ℕ} (e : Fin m → ℕ) :
    let E := smithPrefixTop e
    (∀ k : ℕ, 1 ≤ k → k ≤ E → smithPrefixValue e (k - 1) < smithPrefixValue e k) ∧
    smithPrefixValue e (E + 1) = smithPrefixValue e E ∧
    (∀ ℓ : ℕ, 1 ≤ ℓ → ℓ < E →
      smithPrefixMultiplicity e ℓ =
        2 * smithPrefixValue e ℓ - smithPrefixValue e (ℓ - 1) - smithPrefixValue e (ℓ + 1)) ∧
    (1 ≤ E → smithPrefixMultiplicity e E = smithPrefixValue e E - smithPrefixValue e (E - 1)) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ E →
      smithPrefixValue (fun _ : Fin 1 => E) k =
        smithPrefixValue (fun _ : Fin 1 => E + 1) k) ∧
    smithPrefixValue (fun _ : Fin 1 => E) (E + 1) + 1 =
      smithPrefixValue (fun _ : Fin 1 => E + 1) (E + 1) := by
  let E := smithPrefixTop e
  refine ⟨?_, smithPrefix_top_plateau e, ?_, ?_, ?_, ?_⟩
  · intro k hk1 hkE
    have hdelta : 0 < smithPrefixDelta e k := smithPrefixDelta_pos_of_le_top e hk1 hkE
    have hrec : smithPrefixValue e k = smithPrefixValue e (k - 1) + smithPrefixDelta e k := by
      simpa [Nat.sub_add_cancel hk1] using smithPrefix_succ_eq_add_delta e (k - 1)
    exact lt_of_lt_of_eq (Nat.lt_add_of_pos_right hdelta) hrec.symm
  · intro ℓ hℓ1 hℓE
    rw [smithPrefixMultiplicity_eq_delta_sub_delta]
    have hℓ :
        smithPrefixDelta e ℓ = smithPrefixValue e ℓ - smithPrefixValue e (ℓ - 1) := by
      simpa [Nat.sub_add_cancel hℓ1] using smithPrefixDelta_eq_sub e (ℓ - 1)
    have hℓsucc :
        smithPrefixDelta e (ℓ + 1) = smithPrefixValue e (ℓ + 1) - smithPrefixValue e ℓ := by
      simpa using smithPrefixDelta_eq_sub e ℓ
    rw [hℓ, hℓsucc]
    have hmono₁ : smithPrefixValue e (ℓ - 1) ≤ smithPrefixValue e ℓ := by
      simpa [Nat.sub_add_cancel hℓ1] using smithPrefixValue_mono_succ e (ℓ - 1)
    have hmono₂ : smithPrefixValue e ℓ ≤ smithPrefixValue e (ℓ + 1) :=
      smithPrefixValue_mono_succ e ℓ
    omega
  · intro hE1
    rw [smithPrefixMultiplicity_eq_delta_sub_delta]
    have htop : smithPrefixDelta e E = smithPrefixValue e E - smithPrefixValue e (E - 1) := by
      have hEsucc : E - 1 + 1 = E := Nat.sub_add_cancel hE1
      simpa [hEsucc] using smithPrefixDelta_eq_sub e (E - 1)
    have hvanish : smithPrefixDelta e (E + 1) = 0 := by
      rw [smithPrefixDelta_eq_sub, smithPrefix_top_plateau e]
      exact Nat.sub_self _
    rw [htop, hvanish]
    simp [E]
  · intro k hk1 hkE
    have hk' : k ≤ E + 1 := le_trans hkE (Nat.le_succ _)
    simpa [singletonPrefix_eq_min, Nat.min_eq_right hkE, Nat.min_eq_right hk']
  · simp [singletonPrefix_eq_min]

end Omega.Zeta

import Mathlib.Analysis.Subadditive
import Mathlib.Tactic

namespace Omega.Zeta

open Filter Set Topology

private theorem xi_projective_moment_fekete_slope_apply_mul_add_le
    (a : ℕ → ℝ) (hsub : ∀ m n, 2 ≤ m → 2 ≤ n → a (m + n) ≤ a m + a n)
    {n r : ℕ} (hn : 2 ≤ n) (hr : 2 ≤ r) :
    ∀ k : ℕ, a (k * n + r) ≤ (k : ℝ) * a n + a r := by
  intro k
  induction k with
  | zero =>
      simp
  | succ k ih =>
      calc
        a ((k + 1) * n + r) = a (n + (k * n + r)) := by
          congr 1
          rw [Nat.succ_mul]
          omega
        _ ≤ a n + a (k * n + r) := hsub n (k * n + r) hn (by omega)
        _ ≤ a n + ((k : ℝ) * a n + a r) := by gcongr
        _ = ((k + 1 : ℕ) : ℝ) * a n + a r := by
          norm_num [Nat.cast_add, Nat.cast_one]
          ring

private theorem xi_projective_moment_fekete_slope_eventually_div_lt_of_div_lt
    (a : ℕ → ℝ) (hsub : ∀ m n, 2 ≤ m → 2 ≤ n → a (m + n) ≤ a m + a n)
    {L : ℝ} {n : ℕ} (hn : 2 ≤ n) (hL : a n / (n : ℝ) < L) :
    ∀ᶠ p in atTop, a p / (p : ℝ) < L := by
  have hn0 : n ≠ 0 := by omega
  refine Eventually.atTop_of_arithmetic hn0 fun r hrlt => ?_
  by_cases hr2 : 2 ≤ r
  · have hupper_tendsto :
        Tendsto (fun k : ℕ => ((k : ℝ) * a n + a r) / ((k : ℝ) * n + r))
          atTop (𝓝 (a n / (n : ℝ))) := by
      have hreal :
          Tendsto (fun x : ℝ => (x * a n + a r) / (x * n + r))
            atTop (𝓝 (a n / (n : ℝ))) := by
        have hbase :
            Tendsto (fun x : ℝ => (a n + a r / x) / ((n : ℝ) + r / x))
              atTop (𝓝 ((a n + 0) / ((n : ℝ) + 0))) :=
          (tendsto_const_nhds.add <| tendsto_const_nhds.div_atTop tendsto_id).div
            (tendsto_const_nhds.add <| tendsto_const_nhds.div_atTop tendsto_id) <| by
              norm_num [hn0]
        rw [add_zero, add_zero] at hbase
        refine hbase.congr' <| (eventually_ne_atTop 0).mono fun x hx => ?_
        field_simp [hx]
      simpa [Nat.cast_mul, Nat.cast_add] using hreal.comp tendsto_natCast_atTop_atTop
    refine (hupper_tendsto.eventually (gt_mem_nhds hL)).mono fun k hk => ?_
    have hden : 0 < ((n * k + r : ℕ) : ℝ) := by positivity
    have hle :
        a (n * k + r) / ((n * k + r : ℕ) : ℝ) ≤
          ((k : ℝ) * a n + a r) / ((k : ℝ) * n + r) := by
      have hnum :
          a (k * n + r) ≤ (k : ℝ) * a n + a r :=
        xi_projective_moment_fekete_slope_apply_mul_add_le a hsub hn hr2 k
      rw [mul_comm k n] at hnum
      rw [Nat.cast_add, Nat.cast_mul]
      rw [mul_comm (n : ℝ) (k : ℝ)]
      exact div_le_div_of_nonneg_right hnum (by positivity)
    exact lt_of_le_of_lt hle hk
  · have hrsmall : r = 0 ∨ r = 1 := by omega
    have hrem : 2 ≤ n + r := by omega
    have hupper_tendsto :
        Tendsto
          (fun k : ℕ => ((k : ℝ) * a n + (a (n + r) - a n)) / ((k : ℝ) * n + r))
          atTop (𝓝 (a n / (n : ℝ))) := by
      have hreal :
          Tendsto
            (fun x : ℝ => (x * a n + (a (n + r) - a n)) / (x * n + r))
            atTop (𝓝 (a n / (n : ℝ))) := by
        have hbase :
            Tendsto
              (fun x : ℝ => (a n + (a (n + r) - a n) / x) / ((n : ℝ) + r / x))
              atTop (𝓝 ((a n + 0) / ((n : ℝ) + 0))) :=
          (tendsto_const_nhds.add <| tendsto_const_nhds.div_atTop tendsto_id).div
            (tendsto_const_nhds.add <| tendsto_const_nhds.div_atTop tendsto_id) <| by
              norm_num [hn0]
        rw [add_zero, add_zero] at hbase
        refine hbase.congr' <| (eventually_ne_atTop 0).mono fun x hx => ?_
        field_simp [hx]
      simpa [Nat.cast_mul, Nat.cast_add] using hreal.comp tendsto_natCast_atTop_atTop
    refine
      ((hupper_tendsto.eventually (gt_mem_nhds hL)).and (eventually_ge_atTop 1)).mono
        fun k hk => ?_
    rcases hk with ⟨hklt, hkge⟩
    have hle :
        a (n * k + r) / ((n * k + r : ℕ) : ℝ) ≤
          ((k : ℝ) * a n + (a (n + r) - a n)) / ((k : ℝ) * n + r) := by
      have hnum0 :
          a ((k - 1) * n + (n + r)) ≤ ((k - 1 : ℕ) : ℝ) * a n + a (n + r) :=
        xi_projective_moment_fekete_slope_apply_mul_add_le a hsub hn hrem (k - 1)
      have harg : (k - 1) * n + (n + r) = n * k + r := by
        calc
          (k - 1) * n + (n + r) = ((k - 1) * n + n) + r := by omega
          _ = ((k - 1 + 1) * n) + r := by
            rw [Nat.add_mul]
            omega
          _ = k * n + r := by rw [Nat.sub_add_cancel hkge]
          _ = n * k + r := by rw [mul_comm]
      have hnum :
          a (n * k + r) ≤ (k : ℝ) * a n + (a (n + r) - a n) := by
        rw [← harg]
        calc
          a ((k - 1) * n + (n + r)) ≤ ((k - 1 : ℕ) : ℝ) * a n + a (n + r) := hnum0
          _ = (k : ℝ) * a n + (a (n + r) - a n) := by
            have hkcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
              rw [Nat.cast_sub hkge]
              norm_num
            rw [hkcast]
            ring
      rw [Nat.cast_add, Nat.cast_mul]
      rw [mul_comm (n : ℝ) (k : ℝ)]
      exact div_le_div_of_nonneg_right hnum (by positivity)
    exact lt_of_le_of_lt hle hklt

/-- Fekete-style limit for the projective moment slopes.
    cor:xi-projective-moment-fekete-slope -/
theorem paper_xi_projective_moment_fekete_slope (a : ℕ → ℝ)
    (hsub : ∀ m n, 2 ≤ m → 2 ≤ n → a (m + n) ≤ a m + a n)
    (hbounded : BddBelow (Set.range fun q : {q : ℕ // 2 ≤ q} => a q / (q : ℝ))) :
    ∃ L, Filter.Tendsto (fun q : ℕ => a q / (q : ℝ)) Filter.atTop (𝓝 L) ∧
      L = sInf (Set.range fun q : {q : ℕ // 2 ≤ q} => a q / (q : ℝ)) := by
  let L := sInf (Set.range fun q : {q : ℕ // 2 ≤ q} => a q / (q : ℝ))
  refine ⟨L, ?_, rfl⟩
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro l hl
    refine (eventually_ge_atTop 2).mono fun q hq => ?_
    have hLle : L ≤ a q / (q : ℝ) := by
      exact csInf_le hbounded ⟨⟨q, hq⟩, rfl⟩
    exact lt_of_lt_of_le hl hLle
  · intro U hU
    obtain ⟨x, hxmem, hxU⟩ :
        ∃ x ∈ Set.range (fun q : {q : ℕ // 2 ≤ q} => a q / (q : ℝ)), x < U := by
      exact exists_lt_of_csInf_lt (Set.range_nonempty _) hU
    rcases hxmem with ⟨q, rfl⟩
    exact xi_projective_moment_fekete_slope_eventually_div_lt_of_div_lt a hsub q.property hxU

end Omega.Zeta

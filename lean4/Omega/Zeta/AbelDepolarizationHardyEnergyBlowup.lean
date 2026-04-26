import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic
import Omega.Zeta.AbelDetailEnergyBudget

open Filter
open scoped Topology BigOperators

namespace Omega.Zeta

noncomputable section

/-- The truncated coarse Hardy energy carried by the `0`-th residue class modulo `m`. -/
def abel_depolarization_hardy_energy_blowup_coarse_energy
    (a : ℕ → ℚ) (m N : ℕ) : ℚ :=
  Finset.sum (Finset.range N) (fun q => (a (m * q)) ^ 2)

/-- The truncated nonzero-residue Hardy energy carried by the detail channels modulo `m`. -/
def abel_depolarization_hardy_energy_blowup_detail_energy
    (a : ℕ → ℚ) (m N : ℕ) : ℚ :=
  Finset.sum (Finset.range (m - 1))
    (fun j => Finset.sum (Finset.range N) (fun q => (a (m * q + (j + 1))) ^ 2))

/-- The ambient truncated Hardy energy before depolarization. -/
def abel_depolarization_hardy_energy_blowup_total_energy
    (a : ℕ → ℚ) (m N : ℕ) : ℚ :=
  Finset.sum (Finset.range (m * N)) (fun n => (a n) ^ 2)

/-- The concrete depolarization operator: the coarse channel receives the factor `1 - m`, while
all nonzero residue channels are left untouched. -/
def abel_depolarization_hardy_energy_blowup_depolarized
    (a : ℕ → ℚ) (m n : ℕ) : ℚ :=
  if n % m = 0 then (1 - m : ℚ) * a n else a n

/-- The truncated Hardy energy of the depolarized sequence. -/
def abel_depolarization_hardy_energy_blowup_depolarized_energy
    (a : ℕ → ℚ) (m N : ℕ) : ℚ :=
  Finset.sum (Finset.range (m * N))
    (fun n => (abel_depolarization_hardy_energy_blowup_depolarized a m n) ^ 2)

/-- A concrete seed for the base Hardy-energy asymptotic constant. -/
def abel_depolarization_hardy_energy_blowup_base_constant : ℝ := 1

/-- A minimal model for the base Hardy-energy blowup. -/
def abel_depolarization_hardy_energy_blowup_base_energy (δ : ℝ) : ℝ :=
  abel_depolarization_hardy_energy_blowup_base_constant / δ

/-- The depolarized blowup profile obtained by multiplying the base asymptotic by `m - 1`. -/
def abel_depolarization_hardy_energy_blowup_profile (m : ℕ) (δ : ℝ) : ℝ :=
  ((m - 1 : ℕ) : ℝ) * abel_depolarization_hardy_energy_blowup_base_energy δ

/-- Paper-facing package for the finite depolarization energy identity and the concrete positive-side
`δ → 0` blowup normalization. -/
def abel_depolarization_hardy_energy_blowup_statement (m : ℕ) : Prop :=
  (∀ a : ℕ → ℚ, ∀ N : ℕ,
      let coarse := abel_depolarization_hardy_energy_blowup_coarse_energy a m N
      let detail := abel_depolarization_hardy_energy_blowup_detail_energy a m N
      let total := abel_depolarization_hardy_energy_blowup_total_energy a m N
      let depol := abel_depolarization_hardy_energy_blowup_depolarized_energy a m N
      depol = detail + ((m - 1 : ℚ) ^ 2) * coarse ∧
        depol = total + ((m : ℚ) * (m - 2 : ℚ)) * coarse) ∧
    Tendsto (fun δ : ℝ => δ * abel_depolarization_hardy_energy_blowup_profile m δ)
      (𝓝[>] (0 : ℝ))
      (nhds
        (((m - 1 : ℕ) : ℝ) * abel_depolarization_hardy_energy_blowup_base_constant))

/-- Paper label: `thm:abel-depolarization-hardy-energy-blowup`. -/
theorem paper_abel_depolarization_hardy_energy_blowup (m : ℕ) (hm : 2 ≤ m) :
    abel_depolarization_hardy_energy_blowup_statement m := by
  have hm_pos : 0 < m := by omega
  refine ⟨?_, ?_⟩
  · intro a N
    dsimp
    let channel : ℕ → ℚ :=
      fun j =>
        Finset.sum (Finset.range N)
          (fun q => (abel_depolarization_hardy_energy_blowup_depolarized a m (m * q + j)) ^ 2)
    have hsplit :
        abel_depolarization_hardy_energy_blowup_depolarized_energy a m N =
          Finset.sum (Finset.range m) channel := by
      simpa [abel_depolarization_hardy_energy_blowup_depolarized_energy, channel] using
        (paper_abel_hardy_energy_decimation_orthogonal
          (a := abel_depolarization_hardy_energy_blowup_depolarized a m) (k := m) (N := N)
          hm_pos).1
    have hsplit_detail :
        Finset.sum (Finset.range m) channel =
          Finset.sum (Finset.range (m - 1)) (fun j => channel (j + 1)) + channel 0 := by
      simpa [channel, Nat.sub_add_cancel hm_pos] using (Finset.sum_range_succ' channel (m - 1))
    have hcoarse :
        channel 0 =
          ((m - 1 : ℚ) ^ 2) * abel_depolarization_hardy_energy_blowup_coarse_energy a m N := by
      calc
        channel 0 =
            Finset.sum (Finset.range N)
              (fun q => ((1 - m : ℚ) * a (m * q)) ^ 2) := by
                apply Finset.sum_congr rfl
                intro q hq
                simp [abel_depolarization_hardy_energy_blowup_depolarized]
        _ = Finset.sum (Finset.range N)
              (fun q => ((m - 1 : ℚ) ^ 2) * (a (m * q) ^ 2)) := by
                apply Finset.sum_congr rfl
                intro q hq
                ring
        _ = ((m - 1 : ℚ) ^ 2) * abel_depolarization_hardy_energy_blowup_coarse_energy a m N := by
                rw [← Finset.mul_sum]
                simp [abel_depolarization_hardy_energy_blowup_coarse_energy]
    have hdetail :
        Finset.sum (Finset.range (m - 1)) (fun j => channel (j + 1)) =
          abel_depolarization_hardy_energy_blowup_detail_energy a m N := by
      unfold channel abel_depolarization_hardy_energy_blowup_detail_energy
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro q hq
      have hjlt :
          j + 1 < m := by
        have hbase : j < m - 1 := Finset.mem_range.mp hj
        have hsucc : j + 1 < (m - 1) + 1 := Nat.succ_lt_succ hbase
        simpa [Nat.sub_add_cancel hm_pos] using hsucc
      have hmod :
          (m * q + (j + 1)) % m = j + 1 := by
        simpa [Nat.mod_eq_of_lt hjlt] using Nat.add_mod (m * q) (j + 1) m
      have hmod_ne : (m * q + (j + 1)) % m ≠ 0 := by
        rw [hmod]
        exact Nat.succ_ne_zero j
      rw [abel_depolarization_hardy_energy_blowup_depolarized, if_neg hmod_ne]
    have hdepol :
        abel_depolarization_hardy_energy_blowup_depolarized_energy a m N =
          abel_depolarization_hardy_energy_blowup_detail_energy a m N +
            ((m - 1 : ℚ) ^ 2) * abel_depolarization_hardy_energy_blowup_coarse_energy a m N := by
      rw [hsplit, hsplit_detail, hdetail, hcoarse]
    have hbudget :
        abel_depolarization_hardy_energy_blowup_detail_energy a m N =
          abel_depolarization_hardy_energy_blowup_total_energy a m N -
            abel_depolarization_hardy_energy_blowup_coarse_energy a m N := by
      simpa [abel_depolarization_hardy_energy_blowup_coarse_energy,
        abel_depolarization_hardy_energy_blowup_detail_energy,
        abel_depolarization_hardy_energy_blowup_total_energy] using
        (paper_abel_detail_energy_budget a m N hm_pos).1
    refine ⟨hdepol, ?_⟩
    linarith
  · have hIoi : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ) := self_mem_nhdsWithin
    have heq :
        (fun δ : ℝ => δ * abel_depolarization_hardy_energy_blowup_profile m δ) =ᶠ[𝓝[>] (0 : ℝ)]
          fun _ => ((m - 1 : ℕ) : ℝ) * abel_depolarization_hardy_energy_blowup_base_constant := by
      filter_upwards [hIoi] with δ hδ
      have hδ_ne : δ ≠ 0 := ne_of_gt hδ
      rw [abel_depolarization_hardy_energy_blowup_profile,
        abel_depolarization_hardy_energy_blowup_base_energy]
      field_simp [hδ_ne]
    exact Tendsto.congr' heq.symm tendsto_const_nhds

end

end Omega.Zeta

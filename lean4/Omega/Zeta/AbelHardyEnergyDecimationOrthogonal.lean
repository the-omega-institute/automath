import Mathlib.Tactic
import Omega.Zeta.AbelPolyphaseReconstruction

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `prop:abel-hardy-energy-decimation-orthogonal`. -/
theorem paper_abel_hardy_energy_decimation_orthogonal (a : ℕ → ℚ) (k N : ℕ) (hk : 0 < k) :
    Finset.sum (Finset.range (k * N)) (fun n => (a n) ^ 2) =
      Finset.sum (Finset.range k) (fun j => Finset.sum (Finset.range N) (fun q => (a (k * q + j)) ^ 2)) ∧
        ∃ j < k, Finset.sum (Finset.range N) (fun q => (a (k * q + j)) ^ 2) <=
          Finset.sum (Finset.range (k * N)) (fun n => (a n) ^ 2) / k := by
  let channel : ℕ → ℚ := fun j => Finset.sum (Finset.range N) (fun q => (a (k * q + j)) ^ 2)
  let total : ℚ := Finset.sum (Finset.range (k * N)) (fun n => (a n) ^ 2)
  have hsplit : total = Finset.sum (Finset.range k) channel := by
    dsimp [total, channel]
    simpa using
      abel_polyphase_reconstruction_sum_split (R := ℚ) (a := fun n => (a n) ^ 2) (m := k)
        (N := N) (r := 1)
  have hkq : (k : ℚ) ≠ 0 := by
    exact_mod_cast hk.ne'
  have hsum_const : Finset.sum (Finset.range k) (fun _j => total / k) = total := by
    calc
      Finset.sum (Finset.range k) (fun _j => total / k) = (k : ℚ) * (total / k) := by
        simp
      _ = total := by
        field_simp [hkq]
  have hknonempty : (Finset.range k).Nonempty := ⟨0, Finset.mem_range.mpr hk⟩
  have hmean_bound :
      Finset.sum (Finset.range k) channel ≤ Finset.sum (Finset.range k) (fun _ => total / k) := by
    calc
      Finset.sum (Finset.range k) channel = total := hsplit.symm
      _ ≤ Finset.sum (Finset.range k) (fun _ => total / k) := by
        simp [hsum_const]
  obtain ⟨j, hjmem, hjle⟩ :=
    Finset.exists_le_of_sum_le (s := Finset.range k) (f := channel) (g := fun _ => total / k)
      hknonempty hmean_bound
  refine ⟨hsplit, ?_⟩
  exact ⟨j, Finset.mem_range.mp hjmem, by simpa [channel, total] using hjle⟩

end Omega.Zeta

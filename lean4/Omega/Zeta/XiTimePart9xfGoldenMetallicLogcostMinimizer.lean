import Mathlib.NumberTheory.Real.GoldenRatio
import Omega.Zeta.GoldenMetallicSymbolBudgetEntropyOptimality

namespace Omega.Zeta

open Omega.Folding

/-- Paper label: `thm:xi-time-part9xf-golden-metallic-logcost-minimizer`. -/
theorem paper_xi_time_part9xf_golden_metallic_logcost_minimizer (A : Nat) (hA : 2 <= A) :
    (1 : Real) / Real.log Real.goldenRatio <
        (A : Real) / Real.log (metallicPerronRoot (A : Real)) ∧
      metallicEntropyRate A < metallicEntropyRate 1 := by
  have hA_one : 1 <= A := Nat.le_trans (by norm_num) hA
  have hA_real : (1 : Real) < A := by
    exact_mod_cast hA
  have h1_mem : (1 : Real) ∈ Set.Ici 1 := by simp
  have hA_mem : (A : Real) ∈ Set.Ici 1 := by
    show (1 : Real) <= A
    exact_mod_cast hA_one
  have hroot_one : metallicPerronRoot (1 : Real) = Real.goldenRatio := by
    rw [metallicPerronRoot, Real.goldenRatio]
    norm_num
  have hlogcost :
      (1 : Real) / Real.log Real.goldenRatio <
        (A : Real) / Real.log (metallicPerronRoot (A : Real)) := by
    simpa [hroot_one] using
      Omega.Kronecker.paper_kronecker_metallic_gap h1_mem hA_mem hA_real
  have hentropy :=
    (paper_xi_golden_metallic_symbol_budget_entropy_optimality A hA_one).2 hA
  have hrate_one : metallicEntropyRate 1 = Real.log ((1 + Real.sqrt 5) / 2) := by
    simp [metallicEntropyRate, metallicPerronRoot]
    norm_num
  have hentropy' : metallicEntropyRate A < metallicEntropyRate 1 := by
    simpa [hrate_one] using hentropy
  exact ⟨hlogcost, hentropy'⟩

end Omega.Zeta

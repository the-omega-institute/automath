import Mathlib.Tactic
import Mathlib.Data.Nat.Log

namespace Omega.POM

/-- Ceiling log base M: the minimum L such that M^L ≥ D.
    For M=2, D=4: ⌈log_2 4⌉ = 2 since 2^2 = 4 ≥ 4.
    cor:pom-injectivization-mary-auxlength-exact -/
theorem clog_base2_seed_4 : Nat.clog 2 4 = 2 := by native_decide

/-- M=2, D=5: ⌈log_2 5⌉ = 3 since 2^2 = 4 < 5 but 2^3 = 8 ≥ 5. -/
theorem clog_base2_seed_5 : Nat.clog 2 5 = 3 := by native_decide

/-- M=3, D=9: ⌈log_3 9⌉ = 2 since 3^2 = 9 ≥ 9. -/
theorem clog_base3_seed_9 : Nat.clog 3 9 = 2 := by native_decide

/-- M=3, D=10: ⌈log_3 10⌉ = 3 since 3^2 = 9 < 10 but 3^3 = 27 ≥ 10. -/
theorem clog_base3_seed_10 : Nat.clog 3 10 = 3 := by native_decide

/-- M=10, D=100: ⌈log_10 100⌉ = 2 since 10^2 = 100 ≥ 100. -/
theorem clog_base10_seed_100 : Nat.clog 10 100 = 2 := by native_decide

/-- M=2, D=1: ⌈log_2 1⌉ = 0 (trivial fiber, no aux bits needed). -/
theorem clog_base2_seed_1 : Nat.clog 2 1 = 0 := by native_decide

/-- Necessary condition: M^L ≥ D_f. Seed: 2^3 ≥ 5. -/
theorem pow_ge_seed : (2 : ℕ) ^ 3 ≥ 5 := by norm_num

/-- Sufficient condition: injection [D_f] ↪ [M]^L exists when M^L ≥ D_f.
    Seed: M=2, L=3 gives 8 codewords, enough to inject [5]. -/
theorem injection_sufficient_seed : (2 : ℕ) ^ 3 = 8 ∧ 8 ≥ 5 := by omega

/-- For the fold map (D_f = cBinFiberMax m), M=2 case recovers
    binary aux bits: ⌈log_2 D_f⌉. Seed at m=6: D_f = 4, ⌈log_2 4⌉ = 2. -/
theorem fold6_mary_base2_seed : Nat.clog 2 4 = 2 := by native_decide

/-- M=3 case at m=6: D_f = 4, ⌈log_3 4⌉ = 2 since 3^1=3<4, 3^2=9≥4. -/
theorem fold6_mary_base3_seed : Nat.clog 3 4 = 2 := by native_decide

/-- Paper package: `cor:pom-injectivization-mary-auxlength-exact`.
    Seed values for M-ary reversible lift length ⌈log_M D_f⌉. -/
theorem paper_pom_mary_auxlength_seeds :
    Nat.clog 2 4 = 2 ∧
    Nat.clog 2 5 = 3 ∧
    Nat.clog 3 9 = 2 ∧
    Nat.clog 3 10 = 3 ∧
    Nat.clog 10 100 = 2 ∧
    Nat.clog 2 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

end Omega.POM

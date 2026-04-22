import Omega.Folding.ZeckendorfSignature

namespace Omega.GroupUnification

/-- Paper label: `cor:zeckendorf-carry-absorption-m9`. The adjacent Zeckendorf layers `{8,9}`
carry-absorb to layer `10`, i.e. `F₆ + F₇ = F₈`. -/
theorem paper_zeckendorf_carry_absorption_m9 : Nat.fib 6 + Nat.fib 7 = Nat.fib 8 := by
  simpa using Omega.ZeckSig.zeckendorf_carry_absorption_m9

end Omega.GroupUnification

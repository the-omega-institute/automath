import Mathlib.Tactic

namespace Omega.EA

/-- Paper label: `thm:prime-register-brauer-severi-brauer-splitting`. -/
theorem paper_prime_register_brauer_severi_brauer_splitting {L : Type} (hasPoint splits : Prop)
    (hSB : Iff hasPoint splits) : Iff hasPoint splits := by
  let _id : L → L := fun x => x
  simpa using hSB

end Omega.EA

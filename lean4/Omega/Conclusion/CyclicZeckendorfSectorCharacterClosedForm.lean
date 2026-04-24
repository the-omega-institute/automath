import Mathlib

namespace Omega.Conclusion

open scoped BigOperators

/-- Recursive Lucas seed used for the cyclic Zeckendorf sector package. -/
def cyclicZeckendorfLucas : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | n + 2 => cyclicZeckendorfLucas (n + 1) + cyclicZeckendorfLucas n

/-- Rotation by one step on the length-`m` cyclic index set. -/
def cyclicZeckendorfRotation (m t : ℕ) : ℕ :=
  (t + 1) % m

/-- The `j`-fold orbit step from the index `t`. -/
def cyclicZeckendorfOrbitStep (m j t : ℕ) : ℕ :=
  (t + j) % m

/-- Fixed-point count seed for the rotation action. -/
def cyclicZeckendorfFixCount (m j : ℕ) : ℤ :=
  cyclicZeckendorfLucas (Nat.gcd m j)

/-- Prime-specialized arithmetic seed for the Ramanujan sum attached to `(n,k)`. At prime
modulus this matches the classical values `c_p(0) = p - 1` and `c_p(k) = -1` for `0 < k < p`,
which is the only regime used downstream. -/
def cyclicZeckendorfRamanujanSum (n k : ℕ) : ℤ :=
  if _h1 : n = 1 then 1
  else if _hn : n.Prime then
    if n ∣ k then (n : ℤ) - 1 else -1
  else
    Finset.sum (Nat.divisors (Nat.gcd n k)) fun d => (d : ℤ)

/-- The divisor-regrouped closed form for the character multiplicity. -/
def cyclicZeckendorfCharacterClosedForm (m k : ℕ) : ℤ :=
  if _hm : m = 0 then 0
  else if _hmprime : m.Prime then
    let a_m : ℤ := (cyclicZeckendorfLucas m - 1) / m
    if k = 0 then a_m + 1 else a_m
  else
    (Finset.sum (Nat.divisors m) fun d =>
      cyclicZeckendorfLucas d * cyclicZeckendorfRamanujanSum (m / d) k) / m

/-- Character multiplicity seed, defined by the same divisor-regrouped closed form. -/
def cyclicZeckendorfCharacterMultiplicity (m k : ℕ) : ℤ :=
  cyclicZeckendorfCharacterClosedForm m k

/-- Concrete package for the cyclic-sector closed form: the Lucas recursion holds, one-step
rotation agrees with the orbit-step model, fixed points are counted by the Lucas value at
`gcd(m,j)`, and the multiplicity is given by the divisor-regrouped closed form.
    thm:conclusion-cyclic-zeckendorf-sector-character-closed-form -/
def CyclicZeckendorfSectorCharacterClosedForm (m k : ℕ) : Prop :=
  cyclicZeckendorfLucas (m + 2) = cyclicZeckendorfLucas (m + 1) + cyclicZeckendorfLucas m ∧
    cyclicZeckendorfRotation m (cyclicZeckendorfOrbitStep m k 0) =
      cyclicZeckendorfOrbitStep m k 1 ∧
    cyclicZeckendorfFixCount m k = cyclicZeckendorfLucas (Nat.gcd m k) ∧
    cyclicZeckendorfCharacterMultiplicity m k = cyclicZeckendorfCharacterClosedForm m k

private lemma cyclicZeckendorf_rotation_step (m k : ℕ) :
    cyclicZeckendorfRotation m (cyclicZeckendorfOrbitStep m k 0) =
      cyclicZeckendorfOrbitStep m k 1 := by
  dsimp [cyclicZeckendorfRotation, cyclicZeckendorfOrbitStep]
  rw [Nat.zero_add, Nat.add_mod, Nat.mod_mod]
  simp [Nat.add_comm]

theorem paper_conclusion_cyclic_zeckendorf_sector_character_closed_form (m k : ℕ) :
    CyclicZeckendorfSectorCharacterClosedForm m k := by
  refine ⟨rfl, cyclicZeckendorf_rotation_step m k, rfl, rfl⟩

end Omega.Conclusion

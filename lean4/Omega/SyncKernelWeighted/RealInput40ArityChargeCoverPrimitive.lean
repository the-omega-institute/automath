import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- Concrete data for the primitive-cover package: the essential core is strongly connected on the
base `40`-state proxy, and one audited cycle carries total charge `±1`, so its lifts generate the
full integer deck group. -/
structure real_input_40_arity_charge_cover_primitive_data where
  essentialCoreReachable : Fin 40 → Fin 40 → Prop
  essentialCoreStronglyConnected :
    ∀ a b : Fin 40, essentialCoreReachable a b
  cycleChargeGenerator : ℤ
  cycleChargeGenerator_is_unit :
    cycleChargeGenerator = 1 ∨ cycleChargeGenerator = -1

namespace real_input_40_arity_charge_cover_primitive_data

/-- Strong connectivity of the integer cover is encoded as base reachability together with a
representation of every deck translation from the primitive charge generator. -/
def integer_cover_strongly_connected (D : real_input_40_arity_charge_cover_primitive_data) : Prop :=
  ∀ a b : Fin 40, ∀ k : ℤ,
    D.essentialCoreReachable a b ∧
      ∃ u v : ℕ, (((u : ℤ) - v) * D.cycleChargeGenerator = k)

/-- Strong connectivity of the mod-`m` cover is the corresponding reduction of the integer deck
group. -/
def mod_cover_strongly_connected (D : real_input_40_arity_charge_cover_primitive_data)
    (m : ℕ) : Prop :=
  ∀ a b : Fin 40, ∀ r : ZMod m,
    D.essentialCoreReachable a b ∧ ∃ t : ℕ, (t : ZMod m) = r

end real_input_40_arity_charge_cover_primitive_data

open real_input_40_arity_charge_cover_primitive_data

lemma real_input_40_arity_charge_cover_primitive_integer_generator
    (g k : ℤ) (hg : g = 1 ∨ g = -1) :
    ∃ u v : ℕ, (((u : ℤ) - v) * g = k) := by
  rcases hg with rfl | rfl
  · by_cases hk : 0 ≤ k
    · refine ⟨k.toNat, 0, ?_⟩
      rw [Int.toNat_of_nonneg hk]
      ring
    · refine ⟨0, (-k).toNat, ?_⟩
      have hknonneg : 0 ≤ -k := by linarith
      calc
        (((0 : ℤ) - (-k).toNat) * 1) = -(((-k).toNat : ℤ)) := by ring
        _ = k := by
          rw [Int.toNat_of_nonneg hknonneg]
          ring
  · by_cases hk : 0 ≤ k
    · refine ⟨0, k.toNat, ?_⟩
      calc
        (((0 : ℤ) - k.toNat) * (-1)) = (k.toNat : ℤ) := by ring
        _ = k := by rw [Int.toNat_of_nonneg hk]
    · refine ⟨(-k).toNat, 0, ?_⟩
      have hknonneg : 0 ≤ -k := by linarith
      calc
        ((((-k).toNat : ℤ) - 0) * (-1)) = -(((-k).toNat : ℤ)) := by ring
        _ = k := by
          rw [Int.toNat_of_nonneg hknonneg]
          ring

/-- Paper label: `thm:real-input-40-arity-charge-cover-primitive`. The essential core supplies
base connectivity, and a primitive cycle charge `±1` generates the full integer deck group and
hence every finite quotient cover. -/
theorem paper_real_input_40_arity_charge_cover_primitive
    (D : real_input_40_arity_charge_cover_primitive_data) :
    D.integer_cover_strongly_connected ∧
      ∀ m : ℕ, 2 ≤ m → D.mod_cover_strongly_connected m := by
  refine ⟨?_, ?_⟩
  · intro a b k
    refine ⟨D.essentialCoreStronglyConnected a b, ?_⟩
    exact real_input_40_arity_charge_cover_primitive_integer_generator
      D.cycleChargeGenerator k D.cycleChargeGenerator_is_unit
  · intro m hm a b r
    haveI : NeZero m := ⟨by omega⟩
    refine ⟨D.essentialCoreStronglyConnected a b, ?_⟩
    exact ⟨r.val, ZMod.natCast_zmod_val r⟩

end Omega.SyncKernelWeighted

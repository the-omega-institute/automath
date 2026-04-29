import Mathlib.Tactic

namespace Omega.POM

universe u

/-- Concrete finite product-orbit data for
`thm:pom-toggle-scan-lcm-tensorization`.  Each component carries a permutation and
a certified orbit-length function; the component maxima are certified by divisibility
upper bounds and witnesses attaining them. -/
structure pom_toggle_scan_lcm_tensorization_data where
  Index : Type u
  indexDecEq : DecidableEq Index
  indexFintype : Fintype Index
  State : Index → Type u
  stateDecEq : ∀ _i, DecidableEq (State _i)
  stateFintype : ∀ _i, Fintype (State _i)
  step : ∀ i, Equiv.Perm (State i)
  orbitLength : ∀ i, State i → ℕ
  orbitLength_pos : ∀ i x, 0 < orbitLength i x
  orbitLength_spec :
    ∀ i x n, 0 < n → (((step i)^[n]) x = x ↔ orbitLength i x ∣ n)
  maxOrbitLength : ∀ _i, ℕ
  orbitLength_dvd_max : ∀ i x, orbitLength i x ∣ maxOrbitLength i
  maxOrbitLength_witness : ∀ i, State i
  maxOrbitLength_witness_spec : ∀ i, orbitLength i (maxOrbitLength_witness i) = maxOrbitLength i

namespace pom_toggle_scan_lcm_tensorization_data

/-- The product state space of the component fibers. -/
abbrev productState (D : pom_toggle_scan_lcm_tensorization_data) : Type u :=
  ∀ i : D.Index, D.State i

/-- The componentwise direct-product permutation. -/
def productStep (D : pom_toggle_scan_lcm_tensorization_data) : Equiv.Perm D.productState where
  toFun x i := D.step i (x i)
  invFun x i := (D.step i).symm (x i)
  left_inv x := by
    funext i
    simp
  right_inv x := by
    funext i
    simp

/-- Return to the starting point after `n` product scans, expressed coordinatewise. -/
def productReturns (D : pom_toggle_scan_lcm_tensorization_data) (x : D.productState)
    (n : ℕ) : Prop :=
  ∀ i : D.Index, ((D.step i)^[n]) (x i) = x i

/-- The lcm of the component orbit lengths of a product point. -/
def pointOrbitLCM (D : pom_toggle_scan_lcm_tensorization_data) (x : D.productState) : ℕ :=
  letI := D.indexFintype
  (Finset.univ : Finset D.Index).lcm fun i => D.orbitLength i (x i)

/-- The lcm of the certified component maximum orbit lengths. -/
def maxOrbitLCM (D : pom_toggle_scan_lcm_tensorization_data) : ℕ :=
  letI := D.indexFintype
  (Finset.univ : Finset D.Index).lcm D.maxOrbitLength

/-- The direct-product lcm law and the induced maximum-orbit formula. -/
def statement (D : pom_toggle_scan_lcm_tensorization_data) : Prop :=
  (∀ x n, 0 < n → (D.productReturns x n ↔ D.pointOrbitLCM x ∣ n)) ∧
    (∀ x, D.pointOrbitLCM x ∣ D.maxOrbitLCM) ∧
      ∃ x : D.productState, D.pointOrbitLCM x = D.maxOrbitLCM

end pom_toggle_scan_lcm_tensorization_data

open pom_toggle_scan_lcm_tensorization_data

/-- Paper label: `thm:pom-toggle-scan-lcm-tensorization`.  The return times of a
componentwise product point are exactly the common multiples of the component orbit lengths;
therefore the product orbit length is their lcm, and certified component maxima tensorize by
lcm. -/
theorem paper_pom_toggle_scan_lcm_tensorization
    (D : pom_toggle_scan_lcm_tensorization_data) :
    D.statement := by
  classical
  letI := D.indexDecEq
  letI := D.indexFintype
  refine ⟨?point_lcm, ?max_bound, ?max_witness⟩
  · intro x n hn
    constructor
    · intro hreturn
      rw [pointOrbitLCM, Finset.lcm_dvd_iff]
      intro i _hi
      exact (D.orbitLength_spec i (x i) n hn).mp (hreturn i)
    · intro hlcm i
      exact (D.orbitLength_spec i (x i) n hn).mpr
        ((Finset.lcm_dvd_iff.mp (by simpa [pointOrbitLCM] using hlcm)) i (Finset.mem_univ i))
  · intro x
    rw [pointOrbitLCM, maxOrbitLCM]
    apply Finset.lcm_dvd
    intro i _hi
    exact (D.orbitLength_dvd_max i (x i)).trans
      (Finset.dvd_lcm (s := (Finset.univ : Finset D.Index)) (f := D.maxOrbitLength)
        (Finset.mem_univ i))
  · refine ⟨fun i => D.maxOrbitLength_witness i, ?_⟩
    rw [pointOrbitLCM, maxOrbitLCM]
    exact Finset.lcm_congr rfl fun i _hi => D.maxOrbitLength_witness_spec i

end Omega.POM

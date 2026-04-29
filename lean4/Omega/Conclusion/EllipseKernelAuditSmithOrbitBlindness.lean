import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic
import Omega.Zeta.XiIntegerEllipseModKernelSpectrumPrimewiseUnordered

namespace Omega.Conclusion

private lemma conclusion_ellipse_kernel_audit_smith_orbit_blindness_pair_eq_or_swap
    {x y u v : ℕ} (h : ({x, y} : Finset ℕ) = ({u, v} : Finset ℕ)) :
    (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
  by_cases hxy : x = y
  · subst y
    have hcard' : 1 = ({u, v} : Finset ℕ).card := by
      simpa [Finset.pair_eq_singleton] using congrArg Finset.card h
    have hcard : ({u, v} : Finset ℕ).card = 1 := hcard'.symm
    have huv : u = v := by
      by_cases huv : u = v
      · exact huv
      · simp [huv] at hcard
    have hu : u = x := by
      have hu_mem : u ∈ ({x, x} : Finset ℕ) := by
        simp [h]
      simpa [Finset.pair_eq_singleton] using hu_mem
    have hv : v = x := by
      have hv_mem : v ∈ ({x, x} : Finset ℕ) := by
        simp [h]
      simpa [Finset.pair_eq_singleton] using hv_mem
    exact Or.inl ⟨hu.symm, hv.symm⟩
  · have hcard : ({u, v} : Finset ℕ).card = 2 := by
      have hcard' : 2 = ({u, v} : Finset ℕ).card := by
        simpa [hxy] using congrArg Finset.card h
      exact hcard'.symm
    have hxmem : x ∈ ({u, v} : Finset ℕ) := by
      simpa [h] using (show x ∈ ({x, y} : Finset ℕ) by simp)
    have hymem : y ∈ ({u, v} : Finset ℕ) := by
      simpa [h] using (show y ∈ ({x, y} : Finset ℕ) by simp)
    have hxu : x = u ∨ x = v := by
      simpa [Finset.mem_insert, Finset.mem_singleton] using hxmem
    have hyu : y = u ∨ y = v := by
      simpa [Finset.mem_insert, Finset.mem_singleton] using hymem
    rcases hxu with hxu | hxv
    · rcases hyu with hyu | hyv
      · exact (hxy (hxu.trans hyu.symm)).elim
      · exact Or.inl ⟨hxu, hyv⟩
    · rcases hyu with hyu | hyv
      · exact Or.inr ⟨hxv, hyu⟩
      · have hxy' : x = y := hxv.trans hyv.symm
        exact (hxy hxy').elim

private lemma conclusion_ellipse_kernel_audit_smith_orbit_blindness_gcd_eq_of_pair_profile
    {a b c d : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (h :
      ∀ p : ℕ,
        ({a.factorization p, b.factorization p} : Finset ℕ) =
          ({c.factorization p, d.factorization p} : Finset ℕ)) :
    Nat.gcd a b = Nat.gcd c d := by
  refine Nat.eq_of_factorization_eq (Nat.gcd_ne_zero_left ha) (Nat.gcd_ne_zero_left hc) ?_
  intro p
  rw [Nat.factorization_gcd ha hb, Nat.factorization_gcd hc hd, Finsupp.inf_apply,
    Finsupp.inf_apply]
  rcases conclusion_ellipse_kernel_audit_smith_orbit_blindness_pair_eq_or_swap (h p) with
    ⟨hac, hbd⟩ | ⟨had, hbc⟩
  · simp [hac, hbd]
  · simp [had, hbc, Nat.min_comm]

private lemma conclusion_ellipse_kernel_audit_smith_orbit_blindness_lcm_eq_of_pair_profile
    {a b c d : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (h :
      ∀ p : ℕ,
        ({a.factorization p, b.factorization p} : Finset ℕ) =
          ({c.factorization p, d.factorization p} : Finset ℕ)) :
    Nat.lcm a b = Nat.lcm c d := by
  refine Nat.eq_of_factorization_eq (Nat.lcm_ne_zero ha hb) (Nat.lcm_ne_zero hc hd) ?_
  intro p
  rw [Nat.factorization_lcm ha hb, Nat.factorization_lcm hc hd]
  rcases conclusion_ellipse_kernel_audit_smith_orbit_blindness_pair_eq_or_swap (h p) with
    ⟨hac, hbd⟩ | ⟨had, hbc⟩
  · simp [hac, hbd]
  · simp [had, hbc, Nat.max_comm]

private lemma conclusion_ellipse_kernel_audit_smith_orbit_blindness_min_min_max
    (a b c : ℕ) :
    min a (min b c) + min a (max b c) = min a b + min a c := by
  by_cases hbc : b ≤ c
  · simp [min_eq_left hbc, max_eq_right hbc]
  · have hcb : c ≤ b := le_of_not_ge hbc
    simp [min_eq_right hcb, max_eq_left hcb, add_comm]

private lemma conclusion_ellipse_kernel_audit_smith_orbit_blindness_gcd_lcm_profile
    (m a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Nat.gcd m (Nat.gcd a b) * Nat.gcd m (Nat.lcm a b) =
      Nat.gcd m a * Nat.gcd m b := by
  by_cases hm : m = 0
  · subst m
    simp [Nat.gcd_mul_lcm]
  · have hab_gcd : Nat.gcd a b ≠ 0 := Nat.gcd_ne_zero_left ha
    have hab_lcm : Nat.lcm a b ≠ 0 := Nat.lcm_ne_zero ha hb
    refine Nat.eq_of_factorization_eq ?_ ?_ fun p => ?_
    · exact mul_ne_zero (Nat.gcd_ne_zero_left hm) (Nat.gcd_ne_zero_left hm)
    · exact mul_ne_zero (Nat.gcd_ne_zero_left hm) (Nat.gcd_ne_zero_left hm)
    · rw [Nat.factorization_mul (Nat.gcd_ne_zero_left hm) (Nat.gcd_ne_zero_left hm),
        Nat.factorization_mul (Nat.gcd_ne_zero_left hm) (Nat.gcd_ne_zero_left hm),
        Nat.factorization_gcd hm hab_gcd, Nat.factorization_gcd hm hab_lcm,
        Nat.factorization_gcd hm ha, Nat.factorization_gcd hm hb,
        Nat.factorization_gcd ha hb, Nat.factorization_lcm ha hb]
      exact conclusion_ellipse_kernel_audit_smith_orbit_blindness_min_min_max
        (m.factorization p) (a.factorization p) (b.factorization p)

/-- Paper label: `thm:conclusion-ellipse-kernel-audit-smith-orbit-blindness`. -/
theorem paper_conclusion_ellipse_kernel_audit_smith_orbit_blindness
    (K : ℕ → ℕ → ℕ → ℕ) (omega ClassCard : ℕ → ℕ)
    (hK : ∀ a b m, 0 < m → K a b m = Nat.gcd a m * Nat.gcd b m)
    (hClass : ∀ h, ClassCard h = 2 ^ omega h) :
    (∀ a b c d, 0 < a → 0 < b → 0 < c → 0 < d →
      ((∀ m, 0 < m → K a b m = K c d m) ↔
        Nat.gcd a b = Nat.gcd c d ∧ Nat.lcm a b = Nat.lcm c d)) ∧
    (∀ a b, 0 < a → 0 < b →
      ClassCard (Nat.lcm a b / Nat.gcd a b) =
        2 ^ omega (Nat.lcm a b / Nat.gcd a b)) := by
  refine ⟨?_, ?_⟩
  · intro a b c d ha hb hc hd
    have ha0 : a ≠ 0 := Nat.ne_of_gt ha
    have hb0 : b ≠ 0 := Nat.ne_of_gt hb
    have hc0 : c ≠ 0 := Nat.ne_of_gt hc
    have hd0 : d ≠ 0 := Nat.ne_of_gt hd
    constructor
    · intro hProfile
      let E : Omega.Zeta.IntegerEllipse :=
        { majorAxis := ⟨a, ha⟩, minorAxis := ⟨b, hb⟩ }
      let F : Omega.Zeta.IntegerEllipse :=
        { majorAxis := ⟨c, hc⟩, minorAxis := ⟨d, hd⟩ }
      have hProduct : a * b = c * d := by
        let M := a * b * c * d
        have hMpos : 0 < M := by
          dsimp [M]
          exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos ha hb) hc) hd
        have hEq :
            Nat.gcd a M * Nat.gcd b M = Nat.gcd c M * Nat.gcd d M := by
          calc
            Nat.gcd a M * Nat.gcd b M = K a b M := (hK a b M hMpos).symm
            _ = K c d M := hProfile M hMpos
            _ = Nat.gcd c M * Nat.gcd d M := hK c d M hMpos
        have haM : a ∣ M := ⟨b * c * d, by dsimp [M]; ring⟩
        have hbM : b ∣ M := ⟨a * c * d, by dsimp [M]; ring⟩
        have hcM : c ∣ M := ⟨a * b * d, by dsimp [M]; ring⟩
        have hdM : d ∣ M := ⟨a * b * c, by dsimp [M]; ring⟩
        simpa [Nat.gcd_eq_left haM, Nat.gcd_eq_left hbM, Nat.gcd_eq_left hcM,
          Nat.gcd_eq_left hdM] using hEq
      have hPrimePowers :
          ∀ p k : ℕ,
            Nat.gcd (E.majorAxis : ℕ) (p ^ k) * Nat.gcd (E.minorAxis : ℕ) (p ^ k) =
              Nat.gcd (F.majorAxis : ℕ) (p ^ k) * Nat.gcd (F.minorAxis : ℕ) (p ^ k) := by
        intro p k
        by_cases hzero : p ^ k = 0
        · simp [E, F, hzero, Nat.gcd_zero_right, hProduct]
        · have hpos : 0 < p ^ k := Nat.pos_of_ne_zero hzero
          calc
            Nat.gcd (E.majorAxis : ℕ) (p ^ k) * Nat.gcd (E.minorAxis : ℕ) (p ^ k) =
                K a b (p ^ k) := by
              simpa [E] using (hK a b (p ^ k) hpos).symm
            _ = K c d (p ^ k) := hProfile (p ^ k) hpos
            _ = Nat.gcd (F.majorAxis : ℕ) (p ^ k) *
                Nat.gcd (F.minorAxis : ℕ) (p ^ k) := by
              simpa [F] using hK c d (p ^ k) hpos
      have hPairZeta :=
        (Omega.Zeta.paper_xi_integer_ellipse_mod_kernel_spectrum_primewise_unordered E F).1
          hPrimePowers
      have hPair :
          ∀ p : ℕ,
            ({a.factorization p, b.factorization p} : Finset ℕ) =
              ({c.factorization p, d.factorization p} : Finset ℕ) := by
        intro p
        simpa [E, F] using hPairZeta p
      exact
        ⟨conclusion_ellipse_kernel_audit_smith_orbit_blindness_gcd_eq_of_pair_profile
            ha0 hb0 hc0 hd0 hPair,
          conclusion_ellipse_kernel_audit_smith_orbit_blindness_lcm_eq_of_pair_profile
            ha0 hb0 hc0 hd0 hPair⟩
    · rintro ⟨hgcd, hlcm⟩ m hm
      calc
        K a b m = Nat.gcd a m * Nat.gcd b m := hK a b m hm
        _ = Nat.gcd m a * Nat.gcd m b := by rw [Nat.gcd_comm a m, Nat.gcd_comm b m]
        _ = Nat.gcd m (Nat.gcd a b) * Nat.gcd m (Nat.lcm a b) :=
          (conclusion_ellipse_kernel_audit_smith_orbit_blindness_gcd_lcm_profile
            m a b ha0 hb0).symm
        _ = Nat.gcd m (Nat.gcd c d) * Nat.gcd m (Nat.lcm c d) := by rw [hgcd, hlcm]
        _ = Nat.gcd m c * Nat.gcd m d :=
          conclusion_ellipse_kernel_audit_smith_orbit_blindness_gcd_lcm_profile
            m c d hc0 hd0
        _ = Nat.gcd c m * Nat.gcd d m := by rw [Nat.gcd_comm m c, Nat.gcd_comm m d]
        _ = K c d m := (hK c d m hm).symm
  · intro a b ha hb
    exact hClass (Nat.lcm a b / Nat.gcd a b)

end Omega.Conclusion

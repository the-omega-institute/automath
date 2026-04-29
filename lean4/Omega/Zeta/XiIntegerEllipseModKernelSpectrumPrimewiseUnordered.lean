import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic
import Omega.Zeta.XiTimePart76IntegerEllipseAtomicLengthDivisibility

namespace Omega.Zeta

private lemma xi_integer_ellipse_mod_kernel_spectrum_primewise_unordered_pair_eq_or_swap
    {x y u v : Nat} (h : ({x, y} : Finset Nat) = ({u, v} : Finset Nat)) :
    (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
  by_cases hxy : x = y
  · subst y
    have hcard' : 1 = ({u, v} : Finset Nat).card := by
      simpa [Finset.pair_eq_singleton] using congrArg Finset.card h
    have hcard : ({u, v} : Finset Nat).card = 1 := hcard'.symm
    have huv : u = v := by
      by_cases huv : u = v
      · exact huv
      · simp [huv] at hcard
    have hu : u = x := by
      have hu_mem : u ∈ ({x, x} : Finset Nat) := by
        simpa [h] using (show u ∈ ({u, v} : Finset Nat) by simp)
      simpa [Finset.pair_eq_singleton] using hu_mem
    have hv : v = x := by
      have hv_mem : v ∈ ({x, x} : Finset Nat) := by
        simpa [h] using (show v ∈ ({u, v} : Finset Nat) by simp)
      simpa [Finset.pair_eq_singleton] using hv_mem
    exact Or.inl ⟨hu.symm, hv.symm⟩
  · have hcard : ({u, v} : Finset Nat).card = 2 := by
      have hcard' : 2 = ({u, v} : Finset Nat).card := by
        simpa [hxy] using congrArg Finset.card h
      exact hcard'.symm
    have huv : u ≠ v := by
      intro huv
      simp [huv] at hcard
    have hxmem : x ∈ ({u, v} : Finset Nat) := by
      simpa [h] using (show x ∈ ({x, y} : Finset Nat) by simp)
    have hymem : y ∈ ({u, v} : Finset Nat) := by
      simpa [h] using (show y ∈ ({x, y} : Finset Nat) by simp)
    have hxu : x = u ∨ x = v := by
      simpa [Finset.mem_insert, Finset.mem_singleton] using hxmem
    have hyu : y = u ∨ y = v := by
      simpa [Finset.mem_insert, Finset.mem_singleton] using hymem
    rcases hxu with hxu | hxv
    · rcases hyu with hyu | hyv
      · exfalso
        exact hxy (hxu.trans hyu.symm)
      · exact Or.inl ⟨hxu, hyv⟩
    · rcases hyu with hyu | hyv
      · exact Or.inr ⟨hxv, hyu⟩
      · exfalso
        exact hxy (hxv.trans hyv.symm)

private lemma
    xi_integer_ellipse_mod_kernel_spectrum_primewise_unordered_pair_eq_or_swap_of_min_add_eq
    {x y u v : Nat} (hmin : min x y = min u v) (hsum : x + y = u + v) :
    (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
  have hmax : max x y = max u v := by
    have hxy := min_add_max x y
    have huv := min_add_max u v
    omega
  by_cases hxy : x ≤ y
  · have hx : x = min x y := (Nat.min_eq_left hxy).symm
    have hy : y = max x y := (Nat.max_eq_right hxy).symm
    by_cases huv : u ≤ v
    · have hu : u = min u v := (Nat.min_eq_left huv).symm
      have hv : v = max u v := (Nat.max_eq_right huv).symm
      exact Or.inl (by omega)
    · have hvu : v ≤ u := Nat.le_of_not_ge huv
      have hu : u = max u v := (Nat.max_eq_left hvu).symm
      have hv : v = min u v := (Nat.min_eq_right hvu).symm
      exact Or.inr (by omega)
  · have hyx : y ≤ x := Nat.le_of_not_ge hxy
    have hx : x = max x y := (Nat.max_eq_left hyx).symm
    have hy : y = min x y := (Nat.min_eq_right hyx).symm
    by_cases huv : u ≤ v
    · have hu : u = min u v := (Nat.min_eq_left huv).symm
      have hv : v = max u v := (Nat.max_eq_right huv).symm
      exact Or.inr (by omega)
    · have hvu : v ≤ u := Nat.le_of_not_ge huv
      have hu : u = max u v := (Nat.max_eq_left hvu).symm
      have hv : v = min u v := (Nat.min_eq_right hvu).symm
      exact Or.inl (by omega)

private lemma xi_integer_ellipse_mod_kernel_spectrum_primewise_unordered_gcd_power_factorization
    (a p k q : Nat) (ha : a ≠ 0) (hp0 : p ≠ 0) :
    (Nat.gcd a (p ^ k)).factorization q = min (a.factorization q) (k * p.factorization q) := by
  rw [Nat.factorization_gcd ha (pow_ne_zero k hp0), Finsupp.inf_apply, Nat.factorization_pow,
    Finsupp.smul_apply, nsmul_eq_mul]
  simp [Nat.mul_comm]

private lemma
    xi_integer_ellipse_mod_kernel_spectrum_primewise_unordered_gcd_prime_power_factorization_at_prime
    (a p k : Nat) (ha : a ≠ 0) (hp : Nat.Prime p) :
    (Nat.gcd a (p ^ k)).factorization p = min (a.factorization p) k := by
  rw [Nat.factorization_gcd ha (pow_ne_zero k hp.ne_zero), Finsupp.inf_apply,
    Nat.Prime.factorization_pow hp]
  simp

private lemma xi_integer_ellipse_mod_kernel_spectrum_primewise_unordered_axis_product_eq
    (E F : IntegerEllipse)
    (h :
      ∀ p : Nat,
        ({((E.majorAxis : Nat).factorization p), ((E.minorAxis : Nat).factorization p)} :
            Finset Nat) =
          ({((F.majorAxis : Nat).factorization p), ((F.minorAxis : Nat).factorization p)} :
            Finset Nat)) :
    (E.majorAxis : Nat) * (E.minorAxis : Nat) = (F.majorAxis : Nat) * (F.minorAxis : Nat) := by
  apply Nat.eq_of_factorization_eq
    (Nat.mul_ne_zero (Nat.ne_of_gt E.majorAxis.2) (Nat.ne_of_gt E.minorAxis.2))
    (Nat.mul_ne_zero (Nat.ne_of_gt F.majorAxis.2) (Nat.ne_of_gt F.minorAxis.2))
  intro q
  by_cases hq : Nat.Prime q
  · rcases
      xi_integer_ellipse_mod_kernel_spectrum_primewise_unordered_pair_eq_or_swap (h q) with
      ⟨hMaj, hMin⟩ | ⟨hMaj, hMin⟩
    · rw [Nat.factorization_mul (Nat.ne_of_gt E.majorAxis.2) (Nat.ne_of_gt E.minorAxis.2),
        Nat.factorization_mul (Nat.ne_of_gt F.majorAxis.2) (Nat.ne_of_gt F.minorAxis.2),
        Finsupp.add_apply, Finsupp.add_apply]
      let eMaj := (E.majorAxis : Nat).factorization q
      let eMin := (E.minorAxis : Nat).factorization q
      let fMaj := (F.majorAxis : Nat).factorization q
      let fMin := (F.minorAxis : Nat).factorization q
      have hsum1 : eMaj + eMin = fMaj + eMin := congrArg (fun z => z + eMin) hMaj
      have hsum2 : fMaj + eMin = fMaj + fMin := congrArg (fun z => fMaj + z) hMin
      exact hsum1.trans hsum2
    · rw [Nat.factorization_mul (Nat.ne_of_gt E.majorAxis.2) (Nat.ne_of_gt E.minorAxis.2),
        Nat.factorization_mul (Nat.ne_of_gt F.majorAxis.2) (Nat.ne_of_gt F.minorAxis.2),
        Finsupp.add_apply, Finsupp.add_apply]
      let eMaj := (E.majorAxis : Nat).factorization q
      let eMin := (E.minorAxis : Nat).factorization q
      let fMaj := (F.majorAxis : Nat).factorization q
      let fMin := (F.minorAxis : Nat).factorization q
      have hsum1 : eMaj + eMin = fMin + eMin := congrArg (fun z => z + eMin) hMaj
      have hsum2 : fMin + eMin = fMin + fMaj := congrArg (fun z => fMin + z) hMin
      exact hsum1.trans (hsum2.trans (Nat.add_comm fMin fMaj))
  · rw [Nat.factorization_mul (Nat.ne_of_gt E.majorAxis.2) (Nat.ne_of_gt E.minorAxis.2),
      Nat.factorization_mul (Nat.ne_of_gt F.majorAxis.2) (Nat.ne_of_gt F.minorAxis.2),
      Finsupp.add_apply, Finsupp.add_apply]
    simp [Nat.factorization_eq_zero_of_not_prime _ hq]

/-- Paper label: `thm:xi-integer-ellipse-mod-kernel-spectrum-primewise-unordered`. -/
theorem paper_xi_integer_ellipse_mod_kernel_spectrum_primewise_unordered (E F : Omega.Zeta.IntegerEllipse) :
    ((∀ p k : Nat,
          Nat.gcd (E.majorAxis : Nat) (p ^ k) * Nat.gcd (E.minorAxis : Nat) (p ^ k) =
            Nat.gcd (F.majorAxis : Nat) (p ^ k) * Nat.gcd (F.minorAxis : Nat) (p ^ k)) ↔
      (∀ p : Nat,
        ({((E.majorAxis : Nat).factorization p), ((E.minorAxis : Nat).factorization p)} :
              Finset Nat) =
          ({((F.majorAxis : Nat).factorization p), ((F.minorAxis : Nat).factorization p)} :
              Finset Nat))) := by
  constructor
  · intro h p
    by_cases hp : Nat.Prime p
    · let x := (E.majorAxis : Nat).factorization p
      let y := (E.minorAxis : Nat).factorization p
      let u := (F.majorAxis : Nat).factorization p
      let v := (F.minorAxis : Nat).factorization p
      have hgcd_ne_zero {a b : Nat} (ha : a ≠ 0) : Nat.gcd a b ≠ 0 := by
        intro hz
        exact ha (Nat.gcd_eq_zero_iff.mp hz).1
      have hsum : x + y = u + v := by
        have hEq := congrArg (fun n : Nat => n.factorization p) (h p (x + y + u + v))
        have hmulE :
            (Nat.gcd (E.majorAxis : Nat) (p ^ (x + y + u + v)) *
                  Nat.gcd (E.minorAxis : Nat) (p ^ (x + y + u + v))).factorization =
              (Nat.gcd (E.majorAxis : Nat) (p ^ (x + y + u + v))).factorization +
                (Nat.gcd (E.minorAxis : Nat) (p ^ (x + y + u + v))).factorization :=
          Nat.factorization_mul (hgcd_ne_zero (Nat.ne_of_gt E.majorAxis.2))
            (hgcd_ne_zero (Nat.ne_of_gt E.minorAxis.2))
        have hmulF :
            (Nat.gcd (F.majorAxis : Nat) (p ^ (x + y + u + v)) *
                  Nat.gcd (F.minorAxis : Nat) (p ^ (x + y + u + v))).factorization =
              (Nat.gcd (F.majorAxis : Nat) (p ^ (x + y + u + v))).factorization +
                (Nat.gcd (F.minorAxis : Nat) (p ^ (x + y + u + v))).factorization :=
          Nat.factorization_mul (hgcd_ne_zero (Nat.ne_of_gt F.majorAxis.2))
            (hgcd_ne_zero (Nat.ne_of_gt F.minorAxis.2))
        change
          ((Nat.gcd (E.majorAxis : Nat) (p ^ (x + y + u + v)) *
                Nat.gcd (E.minorAxis : Nat) (p ^ (x + y + u + v))).factorization p) =
            ((Nat.gcd (F.majorAxis : Nat) (p ^ (x + y + u + v)) *
                Nat.gcd (F.minorAxis : Nat) (p ^ (x + y + u + v))).factorization p) at hEq
        rw [hmulE, hmulF, Finsupp.add_apply, Finsupp.add_apply,
          xi_integer_ellipse_mod_kernel_spectrum_primewise_unordered_gcd_prime_power_factorization_at_prime
            (E.majorAxis : Nat) p (x + y + u + v) (Nat.ne_of_gt E.majorAxis.2) hp,
          xi_integer_ellipse_mod_kernel_spectrum_primewise_unordered_gcd_prime_power_factorization_at_prime
            (E.minorAxis : Nat) p (x + y + u + v) (Nat.ne_of_gt E.minorAxis.2) hp,
          xi_integer_ellipse_mod_kernel_spectrum_primewise_unordered_gcd_prime_power_factorization_at_prime
            (F.majorAxis : Nat) p (x + y + u + v) (Nat.ne_of_gt F.majorAxis.2) hp,
          xi_integer_ellipse_mod_kernel_spectrum_primewise_unordered_gcd_prime_power_factorization_at_prime
            (F.minorAxis : Nat) p (x + y + u + v) (Nat.ne_of_gt F.minorAxis.2) hp] at hEq
        have hxle : x ≤ x + y + u + v := by omega
        have hyle : y ≤ x + y + u + v := by omega
        have hule : u ≤ x + y + u + v := by omega
        have hvle : v ≤ x + y + u + v := by omega
        simpa [x, y, u, v, Nat.min_eq_left hxle, Nat.min_eq_left hyle, Nat.min_eq_left hule,
          Nat.min_eq_left hvle] using hEq
      have hmin_le : min x y ≤ min u v := by
        have hEq := congrArg (fun n : Nat => n.factorization p) (h p (min x y))
        have hmulE :
            (Nat.gcd (E.majorAxis : Nat) (p ^ min x y) *
                  Nat.gcd (E.minorAxis : Nat) (p ^ min x y)).factorization =
              (Nat.gcd (E.majorAxis : Nat) (p ^ min x y)).factorization +
                (Nat.gcd (E.minorAxis : Nat) (p ^ min x y)).factorization :=
          Nat.factorization_mul (hgcd_ne_zero (Nat.ne_of_gt E.majorAxis.2))
            (hgcd_ne_zero (Nat.ne_of_gt E.minorAxis.2))
        have hmulF :
            (Nat.gcd (F.majorAxis : Nat) (p ^ min x y) *
                  Nat.gcd (F.minorAxis : Nat) (p ^ min x y)).factorization =
              (Nat.gcd (F.majorAxis : Nat) (p ^ min x y)).factorization +
                (Nat.gcd (F.minorAxis : Nat) (p ^ min x y)).factorization :=
          Nat.factorization_mul (hgcd_ne_zero (Nat.ne_of_gt F.majorAxis.2))
            (hgcd_ne_zero (Nat.ne_of_gt F.minorAxis.2))
        change
          ((Nat.gcd (E.majorAxis : Nat) (p ^ min x y) *
                Nat.gcd (E.minorAxis : Nat) (p ^ min x y)).factorization p) =
            ((Nat.gcd (F.majorAxis : Nat) (p ^ min x y) *
                Nat.gcd (F.minorAxis : Nat) (p ^ min x y)).factorization p) at hEq
        rw [hmulE, hmulF, Finsupp.add_apply, Finsupp.add_apply,
          xi_integer_ellipse_mod_kernel_spectrum_primewise_unordered_gcd_prime_power_factorization_at_prime
            (E.majorAxis : Nat) p (min x y) (Nat.ne_of_gt E.majorAxis.2) hp,
          xi_integer_ellipse_mod_kernel_spectrum_primewise_unordered_gcd_prime_power_factorization_at_prime
            (E.minorAxis : Nat) p (min x y) (Nat.ne_of_gt E.minorAxis.2) hp,
          xi_integer_ellipse_mod_kernel_spectrum_primewise_unordered_gcd_prime_power_factorization_at_prime
            (F.majorAxis : Nat) p (min x y) (Nat.ne_of_gt F.majorAxis.2) hp,
          xi_integer_ellipse_mod_kernel_spectrum_primewise_unordered_gcd_prime_power_factorization_at_prime
            (F.minorAxis : Nat) p (min x y) (Nat.ne_of_gt F.minorAxis.2) hp] at hEq
        have hEq' :
            min x y + min x y = min u (min x y) + min v (min x y) := by
          simpa [x, y, u, v, Nat.min_eq_left (Nat.min_le_left _ _),
            Nat.min_eq_left (Nat.min_le_right _ _)] using hEq
        have hule : min x y ≤ u := by
          omega
        have hvle : min x y ≤ v := by
          omega
        exact le_min hule hvle
      have hmin_ge : min u v ≤ min x y := by
        have hEq := congrArg (fun n : Nat => n.factorization p) (h p (min u v))
        have hmulE :
            (Nat.gcd (E.majorAxis : Nat) (p ^ min u v) *
                  Nat.gcd (E.minorAxis : Nat) (p ^ min u v)).factorization =
              (Nat.gcd (E.majorAxis : Nat) (p ^ min u v)).factorization +
                (Nat.gcd (E.minorAxis : Nat) (p ^ min u v)).factorization :=
          Nat.factorization_mul (hgcd_ne_zero (Nat.ne_of_gt E.majorAxis.2))
            (hgcd_ne_zero (Nat.ne_of_gt E.minorAxis.2))
        have hmulF :
            (Nat.gcd (F.majorAxis : Nat) (p ^ min u v) *
                  Nat.gcd (F.minorAxis : Nat) (p ^ min u v)).factorization =
              (Nat.gcd (F.majorAxis : Nat) (p ^ min u v)).factorization +
                (Nat.gcd (F.minorAxis : Nat) (p ^ min u v)).factorization :=
          Nat.factorization_mul (hgcd_ne_zero (Nat.ne_of_gt F.majorAxis.2))
            (hgcd_ne_zero (Nat.ne_of_gt F.minorAxis.2))
        change
          ((Nat.gcd (E.majorAxis : Nat) (p ^ min u v) *
                Nat.gcd (E.minorAxis : Nat) (p ^ min u v)).factorization p) =
            ((Nat.gcd (F.majorAxis : Nat) (p ^ min u v) *
                Nat.gcd (F.minorAxis : Nat) (p ^ min u v)).factorization p) at hEq
        rw [hmulE, hmulF, Finsupp.add_apply, Finsupp.add_apply,
          xi_integer_ellipse_mod_kernel_spectrum_primewise_unordered_gcd_prime_power_factorization_at_prime
            (E.majorAxis : Nat) p (min u v) (Nat.ne_of_gt E.majorAxis.2) hp,
          xi_integer_ellipse_mod_kernel_spectrum_primewise_unordered_gcd_prime_power_factorization_at_prime
            (E.minorAxis : Nat) p (min u v) (Nat.ne_of_gt E.minorAxis.2) hp,
          xi_integer_ellipse_mod_kernel_spectrum_primewise_unordered_gcd_prime_power_factorization_at_prime
            (F.majorAxis : Nat) p (min u v) (Nat.ne_of_gt F.majorAxis.2) hp,
          xi_integer_ellipse_mod_kernel_spectrum_primewise_unordered_gcd_prime_power_factorization_at_prime
            (F.minorAxis : Nat) p (min u v) (Nat.ne_of_gt F.minorAxis.2) hp] at hEq
        have hEq' :
            min x (min u v) + min y (min u v) = min u v + min u v := by
          simpa [x, y, u, v, Nat.min_eq_left (Nat.min_le_left _ _),
            Nat.min_eq_left (Nat.min_le_right _ _)] using hEq
        have hxle : min u v ≤ x := by
          omega
        have hyle : min u v ≤ y := by
          omega
        exact le_min hxle hyle
      have hmin : min x y = min u v := Nat.le_antisymm hmin_le hmin_ge
      rcases
          xi_integer_ellipse_mod_kernel_spectrum_primewise_unordered_pair_eq_or_swap_of_min_add_eq
            hmin hsum with
        ⟨hxu, hyv⟩ | ⟨hxv, hyu⟩
      · simpa [x, y, u, v, hxu, hyv]
      · simpa [x, y, u, v, hxv, hyu] using (Finset.pair_comm u v).symm
    · simp [Nat.factorization_eq_zero_of_not_prime (E.majorAxis : Nat) hp,
        Nat.factorization_eq_zero_of_not_prime (E.minorAxis : Nat) hp,
        Nat.factorization_eq_zero_of_not_prime (F.majorAxis : Nat) hp,
        Nat.factorization_eq_zero_of_not_prime (F.minorAxis : Nat) hp]
  · intro h p k
    by_cases hp0 : p = 0
    · subst p
      cases k with
      | zero =>
          simp
      | succ k =>
          simpa using
            xi_integer_ellipse_mod_kernel_spectrum_primewise_unordered_axis_product_eq E F h
    · apply Nat.eq_of_factorization_eq
        (Nat.mul_ne_zero
          (by
            intro hz
            exact (Nat.ne_of_gt E.majorAxis.2) (Nat.gcd_eq_zero_iff.mp hz).1)
          (by
            intro hz
            exact (Nat.ne_of_gt E.minorAxis.2) (Nat.gcd_eq_zero_iff.mp hz).1))
        (Nat.mul_ne_zero
          (by
            intro hz
            exact (Nat.ne_of_gt F.majorAxis.2) (Nat.gcd_eq_zero_iff.mp hz).1)
          (by
            intro hz
            exact (Nat.ne_of_gt F.minorAxis.2) (Nat.gcd_eq_zero_iff.mp hz).1))
      intro q
      by_cases hq : Nat.Prime q
      · rcases
          xi_integer_ellipse_mod_kernel_spectrum_primewise_unordered_pair_eq_or_swap (h q) with
          ⟨hMaj, hMin⟩ | ⟨hMaj, hMin⟩
        · rw [Nat.factorization_mul
              (by
                intro hz
                exact (Nat.ne_of_gt E.majorAxis.2) (Nat.gcd_eq_zero_iff.mp hz).1)
              (by
                intro hz
                exact (Nat.ne_of_gt E.minorAxis.2) (Nat.gcd_eq_zero_iff.mp hz).1),
            Nat.factorization_mul
              (by
                intro hz
                exact (Nat.ne_of_gt F.majorAxis.2) (Nat.gcd_eq_zero_iff.mp hz).1)
              (by
                intro hz
                exact (Nat.ne_of_gt F.minorAxis.2) (Nat.gcd_eq_zero_iff.mp hz).1),
            Finsupp.add_apply, Finsupp.add_apply,
            xi_integer_ellipse_mod_kernel_spectrum_primewise_unordered_gcd_power_factorization
              (E.majorAxis : Nat) p k q (Nat.ne_of_gt E.majorAxis.2) hp0,
            xi_integer_ellipse_mod_kernel_spectrum_primewise_unordered_gcd_power_factorization
              (E.minorAxis : Nat) p k q (Nat.ne_of_gt E.minorAxis.2) hp0,
            xi_integer_ellipse_mod_kernel_spectrum_primewise_unordered_gcd_power_factorization
              (F.majorAxis : Nat) p k q (Nat.ne_of_gt F.majorAxis.2) hp0,
            xi_integer_ellipse_mod_kernel_spectrum_primewise_unordered_gcd_power_factorization
              (F.minorAxis : Nat) p k q (Nat.ne_of_gt F.minorAxis.2) hp0]
          simp [hMaj, hMin]
        · rw [Nat.factorization_mul
              (by
                intro hz
                exact (Nat.ne_of_gt E.majorAxis.2) (Nat.gcd_eq_zero_iff.mp hz).1)
              (by
                intro hz
                exact (Nat.ne_of_gt E.minorAxis.2) (Nat.gcd_eq_zero_iff.mp hz).1),
            Nat.factorization_mul
              (by
                intro hz
                exact (Nat.ne_of_gt F.majorAxis.2) (Nat.gcd_eq_zero_iff.mp hz).1)
              (by
                intro hz
                exact (Nat.ne_of_gt F.minorAxis.2) (Nat.gcd_eq_zero_iff.mp hz).1),
            Finsupp.add_apply, Finsupp.add_apply,
            xi_integer_ellipse_mod_kernel_spectrum_primewise_unordered_gcd_power_factorization
              (E.majorAxis : Nat) p k q (Nat.ne_of_gt E.majorAxis.2) hp0,
            xi_integer_ellipse_mod_kernel_spectrum_primewise_unordered_gcd_power_factorization
              (E.minorAxis : Nat) p k q (Nat.ne_of_gt E.minorAxis.2) hp0,
            xi_integer_ellipse_mod_kernel_spectrum_primewise_unordered_gcd_power_factorization
              (F.majorAxis : Nat) p k q (Nat.ne_of_gt F.majorAxis.2) hp0,
            xi_integer_ellipse_mod_kernel_spectrum_primewise_unordered_gcd_power_factorization
              (F.minorAxis : Nat) p k q (Nat.ne_of_gt F.minorAxis.2) hp0]
          simp [hMaj, hMin, Nat.add_comm]
      · simp [Nat.factorization_eq_zero_of_not_prime _ hq]

end Omega.Zeta

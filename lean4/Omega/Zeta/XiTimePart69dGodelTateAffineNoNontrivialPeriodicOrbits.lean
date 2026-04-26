import Mathlib.Tactic

namespace Omega.Zeta

def xi_time_part69d_godel_tate_affine_no_nontrivial_periodic_orbits_affine
    {M : Type*} [AddCommGroup M] (B : M →+ M) (t : M) : M → M :=
  fun x => B x + t

def xi_time_part69d_godel_tate_affine_no_nontrivial_periodic_orbits_translation
    {M : Type*} [AddCommGroup M] (t : M) : M → M :=
  fun x => x + t

lemma xi_time_part69d_godel_tate_affine_no_nontrivial_periodic_orbits_iterate_sub_fixed
    {M : Type*} [AddCommGroup M] (B : M →+ M) (t p : M)
    (hp : B p + t = p) :
    ∀ (n : ℕ) (x : M),
      (xi_time_part69d_godel_tate_affine_no_nontrivial_periodic_orbits_affine B t)^[n] x -
          p =
        (B^[n]) (x - p) := by
  intro n
  induction n with
  | zero =>
      intro x
      simp
  | succ n ih =>
      intro x
      have ht : t = p - B p := by
        calc
          t = (B p + t) - B p := by abel
          _ = p - B p := by rw [hp]
      have hstep : B x + t - p = B (x - p) := by
        rw [ht, map_sub]
        abel
      calc
        (xi_time_part69d_godel_tate_affine_no_nontrivial_periodic_orbits_affine B t)^[n + 1]
              x - p =
            (xi_time_part69d_godel_tate_affine_no_nontrivial_periodic_orbits_affine B t)^[n]
                (B x + t) - p := by
              rfl
        _ = (B^[n]) (B x + t - p) := ih (B x + t)
        _ = (B^[n]) (B (x - p)) := by
              rw [hstep]
        _ = (B^[n + 1]) (x - p) := by
              rfl

lemma xi_time_part69d_godel_tate_affine_no_nontrivial_periodic_orbits_translation_iterate
    {M : Type*} [AddCommGroup M] (t : M) :
    ∀ (n : ℕ) (x : M),
      (xi_time_part69d_godel_tate_affine_no_nontrivial_periodic_orbits_translation t)^[n] x =
        x + n • t := by
  intro n
  induction n with
  | zero =>
      intro x
      simp
  | succ n ih =>
      intro x
      calc
        (xi_time_part69d_godel_tate_affine_no_nontrivial_periodic_orbits_translation t)^[n + 1]
            x =
            (xi_time_part69d_godel_tate_affine_no_nontrivial_periodic_orbits_translation t)^[n]
              (x + t) := by
              rfl
        _ = x + t + n • t := ih (x + t)
        _ = x + (n + 1) • t := by
              rw [succ_nsmul]
              abel

def xi_time_part69d_godel_tate_affine_no_nontrivial_periodic_orbits_statement : Prop :=
  (∀ {M : Type*} [AddCommGroup M] (B : M →+ M) (t p : M),
      B p + t = p →
        (∀ n : ℕ, 0 < n → ∀ y : M, (B^[n]) y = y → y = 0) →
          (∀ ⦃x : M⦄ ⦃n : ℕ⦄,
            0 < n →
              (xi_time_part69d_godel_tate_affine_no_nontrivial_periodic_orbits_affine B t)^[n]
                  x = x →
                x = p) ∧
            ∀ x : M,
              xi_time_part69d_godel_tate_affine_no_nontrivial_periodic_orbits_affine B t x =
                x ↔ x = p) ∧
    ∀ {M : Type*} [AddCommGroup M] (t : M),
      t ≠ 0 →
        (∀ n : ℕ, 0 < n → n • t ≠ 0) →
          ∀ ⦃x : M⦄ ⦃n : ℕ⦄,
            0 < n →
              (xi_time_part69d_godel_tate_affine_no_nontrivial_periodic_orbits_translation t)^[n]
                  x ≠ x

/-- Paper label: `thm:xi-time-part69d-godel-tate-affine-no-nontrivial-periodic-orbits`.
Contractions with invertible `1 - B^n` have only their fixed point as a periodic point, while
nonzero torsion-free translations have no periodic points. -/
theorem paper_xi_time_part69d_godel_tate_affine_no_nontrivial_periodic_orbits :
    xi_time_part69d_godel_tate_affine_no_nontrivial_periodic_orbits_statement := by
  constructor
  · intro M _ B t p hp hcontract
    constructor
    · intro x n hn hperiod
      have hiter :=
        xi_time_part69d_godel_tate_affine_no_nontrivial_periodic_orbits_iterate_sub_fixed
          B t p hp n x
      have hfixed : (B^[n]) (x - p) = x - p := by
        rw [← hiter, hperiod]
      have hzero : x - p = 0 := hcontract n hn (x - p) hfixed
      exact sub_eq_zero.mp hzero
    · intro x
      constructor
      · intro hx
        have hperiod :
            (xi_time_part69d_godel_tate_affine_no_nontrivial_periodic_orbits_affine B t)^[1]
                x = x := by
          simpa using hx
        have honly :=
          (xi_time_part69d_godel_tate_affine_no_nontrivial_periodic_orbits_iterate_sub_fixed
            B t p hp 1 x)
        have hfixed : (B^[1]) (x - p) = x - p := by
          rw [← honly, hperiod]
        have hzero : x - p = 0 := hcontract 1 (by norm_num) (x - p) hfixed
        exact sub_eq_zero.mp hzero
      · intro hx
        rw [hx]
        exact hp
  · intro M _ t ht htorsion x n hn hperiod
    have hiter :=
      xi_time_part69d_godel_tate_affine_no_nontrivial_periodic_orbits_translation_iterate t n x
    have hzero : n • t = 0 := by
      have hxadd : x + n • t = x := by
        rw [← hiter]
        exact hperiod
      calc
        n • t = (x + n • t) - x := by abel
        _ = 0 := by rw [hxadd]; simp
    exact htorsion n hn hzero

end Omega.Zeta

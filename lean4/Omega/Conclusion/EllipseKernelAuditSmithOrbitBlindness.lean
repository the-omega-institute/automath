import Mathlib.Tactic

namespace Omega.Conclusion

lemma conclusion_ellipse_kernel_audit_smith_orbit_blindness_square_forces_eq
    {g x y : ℕ} (hg : 0 < g) (hx : x ≤ g) (hy : y ≤ g) (hxy : x * y = g * g) :
    x = g ∧ y = g := by
  have hxy_le_xg : x * y ≤ x * g := Nat.mul_le_mul_left x hy
  have hxg_le_gg : x * g ≤ g * g := Nat.mul_le_mul_right g hx
  have hgg_le_xg : g * g ≤ x * g := by
    simpa [hxy] using hxy_le_xg
  have hxg : x * g = g * g := le_antisymm hxg_le_gg hgg_le_xg
  have hx_eq : x = g := Nat.eq_of_mul_eq_mul_right hg hxg
  have hgy : g * y = g * g := by
    rwa [hx_eq] at hxy
  have hy_eq : y = g := Nat.eq_of_mul_eq_mul_left hg hgy
  exact ⟨hx_eq, hy_eq⟩

lemma conclusion_ellipse_kernel_audit_smith_orbit_blindness_min_max_identity
    (u v w : ℕ) :
    minDefault u (minDefault v w) + minDefault u (maxDefault v w) =
      minDefault u v + minDefault u w := by
  unfold minDefault maxDefault
  split_ifs <;> omega

lemma conclusion_ellipse_kernel_audit_smith_orbit_blindness_gcd_mul_gcd_eq
    (m a b : ℕ) (hm : m ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    Nat.gcd m a * Nat.gcd m b =
      Nat.gcd m (Nat.gcd a b) * Nat.gcd m (Nat.lcm a b) := by
  apply Nat.eq_of_factorization_eq
  · exact mul_ne_zero (Nat.gcd_ne_zero_left hm) (Nat.gcd_ne_zero_left hm)
  · exact mul_ne_zero (Nat.gcd_ne_zero_left hm) (Nat.gcd_ne_zero_left hm)
  intro p
  rw [Nat.factorization_mul (Nat.gcd_ne_zero_left hm) (Nat.gcd_ne_zero_left hm)]
  rw [Nat.factorization_mul (Nat.gcd_ne_zero_left hm) (Nat.gcd_ne_zero_left hm)]
  rw [Nat.factorization_gcd hm ha, Nat.factorization_gcd hm hb]
  rw [Nat.factorization_gcd hm (Nat.gcd_ne_zero_left ha)]
  rw [Nat.factorization_gcd hm (Nat.lcm_ne_zero ha hb)]
  rw [Nat.factorization_gcd ha hb, Nat.factorization_lcm ha hb]
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.inf_apply, Finsupp.sup_apply,
    inf_eq_minDefault, sup_eq_maxDefault]
  exact (conclusion_ellipse_kernel_audit_smith_orbit_blindness_min_max_identity
    (m.factorization p) (a.factorization p) (b.factorization p)).symm

lemma conclusion_ellipse_kernel_audit_smith_orbit_blindness_gcd_eq_of_profile
    {a b c d : ℕ} (ha : 0 < a) (_hb : 0 < b)
    (h : ∀ m : ℕ, 0 < m →
      Nat.gcd m a * Nat.gcd m b = Nat.gcd m c * Nat.gcd m d) :
    Nat.gcd a b ∣ Nat.gcd c d := by
  let g := Nat.gcd a b
  have hg : 0 < g := Nat.gcd_pos_of_pos_left b ha
  have hprofile := h g hg
  have hga : Nat.gcd g a = g := by
    exact Nat.gcd_eq_left (Nat.gcd_dvd_left a b)
  have hgb : Nat.gcd g b = g := by
    exact Nat.gcd_eq_left (Nat.gcd_dvd_right a b)
  have hprod : Nat.gcd g c * Nat.gcd g d = g * g := by
    simpa [g, hga, hgb] using hprofile.symm
  have hcg_le : Nat.gcd g c ≤ g := Nat.gcd_le_left c hg
  have hdg_le : Nat.gcd g d ≤ g := Nat.gcd_le_left d hg
  rcases conclusion_ellipse_kernel_audit_smith_orbit_blindness_square_forces_eq hg
      hcg_le hdg_le hprod with ⟨hc_eq, hd_eq⟩
  have hgc : g ∣ c := Nat.gcd_eq_left_iff_dvd.mp hc_eq
  have hgd : g ∣ d := Nat.gcd_eq_left_iff_dvd.mp hd_eq
  exact Nat.dvd_gcd hgc hgd

/-- Paper label: `thm:conclusion-ellipse-kernel-audit-smith-orbit-blindness`. -/
theorem paper_conclusion_ellipse_kernel_audit_smith_orbit_blindness
    (a b c d : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    ((∀ m : ℕ, 0 < m →
        Nat.gcd m a * Nat.gcd m b = Nat.gcd m c * Nat.gcd m d) ↔
      Nat.gcd a b = Nat.gcd c d ∧ Nat.lcm a b = Nat.lcm c d) := by
  constructor
  · intro h
    have hgcd_dvd :
        Nat.gcd a b ∣ Nat.gcd c d :=
      conclusion_ellipse_kernel_audit_smith_orbit_blindness_gcd_eq_of_profile ha hb h
    have hsymm :
        ∀ m : ℕ, 0 < m →
          Nat.gcd m c * Nat.gcd m d = Nat.gcd m a * Nat.gcd m b := by
      intro m hm
      exact (h m hm).symm
    have hgcd_dvd' :
        Nat.gcd c d ∣ Nat.gcd a b :=
      conclusion_ellipse_kernel_audit_smith_orbit_blindness_gcd_eq_of_profile hc hd hsymm
    have hgcd : Nat.gcd a b = Nat.gcd c d := Nat.dvd_antisymm hgcd_dvd hgcd_dvd'
    let M := a * b * c * d
    have hM : 0 < M := by positivity
    have hprod_profile := h M hM
    have hMa : Nat.gcd M a = a := by
      exact Nat.gcd_eq_right (by
        refine ⟨b * c * d, ?_⟩
        simp [M, mul_assoc])
    have hMb : Nat.gcd M b = b := by
      exact Nat.gcd_eq_right (by
        refine ⟨a * c * d, ?_⟩
        ring)
    have hMc : Nat.gcd M c = c := by
      exact Nat.gcd_eq_right (by
        refine ⟨a * b * d, ?_⟩
        ring)
    have hMd : Nat.gcd M d = d := by
      exact Nat.gcd_eq_right (by
        refine ⟨a * b * c, ?_⟩
        ring)
    have hprod : a * b = c * d := by
      simpa [hMa, hMb, hMc, hMd] using hprod_profile
    have hlcm_mul :
        Nat.gcd a b * Nat.lcm a b = Nat.gcd c d * Nat.lcm c d := by
      rw [Nat.gcd_mul_lcm, Nat.gcd_mul_lcm, hprod]
    have hgpos : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
    have hlcm : Nat.lcm a b = Nat.lcm c d := by
      exact Nat.eq_of_mul_eq_mul_left hgpos (by simpa [hgcd] using hlcm_mul)
    exact ⟨hgcd, hlcm⟩
  · rintro ⟨hgcd, hlcm⟩ m hm
    have hm0 : m ≠ 0 := Nat.ne_of_gt hm
    have hab0 : a ≠ 0 := Nat.ne_of_gt ha
    have hbb0 : b ≠ 0 := Nat.ne_of_gt hb
    have hc0 : c ≠ 0 := Nat.ne_of_gt hc
    have hd0 : d ≠ 0 := Nat.ne_of_gt hd
    rw [conclusion_ellipse_kernel_audit_smith_orbit_blindness_gcd_mul_gcd_eq
        m a b hm0 hab0 hbb0]
    rw [conclusion_ellipse_kernel_audit_smith_orbit_blindness_gcd_mul_gcd_eq
        m c d hm0 hc0 hd0]
    rw [hgcd, hlcm]

end Omega.Conclusion

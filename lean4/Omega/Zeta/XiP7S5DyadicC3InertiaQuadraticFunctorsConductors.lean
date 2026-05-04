import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-p7-s5-dyadic-c3-inertia-quadratic-functors-conductors`. -/
theorem paper_xi_p7_s5_dyadic_c3_inertia_quadratic_functors_conductors
    (a b dim sym2 wedge2 : Fin 3 -> Nat) (tensor : Fin 3 -> Fin 3 -> Nat)
    (ha : a 0 = 2 ∧ a 1 = 1 ∧ a 2 = 2)
    (hb : b 0 = 1 ∧ b 1 = 2 ∧ b 2 = 2)
    (hdim : dim 0 = 4 ∧ dim 1 = 5 ∧ dim 2 = 6)
    (hsym :
      ∀ i, sym2 i = (dim i * (dim i + 1)) / 2 -
        ((a i * (a i + 1)) / 2 + b i ^ 2))
    (hwedge :
      ∀ i, wedge2 i = (dim i * (dim i - 1)) / 2 -
        ((a i * (a i - 1)) / 2 + b i ^ 2))
    (htensor : ∀ i j, tensor i j = dim i * dim j - (a i * a j + 2 * b i * b j)) :
    (sym2 0 = 6 ∧ wedge2 0 = 4) ∧
      (sym2 1 = 10 ∧ wedge2 1 = 6) ∧
      (sym2 2 = 14 ∧ wedge2 2 = 10) ∧
      tensor 0 1 = 14 ∧ tensor 0 2 = 16 ∧ tensor 1 2 = 20 := by
  rcases ha with ⟨ha0, ha1, ha2⟩
  rcases hb with ⟨hb0, hb1, hb2⟩
  rcases hdim with ⟨hdim0, hdim1, hdim2⟩
  have hsym0 : sym2 0 = 6 := by
    have h := hsym 0
    norm_num [hdim0, ha0, hb0] at h
    exact h
  have hwedge0 : wedge2 0 = 4 := by
    have h := hwedge 0
    norm_num [hdim0, ha0, hb0] at h
    exact h
  have hsym1 : sym2 1 = 10 := by
    have h := hsym 1
    norm_num [hdim1, ha1, hb1] at h
    exact h
  have hwedge1 : wedge2 1 = 6 := by
    have h := hwedge 1
    norm_num [hdim1, ha1, hb1] at h
    exact h
  have hsym2 : sym2 2 = 14 := by
    have h := hsym 2
    norm_num [hdim2, ha2, hb2] at h
    exact h
  have hwedge2 : wedge2 2 = 10 := by
    have h := hwedge 2
    norm_num [hdim2, ha2, hb2] at h
    exact h
  have htensor01 : tensor 0 1 = 14 := by
    have h := htensor 0 1
    norm_num [hdim0, hdim1, ha0, ha1, hb0, hb1] at h
    exact h
  have htensor02 : tensor 0 2 = 16 := by
    have h := htensor 0 2
    norm_num [hdim0, hdim2, ha0, ha2, hb0, hb2] at h
    exact h
  have htensor12 : tensor 1 2 = 20 := by
    have h := htensor 1 2
    norm_num [hdim1, hdim2, ha1, ha2, hb1, hb2] at h
    exact h
  exact ⟨⟨hsym0, hwedge0⟩, ⟨hsym1, hwedge1⟩, ⟨hsym2, hwedge2⟩,
    htensor01, htensor02, htensor12⟩

end Omega.Zeta

import Mathlib.Tactic

namespace Omega.Zeta

/-- Split a length-`N` quaternary word into its first `m` digits and its remaining `N - m` free
digits. -/
noncomputable def xi_coherence_affine_subcube_splitEquiv
    (N m : ℕ) (hm : m ≤ N) :
    (Fin N → Fin 4) ≃ (Fin m → Fin 4) × (Fin (N - m) → Fin 4) := by
  have hsplit : m + (N - m) = N := by omega
  let e : Fin m ⊕ Fin (N - m) ≃ Fin N :=
    (finSumFinEquiv : Fin m ⊕ Fin (N - m) ≃ Fin (m + (N - m))).trans
      (finCongr hsplit)
  exact (Equiv.piCongrLeft (fun _ => Fin 4) e).symm.trans
    (Equiv.sumArrowEquivProdArrow (Fin m) (Fin (N - m)) (Fin 4))

/-- The coherence class obtained by fixing the first `m` digits of a length-`N` base-`4` word. -/
def xi_coherence_affine_subcube_class
    (N m : ℕ) (hm : m ≤ N) (x : Fin N → Fin 4) : Type :=
  { y : Fin N → Fin 4 //
      (xi_coherence_affine_subcube_splitEquiv N m hm y).1 =
        (xi_coherence_affine_subcube_splitEquiv N m hm x).1 }

noncomputable instance xi_coherence_affine_subcube_class_fintype
    (N m : ℕ) (hm : m ≤ N) (x : Fin N → Fin 4) :
    Fintype (xi_coherence_affine_subcube_class N m hm x) :=
  by
    classical
    unfold xi_coherence_affine_subcube_class
    infer_instance

/-- The remaining `N - m` digits provide coordinates on the coherence class. -/
noncomputable def xi_coherence_affine_subcube_suffixEquiv
    (N m : ℕ) (hm : m ≤ N) (x : Fin N → Fin 4) :
    xi_coherence_affine_subcube_class N m hm x ≃ (Fin (N - m) → Fin 4) where
  toFun y := (xi_coherence_affine_subcube_splitEquiv N m hm y.1).2
  invFun suffix :=
    ⟨(xi_coherence_affine_subcube_splitEquiv N m hm).symm
        ((xi_coherence_affine_subcube_splitEquiv N m hm x).1, suffix), by
      simp⟩
  left_inv y := by
    apply Subtype.ext
    apply (xi_coherence_affine_subcube_splitEquiv N m hm).injective
    simpa using
      (Prod.ext y.2.symm rfl :
        ((xi_coherence_affine_subcube_splitEquiv N m hm x).1,
            (xi_coherence_affine_subcube_splitEquiv N m hm y.1).2) =
          xi_coherence_affine_subcube_splitEquiv N m hm y.1)
  right_inv suffix := by
    simp

/-- Cardinality of the coherence class at resolution `m`. -/
noncomputable def xi_coherence_affine_subcube_class_card
    (N m : ℕ) (hm : m ≤ N) (x : Fin N → Fin 4) : ℕ :=
  Fintype.card (xi_coherence_affine_subcube_class N m hm x)

/-- Paper label: `thm:xi-coherence-affine-subcube`. -/
theorem paper_xi_coherence_affine_subcube
    (N m : ℕ) (hm : m ≤ N) (x : Fin N → Fin 4) :
    xi_coherence_affine_subcube_class_card N m hm x = 4 ^ (N - m) := by
  unfold xi_coherence_affine_subcube_class_card
  simpa [Fintype.card_fun] using
    Fintype.card_congr (xi_coherence_affine_subcube_suffixEquiv N m hm x)

end Omega.Zeta

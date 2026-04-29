import Omega.GroupUnification.GroupJGFoldPrimeEllipseTriple

namespace Omega.Zeta

/-- The composed fold, squarefree-prime-register, and ellipse-axis encoding. -/
noncomputable def xi_fold_loss_prime_ellipse_triple_correspondence_encoding (m : Nat) :
    Omega.GroupUnification.FoldOmega m → Fin (m + 1) × Bool × ℝ :=
  fun omega =>
    (omega.base, omega.hidden,
      Omega.GroupUnification.groupJGEllipseAxis
        (Omega.GroupUnification.foldSquarefreeToPrimeRegister omega.choices))

/-- Concrete statement: the composed fold-squarefree-ellipse encoding is injective. -/
def xi_fold_loss_prime_ellipse_triple_correspondence_statement : Prop :=
  ∀ m : Nat, Function.Injective
    (xi_fold_loss_prime_ellipse_triple_correspondence_encoding m)

/-- Paper-facing wrapper for the fold-loss prime ellipse triple correspondence.
    cor:xi-fold-loss-prime-ellipse-triple-correspondence -/
theorem paper_xi_fold_loss_prime_ellipse_triple_correspondence :
    xi_fold_loss_prime_ellipse_triple_correspondence_statement := by
  intro m
  simpa [xi_fold_loss_prime_ellipse_triple_correspondence_encoding] using
    Omega.GroupUnification.paper_group_jg_fold_prime_ellipse_triple m

end Omega.Zeta

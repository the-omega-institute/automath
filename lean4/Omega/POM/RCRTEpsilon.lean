import Mathlib.Tactic
import Omega.POM.OrderSpatialization

namespace Omega.POM

/-- The chapter-local deterministic envelope `d_m(X)` controlling the order-projection register. -/
def pomResidualBudget (m : ℕ) (X : ℤ) : ℤ :=
  m + |X|

/-- The bad event in the `(\mathrm{RCRT}_\varepsilon)` certificate: the hidden integer leaves the
hard-threshold window `[-B, B]`. -/
def pomRCRTBadEvent (Y : ℤ) (B : ℕ) : Prop :=
  (B : ℤ) < |Y|

/-- Indicator mass for the bad event, used as the explicit failure-probability proxy. -/
noncomputable def pomBadEventMass (Y : ℤ) (B : ℕ) : ℝ := by
  classical
  exact if pomRCRTBadEvent Y B then 1 else 0

/-- A concrete `\varepsilon`-sound rewrite certificate records the tail bound, the domination of
the bad event by the budget envelope `d_m(X)`, and exact CRT reconstruction on the good event. -/
def pomEpsSoundRewriteCertificate
    (m : ℕ) (eps : ℝ) (X Y : ℤ) (B P : ℕ) (reconstruct : ℤ → ℤ) : Prop :=
  pomBadEventMass Y B ≤ eps ∧
    (pomRCRTBadEvent Y B → (B : ℤ) < pomResidualBudget m X) ∧
    (¬ pomRCRTBadEvent Y B → reconstruct (Y % P) = Y)

/-- Paper: `prop:pom-rcrt-epsilon`.
If the hidden order label is dominated by the deterministic budget `d_m(X)`, the tail indicator of
the bad event is at most `ε`, and the hard-threshold CRT reconstruction is exact on `[-B, B]`,
then one obtains an `ε`-sound rewrite certificate for the order projection. -/
theorem paper_pom_rcrt_epsilon :
    ∀ {m : Nat} {eps : Real}, 0 < eps → eps < 1 →
      ∀ {X Y : ℤ} {B P : ℕ} (reconstruct : ℤ → ℤ),
        |Y| ≤ pomResidualBudget m X →
        pomBadEventMass Y B ≤ eps →
        P > 2 * B →
        (∀ {z : ℤ}, |z| ≤ B → reconstruct (z % P) = z) →
        pomEpsSoundRewriteCertificate m eps X Y B P reconstruct := by
  intro m eps heps hlt X Y B P reconstruct hdom htail hP hrec
  let _ := hP
  refine ⟨htail, ?_, ?_⟩
  · intro hbad
    exact lt_of_lt_of_le hbad hdom
  · intro hgood
    have hY : |Y| ≤ B := by
      exact le_of_not_gt hgood
    exact hrec hY

end Omega.POM

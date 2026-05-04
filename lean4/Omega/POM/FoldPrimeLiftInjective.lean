import Mathlib.Tactic

/-- Paper-facing replay/recover formulation of prime-register lift injectivity.
    prop:pom-fold-prime-lift-injective -/
theorem paper_pom_fold_prime_lift_injective {Omega X E Cfg : Type*} (Fold : Omega → X)
    (embed : Omega → Cfg) (normal : X → Cfg) (events : Omega → List E)
    (replayInv : Cfg → List E → Cfg) (recover : Cfg → Omega)
    (h_replay : ∀ w, replayInv (normal (Fold w)) (events w).reverse = embed w)
    (h_recover : ∀ w, recover (embed w) = w) :
    Function.Injective (fun w => (Fold w, events w)) := by
  intro w₁ w₂ h
  have hFold : Fold w₁ = Fold w₂ := congrArg Prod.fst h
  have hEvents : events w₁ = events w₂ := congrArg Prod.snd h
  calc
    w₁ = recover (embed w₁) := (h_recover w₁).symm
    _ = recover (replayInv (normal (Fold w₁)) (events w₁).reverse) := by
      rw [h_replay w₁]
    _ = recover (replayInv (normal (Fold w₂)) (events w₂).reverse) := by
      rw [hFold, hEvents]
    _ = recover (embed w₂) := by
      rw [h_replay w₂]
    _ = w₂ := h_recover w₂

import Mathlib.Data.Set.Function
import Omega.LogicExpansionChain.ChoiceSpectrum

namespace Omega.LogicExpansionChain

section ChoiceSpectrumSymmetryInvariance

variable {Observer State Action Formula : Type}
variable (Enabled : Observer → State → Set Action)
variable (Upd : Observer → Action → State → Set State)
variable (Forces : Observer → State → Formula → Prop)
variable (σI : Observer ≃ Observer) (σP : State ≃ State)
variable
  (hEnabled : ∀ {i : Observer} {p : State} {α : Action},
    α ∈ Enabled i p ↔ α ∈ Enabled (σI i) (σP p))
variable
  (hUpd : ∀ {i : Observer} {p q : State} {α : Action},
    q ∈ Upd i α p ↔ σP q ∈ Upd (σI i) α (σP p))
variable
  (hForces : ∀ (i : Observer) (q : State) (φ : Formula),
    Forces i q φ ↔ Forces (σI i) (σP q) φ)

include hEnabled hUpd hForces

private def transportOneStepFuture (i : Observer) (p : State) :
    OneStepFuture Enabled Upd i p →
      OneStepFuture Enabled Upd (σI i) (σP p)
  | ⟨q, hq⟩ =>
      ⟨σP q, by
        rcases hq with ⟨α, hα, hqα⟩
        exact ⟨α,
          (hEnabled (i := i) (p := p) (α := α)).mp hα,
          (hUpd (i := i) (p := p) (q := q) (α := α)).mp hqα⟩⟩

private def transportOneStepFutureSymm (i : Observer) (p : State) :
    OneStepFuture Enabled Upd (σI i) (σP p) →
      OneStepFuture Enabled Upd i p
  | ⟨q, hq⟩ =>
      ⟨σP.symm q, by
        rcases hq with ⟨α, hα, hqα⟩
        refine ⟨α, ?_, ?_⟩
        · exact (hEnabled (i := i) (p := p) (α := α)).mpr hα
        · exact (hUpd (i := i) (p := p) (q := σP.symm q) (α := α)).mpr (by
            simpa using hqα)⟩

private theorem transportOneStepFuture_respects
    {i : Observer} {p : State}
    {q r : OneStepFuture Enabled Upd i p}
    (hqr : FutureEquivalent Enabled Upd Forces i p q r) :
    FutureEquivalent Enabled Upd Forces (σI i) (σP p)
      (transportOneStepFuture Enabled Upd σI σP hEnabled hUpd i p q)
      (transportOneStepFuture Enabled Upd σI σP hEnabled hUpd i p r) := by
  intro φ
  exact (hForces i q.1 φ).symm.trans ((hqr φ).trans (hForces i r.1 φ))

private theorem transportOneStepFutureSymm_respects
    {i : Observer} {p : State}
    {q r : OneStepFuture Enabled Upd (σI i) (σP p)}
    (hqr : FutureEquivalent Enabled Upd Forces (σI i) (σP p) q r) :
    FutureEquivalent Enabled Upd Forces i p
      (transportOneStepFutureSymm Enabled Upd σI σP hEnabled hUpd i p q)
      (transportOneStepFutureSymm Enabled Upd σI σP hEnabled hUpd i p r) := by
  intro φ
  have hq :
      Forces i (σP.symm q.1) φ ↔ Forces (σI i) q.1 φ := by
    simpa using hForces i (σP.symm q.1) φ
  have hr :
      Forces i (σP.symm r.1) φ ↔ Forces (σI i) r.1 φ := by
    simpa using hForces i (σP.symm r.1) φ
  exact hq.trans ((hqr φ).trans hr.symm)

private theorem transportOneStepFuture_left_inv
    {i : Observer} {p : State} :
    Function.LeftInverse
      (transportOneStepFutureSymm Enabled Upd σI σP hEnabled hUpd i p)
      (transportOneStepFuture Enabled Upd σI σP hEnabled hUpd i p) := by
  intro q
  cases q with
  | mk q hq =>
      apply Subtype.ext
      simp [transportOneStepFuture, transportOneStepFutureSymm]

private theorem transportOneStepFuture_right_inv
    {i : Observer} {p : State} :
    Function.RightInverse
      (transportOneStepFutureSymm Enabled Upd σI σP hEnabled hUpd i p)
      (transportOneStepFuture Enabled Upd σI σP hEnabled hUpd i p) := by
  intro q
  cases q with
  | mk q hq =>
      apply Subtype.ext
      simp [transportOneStepFuture, transportOneStepFutureSymm]

private def futureClassEquiv (i : Observer) (p : State) :
    FutureClass Enabled Upd Forces i p ≃
      FutureClass Enabled Upd Forces (σI i) (σP p) where
  toFun :=
    Quotient.map
      (transportOneStepFuture Enabled Upd σI σP hEnabled hUpd i p)
      (fun _ _ h =>
        transportOneStepFuture_respects
          Enabled Upd Forces σI σP hEnabled hUpd hForces h)
  invFun :=
    Quotient.map
      (transportOneStepFutureSymm Enabled Upd σI σP hEnabled hUpd i p)
      (fun _ _ h =>
        transportOneStepFutureSymm_respects
          Enabled Upd Forces σI σP hEnabled hUpd hForces h)
  left_inv := by
    intro w
    refine Quotient.inductionOn w ?_
    intro q
    simpa using congrArg
      (Quotient.mk (futureSetoid Enabled Upd Forces i p))
      (transportOneStepFuture_left_inv
        (Enabled := Enabled) (Upd := Upd) (Forces := Forces)
        (σI := σI) (σP := σP)
        (hEnabled := hEnabled) (hUpd := hUpd) (hForces := hForces)
        (i := i) (p := p) q)
  right_inv := by
    intro w
    refine Quotient.inductionOn w ?_
    intro q
    simpa using congrArg
      (Quotient.mk (futureSetoid Enabled Upd Forces (σI i) (σP p)))
      (transportOneStepFuture_right_inv
        (Enabled := Enabled) (Upd := Upd) (Forces := Forces)
        (σI := σI) (σP := σP)
        (hEnabled := hEnabled) (hUpd := hUpd) (hForces := hForces)
        (i := i) (p := p) q)

private def transportEnabledAction (i : Observer) (p : State) :
    EnabledAction Enabled i p →
      EnabledAction Enabled (σI i) (σP p)
  | ⟨α, hα⟩ => ⟨α, (hEnabled (i := i) (p := p) (α := α)).mp hα⟩

private def transportEnabledActionSymm (i : Observer) (p : State) :
    EnabledAction Enabled (σI i) (σP p) →
      EnabledAction Enabled i p
  | ⟨α, hα⟩ => ⟨α, (hEnabled (i := i) (p := p) (α := α)).mpr hα⟩

private theorem transportEnabledAction_left_inv
    {i : Observer} {p : State} :
    Function.LeftInverse
      (transportEnabledActionSymm Enabled σI σP hEnabled i p)
      (transportEnabledAction Enabled σI σP hEnabled i p) := by
  intro α
  cases α
  rfl

private theorem transportEnabledAction_right_inv
    {i : Observer} {p : State} :
    Function.RightInverse
      (transportEnabledActionSymm Enabled σI σP hEnabled i p)
      (transportEnabledAction Enabled σI σP hEnabled i p) := by
  intro α
  cases α
  rfl

private theorem futureImage_transport
    {i : Observer} {p : State} (α : EnabledAction Enabled i p) :
    futureImage Enabled Upd Forces (σI i) (σP p)
        (transportEnabledAction Enabled σI σP hEnabled i p α) =
      Set.image
        (futureClassEquiv Enabled Upd Forces σI σP hEnabled hUpd hForces i p)
        (futureImage Enabled Upd Forces i p α) := by
  ext w
  constructor
  · intro hw
    rcases hw with ⟨q, hq, rfl⟩
    have hq' : σP.symm q ∈ Upd i α.1 p := by
      exact (hUpd (i := i) (p := p) (q := σP.symm q) (α := α.1)).mpr (by
        simpa using hq)
    refine ⟨Quotient.mk (futureSetoid Enabled Upd Forces i p)
      ⟨σP.symm q, ⟨α.1, α.2, hq'⟩⟩, ?_, ?_⟩
    · exact ⟨σP.symm q, hq', rfl⟩
    · change
        Quotient.mk (futureSetoid Enabled Upd Forces (σI i) (σP p))
            (transportOneStepFuture Enabled Upd σI σP hEnabled hUpd i p
              ⟨σP.symm q, ⟨α.1, α.2, hq'⟩⟩) =
          Quotient.mk (futureSetoid Enabled Upd Forces (σI i) (σP p))
            ⟨q, ⟨α.1, (transportEnabledAction Enabled σI σP hEnabled i p α).2, hq⟩⟩
      apply Quotient.sound
      intro φ
      simpa [transportOneStepFuture]
  · intro hw
    rcases hw with ⟨w', hw', rfl⟩
    rcases hw' with ⟨q, hq, rfl⟩
    refine ⟨σP q, (hUpd (i := i) (p := p) (q := q) (α := α.1)).mp hq, ?_⟩
    change
      Quotient.mk (futureSetoid Enabled Upd Forces (σI i) (σP p))
          (transportOneStepFuture Enabled Upd σI σP hEnabled hUpd i p
            ⟨q, ⟨α.1, α.2, hq⟩⟩) =
        Quotient.mk (futureSetoid Enabled Upd Forces (σI i) (σP p))
          ⟨σP q, ⟨α.1, (transportEnabledAction Enabled σI σP hEnabled i p α).2,
            (hUpd (i := i) (p := p) (q := q) (α := α.1)).mp hq⟩⟩
    apply Quotient.sound
    intro φ
    simpa [transportOneStepFuture]

private theorem futureImage_transport_symm
    {i : Observer} {p : State}
    (α : EnabledAction Enabled (σI i) (σP p)) :
    futureImage Enabled Upd Forces i p
        (transportEnabledActionSymm Enabled σI σP hEnabled i p α) =
      Set.image
        (futureClassEquiv Enabled Upd Forces σI σP hEnabled hUpd hForces i p).symm
        (futureImage Enabled Upd Forces (σI i) (σP p) α) := by
  ext w
  constructor
  · intro hw
    rcases hw with ⟨q, hq, rfl⟩
    have hq' : σP q ∈ Upd (σI i) α.1 (σP p) := by
      exact (hUpd (i := i) (p := p) (q := q) (α := α.1)).mp hq
    refine ⟨Quotient.mk (futureSetoid Enabled Upd Forces (σI i) (σP p))
      ⟨σP q, ⟨α.1, α.2, hq'⟩⟩, ?_, ?_⟩
    · exact ⟨σP q, hq', rfl⟩
    · change
        Quotient.mk (futureSetoid Enabled Upd Forces i p)
            (transportOneStepFutureSymm Enabled Upd σI σP hEnabled hUpd i p
              ⟨σP q, ⟨α.1, α.2, hq'⟩⟩) =
          Quotient.mk (futureSetoid Enabled Upd Forces i p)
            ⟨q, ⟨α.1, (transportEnabledActionSymm Enabled σI σP hEnabled i p α).2, hq⟩⟩
      apply Quotient.sound
      intro φ
      simpa [transportOneStepFutureSymm]
  · intro hw
    rcases hw with ⟨w', hw', rfl⟩
    rcases hw' with ⟨q, hq, rfl⟩
    have hq' : σP.symm q ∈ Upd i α.1 p := by
      exact (hUpd (i := i) (p := p) (q := σP.symm q) (α := α.1)).mpr (by
        simpa using hq)
    refine ⟨σP.symm q, hq', ?_⟩
    change
      Quotient.mk (futureSetoid Enabled Upd Forces i p)
          (transportOneStepFutureSymm Enabled Upd σI σP hEnabled hUpd i p
            ⟨q, ⟨α.1, α.2, hq⟩⟩) =
        Quotient.mk (futureSetoid Enabled Upd Forces i p)
          ⟨σP.symm q, ⟨α.1, (transportEnabledActionSymm Enabled σI σP hEnabled i p α).2,
            hq'⟩⟩
    apply Quotient.sound
    intro φ
    simpa [transportOneStepFutureSymm]

private theorem transportEnabledAction_respects
    {i : Observer} {p : State}
    {α β : EnabledAction Enabled i p}
    (hαβ : ActionEquivalent Enabled Upd Forces i p α β) :
    ActionEquivalent Enabled Upd Forces (σI i) (σP p)
      (transportEnabledAction Enabled σI σP hEnabled i p α)
      (transportEnabledAction Enabled σI σP hEnabled i p β) := by
  calc
    futureImage Enabled Upd Forces (σI i) (σP p)
        (transportEnabledAction Enabled σI σP hEnabled i p α) =
      Set.image
        (futureClassEquiv Enabled Upd Forces σI σP hEnabled hUpd hForces i p)
        (futureImage Enabled Upd Forces i p α) :=
      futureImage_transport
        Enabled Upd Forces σI σP hEnabled hUpd hForces α
    _ =
      Set.image
        (futureClassEquiv Enabled Upd Forces σI σP hEnabled hUpd hForces i p)
        (futureImage Enabled Upd Forces i p β) := by
      rw [hαβ]
    _ =
      futureImage Enabled Upd Forces (σI i) (σP p)
        (transportEnabledAction Enabled σI σP hEnabled i p β) := by
      symm
      exact futureImage_transport
        Enabled Upd Forces σI σP hEnabled hUpd hForces β

private theorem transportEnabledActionSymm_respects
    {i : Observer} {p : State}
    {α β : EnabledAction Enabled (σI i) (σP p)}
    (hαβ : ActionEquivalent Enabled Upd Forces (σI i) (σP p) α β) :
    ActionEquivalent Enabled Upd Forces i p
      (transportEnabledActionSymm Enabled σI σP hEnabled i p α)
      (transportEnabledActionSymm Enabled σI σP hEnabled i p β) := by
  calc
    futureImage Enabled Upd Forces i p
        (transportEnabledActionSymm Enabled σI σP hEnabled i p α) =
      Set.image
        (futureClassEquiv Enabled Upd Forces σI σP hEnabled hUpd hForces i p).symm
        (futureImage Enabled Upd Forces (σI i) (σP p) α) :=
      futureImage_transport_symm
        Enabled Upd Forces σI σP hEnabled hUpd hForces α
    _ =
      Set.image
        (futureClassEquiv Enabled Upd Forces σI σP hEnabled hUpd hForces i p).symm
        (futureImage Enabled Upd Forces (σI i) (σP p) β) := by
      rw [hαβ]
    _ =
      futureImage Enabled Upd Forces i p
        (transportEnabledActionSymm Enabled σI σP hEnabled i p β) := by
      symm
      exact futureImage_transport_symm
        Enabled Upd Forces σI σP hEnabled hUpd hForces β

private def actionClassEquiv (i : Observer) (p : State) :
    ActionClass Enabled Upd Forces i p ≃
      ActionClass Enabled Upd Forces (σI i) (σP p) where
  toFun :=
    Quotient.map
      (transportEnabledAction Enabled σI σP hEnabled i p)
      (fun _ _ h =>
        transportEnabledAction_respects
          Enabled Upd Forces σI σP hEnabled hUpd hForces h)
  invFun :=
    Quotient.map
      (transportEnabledActionSymm Enabled σI σP hEnabled i p)
      (fun _ _ h =>
        transportEnabledActionSymm_respects
          Enabled Upd Forces σI σP hEnabled hUpd hForces h)
  left_inv := by
    intro w
    refine Quotient.inductionOn w ?_
    intro α
    simpa using congrArg
      (Quotient.mk (actionSetoid Enabled Upd Forces i p))
      (transportEnabledAction_left_inv
        (Enabled := Enabled) (Upd := Upd) (Forces := Forces)
        (σI := σI) (σP := σP)
        (hEnabled := hEnabled) (hUpd := hUpd) (hForces := hForces)
        (i := i) (p := p) α)
  right_inv := by
    intro w
    refine Quotient.inductionOn w ?_
    intro α
    simpa using congrArg
      (Quotient.mk (actionSetoid Enabled Upd Forces (σI i) (σP p)))
      (transportEnabledAction_right_inv
        (Enabled := Enabled) (Upd := Upd) (Forces := Forces)
        (σI := σI) (σP := σP)
        (hEnabled := hEnabled) (hUpd := hUpd) (hForces := hForces)
        (i := i) (p := p) α)

omit hEnabled hUpd hForces in
set_option maxHeartbeats 400000 in
/-- Paper-facing symmetry invariance for the quotient-based one-step future and action spectra.
    thm:logic-expansion-choice-spectrum-symmetry-invariance -/
theorem paper_logic_expansion_choice_spectrum_symmetry_invariance
    {Observer State Action Formula : Type}
    (Enabled : Observer → State → Set Action)
    (Upd : Observer → Action → State → Set State)
    (Forces : Observer → State → Formula → Prop)
    (σI : Observer ≃ Observer) (σP : State ≃ State)
    (hEnabled : ∀ {i : Observer} {p : State} {α : Action},
      α ∈ Enabled i p ↔ α ∈ Enabled (σI i) (σP p))
    (hUpd : ∀ {i : Observer} {p q : State} {α : Action},
      q ∈ Upd i α p ↔ σP q ∈ Upd (σI i) α (σP p))
    (hForces : ∀ (i : Observer) (q : State) (φ : Formula),
      Forces i q φ ↔ Forces (σI i) (σP q) φ)
    (i : Observer) (p : State) :
    Nonempty ((Omega.LogicExpansionChain.FutureClass Enabled Upd Forces i p) ≃
      (Omega.LogicExpansionChain.FutureClass Enabled Upd Forces (σI i) (σP p))) ∧
      Nonempty ((Omega.LogicExpansionChain.ActionClass Enabled Upd Forces i p) ≃
        (Omega.LogicExpansionChain.ActionClass Enabled Upd Forces (σI i) (σP p))) := by
  exact ⟨⟨futureClassEquiv Enabled Upd Forces σI σP hEnabled hUpd hForces i p⟩,
    ⟨actionClassEquiv Enabled Upd Forces σI σP hEnabled hUpd hForces i p⟩⟩

end ChoiceSpectrumSymmetryInvariance

end Omega.LogicExpansionChain

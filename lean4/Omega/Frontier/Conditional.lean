import Omega.Frontier.Certificates
import Omega.Graph.Sofic
import Omega.SPG.Clopen
import Omega.SPG.ScanErrorMeasure

namespace Omega.Frontier

noncomputable section

/-- The realization map from finite witnesses to their projected defect patterns. -/
def defectRealizationMap (m : Nat) : (Σ k : Nat, Word (m + k)) → Word m
  | ⟨k, ω⟩ => globalDefect (Nat.le_add_right m k) ω

theorem fullGeneration_surjective (m : Nat) (h : FullGeneration m) :
    Function.Surjective (defectRealizationMap m) := by
  intro d
  rcases h d with ⟨k, ω, hω⟩
  exact ⟨⟨k, ω⟩, hω⟩

theorem uniformGap_bounds (h : UniformGap) :
    0 < h.η ∧ h.η < 1 :=
  ⟨h.η_pos, h.η_lt_one⟩

theorem defectBudget_has_bound (m k : Nat) (h : DefectBudget m) :
    ∃ C : Nat, C ≤ m + k :=
  h k

theorem globalFullGeneration_specializes (h : GlobalFullGeneration) (m : Nat) :
    FullGeneration m :=
  h m

theorem globalDefectBudget_specializes (h : GlobalDefectBudget) (m : Nat) :
    DefectBudget m :=
  h m

/-- A canonical certified realization supplied by the full-generation hypothesis. -/
noncomputable def generatedDefectCertificate (m : Nat) (h : FullGeneration m) (d : Word m) :
    DefectCertificate :=
  let k := Classical.choose (h d)
  let hk := Classical.choose_spec (h d)
  let ω := Classical.choose hk
  { m := m, k := k, input := ω, claimed := d }

@[simp] theorem generatedDefectCertificate_claimed (m : Nat) (h : FullGeneration m) (d : Word m) :
    (generatedDefectCertificate m h d).claimed = d := rfl

theorem generatedDefectCertificate_valid (m : Nat) (h : FullGeneration m) (d : Word m) :
    (generatedDefectCertificate m h d).Valid := by
  dsimp [generatedDefectCertificate, DefectCertificate.Valid]
  let k := Classical.choose (h d)
  let hk := Classical.choose_spec (h d)
  let ω := Classical.choose hk
  let hω := Classical.choose_spec hk
  simpa [k, hk, ω] using hω

/-- cond:full-generation-certifies -/
theorem fullGeneration_certifies (m : Nat) (h : FullGeneration m) (d : Word m) :
    (generatedDefectCertificate m h d).Valid :=
  generatedDefectCertificate_valid m h d

/-- Any concrete local defect claim carries a canonical valid certificate.
    cond:local-defect-certificate -/
theorem localDefect_hasCertificate (η : Word (m + 1)) :
    LocalDefectCertificate.Valid { m := m, input := η, claimed := localDefect η } :=
  rfl

/-- Any concrete global defect claim carries a canonical valid certificate.
    cond:global-defect-certificate -/
theorem globalDefect_hasCertificate (m k : Nat) (ω : Word (m + k)) :
    DefectCertificate.Valid
      ({ m := m, k := k, input := ω
       , claimed := globalDefect (Nat.le_add_right m k) ω } : DefectCertificate) :=
  rfl

/-- Any one-step rewrite witness is already a valid rewrite-step certificate.
    cond:rewrite-step-certificate -/
theorem rewriteStep_hasCertificate {a b : Rewrite.DigitCfg} (h : Rewrite.Step a b) :
    RewriteStepCertificate.Valid { source := a, target := b } :=
  h

/-- Stable words yield canonical irreducibility certificates for their rewrite embeddings.
    cond:stable-irreducible-certificate -/
theorem stableIrreducible_hasCertificate (x : X m) :
    RewriteIrreducibleCertificate.Valid { source := Rewrite.iota x.1 } :=
  Rewrite.irreducible_iota_of_stable x

/-- Any folded image carries a canonical valid fold certificate.
    cond:fold-certificate -/
theorem fold_hasCertificate (w : Word m) :
    FoldCertificate.Valid { m := m, input := w, claimed := Fold w } :=
  rfl

/-- Observable events carry canonical zero-scan certificates in the discrete model.
    cond:observable-zero-scan-certificate -/
theorem observableZeroScan_hasCertificate {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (A : Set β) :
    ObservableZeroScanCertificate.Valid { μ := μ, obs := obs, event := A } :=
  ObservableZeroScanCertificate.canonical μ obs A

/-- Any discrete scan-error claim has a canonical exact-value certificate.
    cond:scan-error-certificate -/
theorem scanError_hasCertificate {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    ScanErrorCertificate.Valid
      ({ μ := μ, obs := obs, event := P
       , claimed := SPG.scanError μ obs P } : ScanErrorCertificate α β) :=
  rfl

/-- Any prefix scan-error claim has a canonical exact-value certificate.
    cond:prefix-scan-error-certificate -/
theorem prefixScanError_hasCertificate {m n : Nat}
    (μ : PMF (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    PrefixScanErrorCertificate.Valid
      ({ m := m, n := n, h := h, μ := μ, event := P
       , claimed := SPG.prefixScanError μ h P } : PrefixScanErrorCertificate) :=
  rfl

/-- Canonical full-generation certificates are sound.
    cond:generated-defect-certificate-sound -/
theorem generatedDefectCertificate_sound (m : Nat) (h : FullGeneration m) (d : Word m) :
    globalDefect (Nat.le_add_right m (generatedDefectCertificate m h d).k)
        (generatedDefectCertificate m h d).input
      = d := by
  simpa [generatedDefectCertificate_claimed] using
    (generatedDefectCertificate m h d).sound (generatedDefectCertificate_valid m h d)

/-- Canonical rewrite-step certificates preserve the represented value.
    cond:rewrite-step-certificate-value -/
theorem rewriteStep_certificate_value {a b : Rewrite.DigitCfg} (h : Rewrite.Step a b) :
  Rewrite.value b = Rewrite.value a :=
  RewriteStepCertificate.value_preserved { source := a, target := b } h

/-- Canonical fold certificates are idempotent on their claimed stable image.
    cond:fold-certificate-idempotent -/
theorem foldCertificate_idempotent (w : Word m) :
    Fold (Fold w).1 = Fold w :=
  FoldCertificate.idempotent { m := m, input := w, claimed := Fold w } (fold_hasCertificate w)

/-- Canonical fold certificates place the source word inside the target fiber.
    cond:fold-certificate-in-fiber -/
theorem foldCertificate_inFiber (w : Word m) :
    w ∈ X.fiber (Fold w) :=
  FoldCertificate.inFiber { m := m, input := w, claimed := Fold w } (fold_hasCertificate w)

/-- Canonical discrete observable-event zero-scan certificates are sound.
    cond:observable-zero-scan-certificate-sound -/
theorem observableZeroScan_certificate_sound {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (A : Set β) :
    SPG.scanError μ obs (SPG.observableEvent obs A) = 0 :=
  ObservableZeroScanCertificate.sound { μ := μ, obs := obs, event := A }
    (observableZeroScan_hasCertificate μ obs A)

/-- Canonical prefix zero-scan certificates are sound.
    cond:prefix-zero-scan-certificate-sound -/
theorem prefixZeroScan_certificate_sound {m n : Nat}
    (μ : PMF (Word n)) (h : m ≤ n) (A : Set (Word m)) :
    SPG.prefixScanError μ h (SPG.prefixEvent h A) = 0 :=
  PrefixZeroScanCertificate.sound { m := m, n := n, h := h, μ := μ, event := A }
    (PrefixZeroScanCertificate.canonical μ h A)

/-- Exact scan-error certificates are sound by construction.
    cond:scan-error-certificate-sound -/
theorem scanError_certificate_sound {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    SPG.scanError μ obs P = SPG.scanError μ obs P :=
  ScanErrorCertificate.sound
    ({ μ := μ, obs := obs, event := P
     , claimed := SPG.scanError μ obs P } : ScanErrorCertificate α β)
    (scanError_hasCertificate μ obs P)

/-- Exact prefix scan-error certificates are sound by construction.
    cond:prefix-scan-error-certificate-sound -/
theorem prefixScanError_certificate_sound {m n : Nat}
    (μ : PMF (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    SPG.prefixScanError μ h P = SPG.prefixScanError μ h P :=
  PrefixScanErrorCertificate.sound
    ({ m := m, n := n, h := h, μ := μ, event := P
     , claimed := SPG.prefixScanError μ h P } : PrefixScanErrorCertificate)
    (prefixScanError_hasCertificate μ h P)

/-- The finite folding map is idempotent on arbitrary raw words.
    cond:fold-idempotent -/
theorem fold_idempotent (w : Word m) :
    Fold (Fold w).1 = Fold w :=
  Omega.Fold_idempotent w

/-- Stable words are fixed points of the finite folding map.
    cond:fold-fixed-on-stable -/
theorem fold_fixedOnStable (x : X m) :
    Fold x.1 = x :=
  Omega.Fold_stable x

/-- The finite folding map is surjective onto the stable syntax space.
    cond:fold-surjective -/
theorem fold_surjective (m : Nat) :
    Function.Surjective (Fold (m := m)) :=
  Omega.Fold_surjective m

/-- Every stable target has a nonempty finite fiber under `Fold`.
    cond:fold-fiber-nonempty -/
theorem fold_fiber_nonempty (x : X m) :
    (X.fiber x).Nonempty :=
  X.fiber_nonempty x

/-- The finite fiber over a stable target admits canonical rank/unrank coordinates. -/
theorem fold_fiber_rank_unrank (x : X m) (i : Fin (X.fiber x).card) :
    X.rank x (X.unrank x i) = i :=
  X.rank_unrank x i

/-- Unranking a fiber index returns a raw word folding back to the target stable word.
    cond:fold-fiber-unrank-sound -/
theorem fold_fiber_unrank_sound (x : X m) (i : Fin (X.fiber x).card) :
    Fold (X.unrankWord x i) = x :=
  X.Fold_unrankWord x i

/-- Every stable target has a canonical chosen raw preimage.
    cond:fold-choose-preimage-sound -/
theorem fold_choosePreimage_sound (x : X m) :
    Fold (X.choosePreimage x) = x :=
  X.Fold_choosePreimage x

/-- The canonical chosen raw preimage lies in the target fiber.
    cond:fold-choose-preimage-in-fiber -/
theorem fold_choosePreimage_inFiber (x : X m) :
    X.choosePreimage x ∈ X.fiber x :=
  X.choosePreimage_mem_fiber x

/-- Ranking a known preimage and unranking it recovers the original raw word.
    cond:fold-unrank-rank-of-eq -/
theorem fold_unrank_rankOfEq (x : X m) (w : Word m) (h : Fold w = x) :
    X.unrankWord x (X.rankOfFoldEq x w h) = w :=
  X.unrankWord_rankOfFoldEq x w h

/-- Paper-facing order independence for finite folding windows.
    cond:fold-order-independence -/
theorem fold_orderIndependent {m : Nat} (w : Word m) {b : Rewrite.DigitCfg}
    (hab : Relation.ReflTransGen Rewrite.Step (Rewrite.iota w) b)
    (hIrr : Rewrite.Irreducible b) (hSup : Rewrite.SupportedBelow b m) :
    b = Rewrite.iota (Fold w).1 :=
  Rewrite.irreducible_terminal_eq_fold hab hIrr hSup

/-- Any two irreducible terminals reachable from the same configuration must agree.
    cond:rewrite-terminal-unique -/
theorem rewrite_terminal_unique {a b c : Rewrite.DigitCfg}
    (hab : Relation.ReflTransGen Rewrite.Step a b)
    (hac : Relation.ReflTransGen Rewrite.Step a c)
    (hIrrB : Rewrite.Irreducible b) (hIrrC : Rewrite.Irreducible c) :
    b = c :=
  Rewrite.irreducible_terminal_unique_unbounded hab hac hIrrB hIrrC

/-- The rewrite relation is strongly terminating.
    cond:rewrite-strong-termination -/
theorem rewrite_stronglyTerminating :
    WellFounded (flip Rewrite.Step) :=
  Rewrite.step_stronglyTerminating

/-- The rewrite relation is globally confluent.
    cond:rewrite-confluence -/
theorem rewrite_confluent {a b c : Rewrite.DigitCfg}
    (hab : Relation.ReflTransGen Rewrite.Step a b)
    (hac : Relation.ReflTransGen Rewrite.Step a c) :
    Relation.Join (Relation.ReflTransGen Rewrite.Step) b c :=
  Rewrite.step_confluent hab hac

/-- The rewrite relation is locally confluent.
    cond:rewrite-local-confluence -/
theorem rewrite_locallyConfluent {a b c : Rewrite.DigitCfg}
    (hab : Rewrite.Step a b) (hac : Rewrite.Step a c) :
    Relation.Join (Relation.ReflTransGen Rewrite.Step) b c :=
  Rewrite.step_locallyConfluent hab hac

/-- Rewrite descendants preserve the represented Fibonacci value.
    cond:rewrite-value-invariant -/
theorem rewrite_valueInvariant {a b : Rewrite.DigitCfg}
    (hab : Relation.ReflTransGen Rewrite.Step a b) :
    Rewrite.value b = Rewrite.value a :=
  Rewrite.reflTransGen_value hab

/-- Rewrite irreducibility is equivalent to being a stable digit configuration.
    cond:rewrite-irreducible-iff-stablecfg -/
theorem rewrite_irreducible_iff_stableCfg {a : Rewrite.DigitCfg} :
    Rewrite.Irreducible a ↔ Rewrite.StableCfg a :=
  Rewrite.irreducible_iff_stableCfg

/-- Two irreducible configurations with the same represented value must agree.
    cond:rewrite-irreducible-same-value-unique -/
theorem rewrite_irreducible_sameValue_unique {a b : Rewrite.DigitCfg}
    (hIrrA : Rewrite.Irreducible a) (hIrrB : Rewrite.Irreducible b)
    (hVal : Rewrite.value a = Rewrite.value b) :
    a = b :=
  Rewrite.irreducible_eq_of_value_eq hIrrA hIrrB hVal

/-- Folded stable embeddings are irreducible in the rewrite system.
    cond:rewrite-fold-irreducible -/
theorem rewrite_fold_irreducible (w : Word m) :
    Rewrite.Irreducible (Rewrite.iota (Fold w).1) :=
  Rewrite.irreducible_iota_Fold w

/-- Any configuration admits an irreducible descendant under the rewrite relation.
    cond:rewrite-terminal-exists -/
theorem rewrite_terminal_exists (a : Rewrite.DigitCfg) :
    ∃ b : Rewrite.DigitCfg, Relation.ReflTransGen Rewrite.Step a b ∧ Rewrite.Irreducible b :=
  Rewrite.exists_irreducible_descendant a

/-- Any irreducible terminal reached from a finite window agrees with the folded normal form.
    cond:rewrite-terminal-equals-fold -/
theorem rewrite_terminal_equals_fold {w : Word m} {b : Rewrite.DigitCfg}
    (hab : Relation.ReflTransGen Rewrite.Step (Rewrite.iota w) b)
    (hIrr : Rewrite.Irreducible b) (hSup : Rewrite.SupportedBelow b m) :
    b = Rewrite.iota (Fold w).1 :=
  Rewrite.irreducible_terminal_eq_fold hab hIrr hSup

/-- The inverse-limit presentation identifies compatible stable families with infinite stable words.
    cond:inverse-limit-presentation -/
def inverseLimitPresentation : X.CompatibleFamily ≃ X.XInfinity :=
  X.inverseLimitEquiv

/-- The inverse-limit presentation is exact on the compatible-family side. -/
theorem inverseLimitPresentation_left (F : X.CompatibleFamily) :
    inverseLimitPresentation.symm (inverseLimitPresentation F) = F :=
  X.inverseLimitEquiv.left_inv F

/-- The inverse-limit presentation is exact on the infinite-stable-word side. -/
theorem inverseLimitPresentation_right (a : X.XInfinity) :
    inverseLimitPresentation (inverseLimitPresentation.symm a) = a :=
  X.inverseLimitEquiv.right_inv a

/-- The one-step defect is the special case of the global defect at adjacent resolutions.
    cond:defect-local-as-global-step -/
theorem localDefect_as_globalStep (η : Word (m + 1)) :
    localDefect η = globalDefect (Nat.le_succ m) η :=
  localDefect_eq_globalDefect η

/-- Global defect satisfies the recursive xor-step identity.
    cond:defect-recursive-step -/
theorem globalDefect_recursive (h : m ≤ n) (ω : Word (n + 1)) :
    globalDefect (Nat.le_trans h (Nat.le_succ n)) ω
      = xorWord (restrictWord h (localDefect ω)) (globalDefect h (truncate ω)) :=
  globalDefect_step h ω

/-- Global defect is the xor-telescope of projected local defects.
    cond:defect-telescope -/
theorem defect_telescope (m k : Nat) (ω : Word (m + k)) :
    globalDefect (Nat.le_add_right m k) ω = defectChain m k ω :=
  globalDefect_eq_defectChain m k ω

/-- The stable finite language is presented by the explicit two-state golden-mean graph.
    cond:stable-language-sofic -/
theorem stableLanguage_sofic (w : Word m) :
    Omega.Graph.AcceptsWord Omega.Graph.goldenMeanGraph false w ↔ No11 w :=
  Omega.Graph.acceptsWord_goldenMean_iff_no11 w

/-- Any `No11` word is accepted by the explicit two-state golden-mean graph.
    cond:stable-implies-sofic -/
theorem stable_implies_sofic {w : Word m} (hNo11 : No11 w) :
    Omega.Graph.AcceptsWord Omega.Graph.goldenMeanGraph false w :=
  Omega.Graph.acceptsWord_goldenMean_of_no11 hNo11

/-- Any word accepted by the explicit two-state golden-mean graph is stable.
    cond:sofic-implies-stable -/
theorem sofic_implies_stable {w : Word m}
    (hAcc : Omega.Graph.AcceptsWord Omega.Graph.goldenMeanGraph false w) :
    No11 w :=
  Omega.Graph.no11_of_acceptsWord_goldenMean hAcc

/-- The stable length-`m` language equals the explicit golden-mean sofic language as a set.
    cond:stable-language-set-sofic -/
theorem stableLanguage_set_sofic (m : Nat) :
    {w : Word m | No11 w}
      = {w : Word m | Omega.Graph.AcceptsWord Omega.Graph.goldenMeanGraph false w} :=
  Omega.Graph.stableLanguage_eq_goldenMean m

/-- Stable syntax points are accepted by the explicit two-state golden-mean presentation.
    cond:stable-point-sofic -/
theorem stablePoint_sofic (x : X m) :
    Omega.Graph.AcceptsWord Omega.Graph.goldenMeanGraph false x.1 :=
  Omega.Graph.acceptsWord_of_stable x

/-- Prefix balls are exactly the cylinders cut out by the corresponding finite address.
    cond:prefix-ball-cylinder -/
theorem prefixBall_is_cylinder (x : SPG.OmegaInfinity) (m : Nat) :
    SPG.prefixBall x m = SPG.cylinderWord (SPG.prefixWord x m) :=
  SPG.prefixBall_eq_cylinderWord x m

/-- Cylinders are closed balls for the prefix ultrametric.
    cond:cylinder-closed-ball -/
theorem cylinder_is_closedBall (w : Word m) :
    SPG.cylinderWord w
      = {x : SPG.OmegaInfinity | SPG.prefixDist x (SPG.extendWord w) ≤ (1 / 2 : ℝ) ^ m} :=
  SPG.cylinderWord_eq_closedBall w

/-- Prefix balls are closed balls for the prefix ultrametric.
    cond:prefix-ball-closed-ball -/
theorem prefixBall_is_closedBall (x : SPG.OmegaInfinity) (m : Nat) :
    SPG.prefixBall x m = {y : SPG.OmegaInfinity | SPG.prefixDist y x ≤ (1 / 2 : ℝ) ^ m} :=
  SPG.prefixBall_eq_closedBall x m

/-- Finite-prefix events are clopen in the SPG symbolic topology.
    cond:prefix-event-decidable-clopen -/
theorem prefixEvent_decidableClopen (A : Set (Word m)) :
    IsClopen (SPG.fromWordSet A) :=
  SPG.spg_decidableClopen A

/-- Prefix-determined symbolic events are clopen.
    cond:prefix-determined-clopen -/
theorem prefixDetermined_clopen (s : Set SPG.OmegaInfinity) (m : Nat)
    (hs : SPG.PrefixDetermined s m) :
    IsClopen s :=
  SPG.prefixDetermined_isClopen m hs

/-- A symbolic event is prefix-determined exactly when it is cut out by some finite address set.
    cond:prefix-determined-from-wordset -/
theorem prefixDetermined_iff_fromWordSet (s : Set SPG.OmegaInfinity) (m : Nat) :
    SPG.PrefixDetermined s m ↔ ∃ A : Set (Word m), s = SPG.fromWordSet A :=
  SPG.prefixDetermined_iff_exists_fromWordSet s m

/-- Observable events have empty discrete scan-error boundary.
    cond:observable-event-boundary-empty-discrete -/
theorem observableEvent_boundaryEmpty_discrete {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (A : Set β) :
    SPG.boundaryCells μ obs (SPG.observableEvent obs A) = ∅ :=
  SPG.boundaryCells_observableEvent_eq_empty μ obs A

/-- Observable events have zero discrete scan error.
    cond:observable-event-zero-discrete -/
theorem observableEvent_zero_discrete {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (A : Set β) :
    SPG.scanError μ obs (SPG.observableEvent obs A) = 0 :=
  SPG.scanError_observableEvent_eq_zero μ obs A

/-- The discrete scan-error profile admits the exact boundary-cell decomposition.
    cond:scan-error-boundary-decomposition-discrete -/
theorem scanError_boundary_decomposition_discrete {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    SPG.scanError μ obs P
      = Finset.sum (SPG.boundaryCells μ obs P) (fun b =>
          min (SPG.cellEventMass μ obs P b) (SPG.cellComplMass μ obs P b)) :=
  SPG.scanError_eq_sum_boundary μ obs P

/-- The discrete scan-error profile is bounded by the total boundary-cell mass.
    cond:scan-error-boundary-mass-bound-discrete -/
theorem scanError_boundary_mass_bound_discrete {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    SPG.scanError μ obs P
      ≤ Finset.sum (SPG.boundaryCells μ obs P) (fun b =>
          SPG.cellMass μ obs b) :=
  SPG.scanError_le_boundaryMass μ obs P

/-- The discrete scan-error profile is bounded by a uniform cell-mass cap times boundary size.
    cond:scan-error-boundary-card-bound-discrete -/
theorem scanError_boundary_card_bound_discrete {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) (κ : ENNReal)
    (hκ : ∀ b, SPG.cellMass μ obs b ≤ κ) :
    SPG.scanError μ obs P ≤ (SPG.boundaryCells μ obs P).card * κ :=
  SPG.scanError_le_boundaryCard_mul μ obs P κ hκ

/-- Paper finite-boundary scaling wrapper for discrete scan error.
    thm:spg-clarity-volume-boundary-scaling -/
theorem paper_scanError_boundary_scaling {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) (θ κ_lower κ_upper : ENNReal)
    (hθ : ∀ b ∈ SPG.boundaryCells μ obs P,
      θ * SPG.cellMass μ obs b ≤
        min (SPG.cellEventMass μ obs P b) (SPG.cellComplMass μ obs P b))
    (hκ_lower : ∀ b ∈ SPG.boundaryCells μ obs P, κ_lower ≤ SPG.cellMass μ obs b)
    (hκ_upper : ∀ b, SPG.cellMass μ obs b ≤ κ_upper) :
    (SPG.boundaryCells μ obs P).card * (θ * κ_lower) ≤ SPG.scanError μ obs P ∧
      SPG.scanError μ obs P ≤ (SPG.boundaryCells μ obs P).card * κ_upper := by
  exact ⟨SPG.scanError_ge_boundaryCard_mul_lower μ obs P θ κ_lower hθ hκ_lower,
    SPG.scanError_le_boundaryCard_mul μ obs P κ_upper hκ_upper⟩

/-- Empty discrete boundary forces zero scan error.
    cond:scan-error-zero-boundary-empty-discrete -/
theorem scanError_zero_of_boundaryEmpty_discrete {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α)
    (hEmpty : SPG.boundaryCells μ obs P = ∅) :
    SPG.scanError μ obs P = 0 := by
  rw [scanError_boundary_decomposition_discrete, hEmpty]
  simp

/-- Observable events are observable-pure in the finite-observable measure model.
    cond:observable-event-observable-pure-measure -/
theorem observableEvent_observablePure_measure [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (A : Set β) :
    SPG.ObservablePureMeasure μ obs (SPG.observableEvent obs A) :=
  SPG.observablePureMeasure_observableEvent μ obs A

/-- Observable events have empty boundary in the finite-observable measure model.
    cond:observable-event-boundary-empty-measure -/
theorem observableEvent_boundaryEmpty_measure [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (A : Set β) :
    SPG.boundaryCellsMeasure μ obs (SPG.observableEvent obs A) = ∅ :=
  SPG.boundaryCellsMeasure_observableEvent_eq_empty μ obs A

/-- Observable events have zero scan error in the finite-observable measure model.
    cond:observable-event-zero-measure -/
theorem observableEvent_zero_measure [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (A : Set β) :
    SPG.scanErrorMeasure μ obs (SPG.observableEvent obs A) = 0 :=
  SPG.scanErrorMeasure_observableEvent_eq_zero μ obs A

/-- The measure scan-error profile admits the exact boundary-cell decomposition.
    cond:measure-boundary-decomposition -/
theorem scanError_measure_boundary_decomposition [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) :
    SPG.scanErrorMeasure μ obs P
      = Finset.sum (SPG.boundaryCellsMeasure μ obs P) (fun b =>
          min (SPG.cellEventMeasure μ obs P b) (SPG.cellComplMeasure μ obs P b)) :=
  SPG.scanErrorMeasure_eq_sum_boundary μ obs P

/-- The measure scan-error profile is bounded by the total boundary-cell mass.
    cond:measure-boundary-mass-bound -/
theorem scanError_measure_boundary_mass_bound [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) :
    SPG.scanErrorMeasure μ obs P
      ≤ Finset.sum (SPG.boundaryCellsMeasure μ obs P) (fun b =>
          SPG.cellMeasure μ obs b) :=
  SPG.scanErrorMeasure_le_boundaryMass μ obs P

/-- The measure scan-error profile is bounded by a uniform cell-mass cap times boundary size.
    cond:measure-boundary-card-bound -/
theorem scanError_measure_boundary_card_bound [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) (κ : ENNReal)
    (hκ : ∀ b, SPG.cellMeasure μ obs b ≤ κ) :
    SPG.scanErrorMeasure μ obs P ≤ (SPG.boundaryCellsMeasure μ obs P).card * κ :=
  SPG.scanErrorMeasure_le_boundaryCard_mul μ obs P κ hκ

/-- Empty boundary forces zero scan error in the finite-observable measure model.
    cond:measure-zero-boundary-empty -/
theorem scanError_zero_of_boundaryEmpty_measure [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α)
    (hEmpty : SPG.boundaryCellsMeasure μ obs P = ∅) :
    SPG.scanErrorMeasure μ obs P = 0 := by
  have hPure : SPG.ObservablePureMeasure μ obs P :=
    (SPG.observablePureMeasure_iff_boundaryCellsMeasure_eq_empty μ obs P).2 hEmpty
  exact SPG.scanErrorMeasure_eq_zero_of_observablePure μ obs P hPure

/-- The general measure scan-error profile reduces to the discrete one on finite PMFs.
    bridge:scan-measure-discrete -/
theorem scanError_measure_discrete_bridge {α β : Type*} [Fintype α] [Fintype β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    SPG.scanErrorMeasure μ.toMeasure obs P = SPG.scanError μ obs P :=
  SPG.scanErrorMeasure_toMeasure_eq_scanError μ obs P

/-- Observable events remain zero-error after passing from finite PMFs to measures.
    bridge:observable-event-measure-discrete-zero -/
theorem observableEvent_zero_measure_discrete_bridge {α β : Type*} [Fintype α] [Fintype β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : PMF α) (obs : α → β) (A : Set β) :
    SPG.scanErrorMeasure μ.toMeasure obs (SPG.observableEvent obs A) = 0 := by
  rw [scanError_measure_discrete_bridge μ obs]
  exact SPG.scanError_observableEvent_eq_zero μ obs A

/-- Prefix events are pure for the discrete scan-error profile.
    cond:prefix-event-pure-discrete -/
theorem prefixEvent_pure_discrete (μ : PMF (Word n)) (h : m ≤ n) (A : Set (Word m)) :
    SPG.prefixBoundaryCells μ h (SPG.prefixEvent h A) = ∅ ∧
      SPG.prefixScanError μ h (SPG.prefixEvent h A) = 0 := by
  exact ⟨SPG.prefixBoundaryCells_prefixEvent_eq_empty μ h A,
    SPG.prefixScanError_eq_zero_of_prefixEvent μ h A⟩

/-- Prefix events have empty discrete boundary at every finite resolution.
    cond:prefix-event-boundary-empty-discrete -/
theorem prefixEvent_boundaryEmpty_discrete (μ : PMF (Word n)) (h : m ≤ n) (A : Set (Word m)) :
    SPG.prefixBoundaryCells μ h (SPG.prefixEvent h A) = ∅ :=
  SPG.prefixBoundaryCells_prefixEvent_eq_empty μ h A

/-- Prefix events have zero discrete scan error at every finite resolution.
    cond:prefix-event-zero-discrete -/
theorem prefixEvent_zero_discrete (μ : PMF (Word n)) (h : m ≤ n) (A : Set (Word m)) :
    SPG.prefixScanError μ h (SPG.prefixEvent h A) = 0 :=
  SPG.prefixScanError_eq_zero_of_prefixEvent μ h A

/-- Empty prefix boundary forces zero discrete prefix scan error.
    cond:prefix-scan-error-zero-boundary-empty-discrete -/
theorem prefixScanError_zero_of_boundaryEmpty_discrete (μ : PMF (Word n)) (h : m ≤ n)
    (P : Set (Word n)) (hEmpty : SPG.prefixBoundaryCells μ h P = ∅) :
    SPG.prefixScanError μ h P = 0 := by
  rw [SPG.prefixScanError_eq_sum_boundary, hEmpty]
  simp

/-- Prefix events are pure for the finite-observable measure scan-error profile.
    cond:prefix-event-pure-measure -/
theorem prefixEvent_pure_measure [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (A : Set (Word m)) :
    SPG.prefixBoundaryCellsMeasure μ h (SPG.prefixEvent h A) = ∅ ∧
      SPG.prefixScanErrorMeasure μ h (SPG.prefixEvent h A) = 0 := by
  exact ⟨SPG.prefixBoundaryCellsMeasure_prefixEvent_eq_empty μ h A,
    SPG.prefixScanErrorMeasure_eq_zero_of_prefixEvent μ h A⟩

/-- Prefix events have empty measure-theoretic boundary at every finite resolution.
    cond:prefix-event-boundary-empty-measure -/
theorem prefixEvent_boundaryEmpty_measure [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (A : Set (Word m)) :
    SPG.prefixBoundaryCellsMeasure μ h (SPG.prefixEvent h A) = ∅ :=
  SPG.prefixBoundaryCellsMeasure_prefixEvent_eq_empty μ h A

/-- Prefix events have zero measure scan error at every finite resolution.
    cond:prefix-event-zero-measure -/
theorem prefixEvent_zero_measure [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (A : Set (Word m)) :
    SPG.prefixScanErrorMeasure μ h (SPG.prefixEvent h A) = 0 :=
  SPG.prefixScanErrorMeasure_eq_zero_of_prefixEvent μ h A

/-- Empty prefix boundary forces zero measure prefix scan error.
    cond:prefix-measure-zero-boundary-empty -/
theorem prefixScanError_zero_of_boundaryEmpty_measure [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (P : Set (Word n))
    (hEmpty : SPG.prefixBoundaryCellsMeasure μ h P = ∅) :
    SPG.prefixScanErrorMeasure μ h P = 0 := by
  have hPure : SPG.ObservablePureMeasure μ (SPG.prefixObservation h) P :=
    (SPG.observablePureMeasure_iff_boundaryCellsMeasure_eq_empty μ (SPG.prefixObservation h) P).2 hEmpty
  exact SPG.prefixScanErrorMeasure_eq_zero_of_observablePure μ h P hPure

/-- Prefix events are observable-pure in the measure scan-error model.
    cond:prefix-event-observable-pure-measure -/
theorem prefixEvent_observablePure_measure [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (A : Set (Word m)) :
    SPG.ObservablePureMeasure μ (SPG.prefixObservation h) (SPG.prefixEvent h A) :=
  SPG.prefixObservablePureMeasure_prefixEvent μ h A

/-- Observable purity is equivalent to having no boundary cells in the finite-observable measure model.
    cond:observable-pure-iff-boundary-empty-measure -/
theorem observablePure_iff_boundaryEmpty_measure [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) :
    SPG.ObservablePureMeasure μ obs P ↔ SPG.boundaryCellsMeasure μ obs P = ∅ :=
  SPG.observablePureMeasure_iff_boundaryCellsMeasure_eq_empty μ obs P

/-- Zero scan error is equivalent to observable purity in the finite-observable measure model.
    cond:measure-zero-iff-observable-pure -/
theorem scanError_zero_iff_observablePure_measure [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) :
    SPG.scanErrorMeasure μ obs P = 0 ↔ SPG.ObservablePureMeasure μ obs P :=
  SPG.scanErrorMeasure_eq_zero_iff_observablePure μ obs P

/-- Zero scan error is equivalent to having empty boundary in the finite-observable measure model.
    cond:measure-zero-iff-boundary-empty -/
theorem scanError_zero_iff_boundaryEmpty_measure [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) :
    SPG.scanErrorMeasure μ obs P = 0 ↔ SPG.boundaryCellsMeasure μ obs P = ∅ :=
  SPG.scanErrorMeasure_eq_zero_iff_boundaryCellsMeasure_eq_empty μ obs P

/-- Prefix-observable purity is equivalent to an empty prefix boundary.
    cond:prefix-observable-pure-iff-boundary-empty-measure -/
theorem prefixObservablePure_iff_boundaryEmpty_measure [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    SPG.ObservablePureMeasure μ (SPG.prefixObservation h) P
      ↔ SPG.prefixBoundaryCellsMeasure μ h P = ∅ :=
  SPG.observablePureMeasure_iff_boundaryCellsMeasure_eq_empty μ (SPG.prefixObservation h) P

/-- Zero prefix scan error is equivalent to prefix-observable purity in the measure model.
    cond:prefix-measure-zero-iff-observable-pure -/
theorem prefixScanError_zero_iff_observablePure_measure [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    SPG.prefixScanErrorMeasure μ h P = 0
      ↔ SPG.ObservablePureMeasure μ (SPG.prefixObservation h) P :=
  SPG.prefixScanErrorMeasure_eq_zero_iff_observablePure μ h P

/-- Zero prefix scan error is equivalent to having empty prefix boundary in the measure model.
    cond:prefix-measure-zero-iff-boundary-empty -/
theorem prefixScanError_zero_iff_boundaryEmpty_measure [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    SPG.prefixScanErrorMeasure μ h P = 0 ↔ SPG.prefixBoundaryCellsMeasure μ h P = ∅ :=
  SPG.prefixScanErrorMeasure_eq_zero_iff_boundaryCellsMeasure_eq_empty μ h P

/-- Observable purity forces zero prefix scan error in the measure model.
    cond:prefix-observable-pure-zero-measure -/
theorem prefixObservablePure_zero_measure [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (P : Set (Word n))
    (hPure : SPG.ObservablePureMeasure μ (SPG.prefixObservation h) P) :
    SPG.prefixScanErrorMeasure μ h P = 0 :=
  SPG.prefixScanErrorMeasure_eq_zero_of_observablePure μ h P hPure

/-- Observable purity forces zero scan error for any finite observable measure model.
    cond:observable-pure-zero-measure -/
theorem observablePure_zero_measure [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α)
    (hPure : SPG.ObservablePureMeasure μ obs P) :
    SPG.scanErrorMeasure μ obs P = 0 :=
  SPG.scanErrorMeasure_eq_zero_of_observablePure μ obs P hPure

/-- Prefix scan error admits the boundary-cell decomposition in the measure model.
    cond:prefix-measure-boundary-decomposition -/
theorem prefixScanError_measure_boundary_decomposition [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    SPG.prefixScanErrorMeasure μ h P
      = Finset.sum (SPG.prefixBoundaryCellsMeasure μ h P) (fun b =>
          min (SPG.cellEventMeasure μ (SPG.prefixObservation h) P b)
            (SPG.cellComplMeasure μ (SPG.prefixObservation h) P b)) :=
  SPG.prefixScanErrorMeasure_eq_sum_boundary μ h P

/-- Prefix scan error is bounded by the total boundary-cell mass in the measure model.
    cond:prefix-measure-boundary-mass-bound -/
theorem prefixScanError_measure_boundary_mass_bound [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    SPG.prefixScanErrorMeasure μ h P
      ≤ Finset.sum (SPG.prefixBoundaryCellsMeasure μ h P) (fun b =>
          SPG.cellMeasure μ (SPG.prefixObservation h) b) :=
  SPG.prefixScanErrorMeasure_le_boundaryMass μ h P

/-- Prefix scan error is bounded by boundary cardinality times a uniform cell-mass cap.
    cond:prefix-measure-boundary-card-bound -/
theorem prefixScanError_measure_boundary_card_bound [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (P : Set (Word n)) (κ : ENNReal)
    (hκ : ∀ b, SPG.cellMeasure μ (SPG.prefixObservation h) b ≤ κ) :
    SPG.prefixScanErrorMeasure μ h P ≤ (SPG.prefixBoundaryCellsMeasure μ h P).card * κ :=
  SPG.prefixScanErrorMeasure_le_boundaryCard_mul μ h P κ hκ

/-- The measure-theoretic prefix scan error reduces to the discrete one for a finite PMF.
    bridge:prefix-scan-measure-discrete -/
theorem prefixScanError_measure_discrete_bridge [MeasurableSpace (Word n)]
    [MeasurableSingletonClass (Word n)]
    (μ : PMF (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    SPG.prefixScanErrorMeasure μ.toMeasure h P = SPG.prefixScanError μ h P :=
  SPG.prefixScanErrorMeasure_toMeasure_eq_prefixScanError μ h P

/-- Boundary cells commute with the PMF-to-measure bridge for finite observables.
    bridge:boundary-cells-measure-discrete -/
theorem boundaryCells_measure_discrete_bridge {α β : Type*} [Fintype α] [Fintype β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    SPG.boundaryCellsMeasure μ.toMeasure obs P = SPG.boundaryCells μ obs P :=
  SPG.boundaryCellsMeasure_toMeasure_eq_boundaryCells μ obs P

/-- Prefix boundary cells commute with the PMF-to-measure bridge.
    bridge:prefix-boundary-cells-measure-discrete -/
theorem prefixBoundaryCells_measure_discrete_bridge [MeasurableSpace (Word n)]
    [MeasurableSingletonClass (Word n)]
    (μ : PMF (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    SPG.prefixBoundaryCellsMeasure μ.toMeasure h P = SPG.prefixBoundaryCells μ h P :=
  SPG.prefixBoundaryCellsMeasure_toMeasure_eq_prefixBoundaryCells μ h P

/-- Pure prefix events remain zero-error after passing from PMFs to measures.
    bridge:prefix-event-measure-discrete-zero -/
theorem prefixEvent_pure_measure_discrete_bridge [MeasurableSpace (Word n)]
    [MeasurableSingletonClass (Word n)]
    (μ : PMF (Word n)) (h : m ≤ n) (A : Set (Word m)) :
    SPG.prefixScanErrorMeasure μ.toMeasure h (SPG.prefixEvent h A) = 0 := by
  rw [prefixScanError_measure_discrete_bridge μ h]
  exact SPG.prefixScanError_eq_zero_of_prefixEvent μ h A

/-- Prefix zero-error certificates are canonically valid.
    cond:prefix-zero-scan-certificate -/
theorem prefixZeroScan_hasCertificate {m n : Nat}
    (μ : PMF (Word n)) (h : m ≤ n) (A : Set (Word m)) :
    PrefixZeroScanCertificate.Valid { m := m, n := n, h := h, μ := μ, event := A } :=
  PrefixZeroScanCertificate.canonical μ h A

/-- Scan error is symmetric under complement of the event (discrete).
    cond:scan-error-complement-discrete -/
theorem scanError_compl_discrete {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    SPG.scanError μ obs Pᶜ = SPG.scanError μ obs P :=
  SPG.scanError_compl μ obs P

/-- Scan error of the empty event is zero (discrete).
    cond:scan-error-empty-discrete -/
theorem scanError_empty_discrete {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) :
    SPG.scanError μ obs ∅ = 0 :=
  SPG.scanError_empty μ obs

/-- Scan error of the full event is zero (discrete).
    cond:scan-error-univ-discrete -/
theorem scanError_univ_discrete {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) :
    SPG.scanError μ obs Set.univ = 0 :=
  SPG.scanError_univ μ obs

/-- Observable events are observable-pure in the discrete model.
    cond:observable-event-pure-discrete -/
theorem observableEvent_observablePure_discrete {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (A : Set β) :
    SPG.ObservablePure μ obs (SPG.observableEvent obs A) :=
  SPG.observablePure_observableEvent μ obs A

/-- Discrete observable purity is equivalent to having empty boundary.
    cond:discrete-pure-iff-boundary-empty -/
theorem observablePure_iff_boundaryEmpty_discrete {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    SPG.ObservablePure μ obs P ↔ SPG.boundaryCells μ obs P = ∅ :=
  SPG.observablePure_iff_boundaryCells_eq_empty μ obs P

/-- Zero discrete scan error is equivalent to discrete observable purity.
    cond:discrete-zero-iff-pure -/
theorem scanError_zero_iff_observablePure_discrete {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    SPG.scanError μ obs P = 0 ↔ SPG.ObservablePure μ obs P :=
  SPG.scanError_eq_zero_iff_observablePure μ obs P

/-- Zero discrete scan error is equivalent to empty boundary.
    cond:discrete-zero-iff-boundary-empty -/
theorem scanError_zero_iff_boundaryEmpty_discrete {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    SPG.scanError μ obs P = 0 ↔ SPG.boundaryCells μ obs P = ∅ :=
  SPG.scanError_eq_zero_iff_boundaryCells_eq_empty μ obs P

/-- Scan error is symmetric under complement of the event (measure).
    cond:scan-error-complement-measure -/
theorem scanError_compl_measure [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) :
    SPG.scanErrorMeasure μ obs Pᶜ = SPG.scanErrorMeasure μ obs P :=
  SPG.scanErrorMeasure_compl μ obs P

/-- Scan error of the empty event is zero (measure).
    cond:scan-error-empty-measure -/
theorem scanError_empty_measure [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) :
    SPG.scanErrorMeasure μ obs ∅ = 0 :=
  SPG.scanErrorMeasure_empty μ obs

/-- Scan error of the full event is zero (measure).
    cond:scan-error-univ-measure -/
theorem scanError_univ_measure [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) :
    SPG.scanErrorMeasure μ obs Set.univ = 0 :=
  SPG.scanErrorMeasure_univ μ obs

/-- Prefix events are observable-pure in the discrete model.
    cond:prefix-event-pure-discrete-obs -/
theorem prefixEvent_observablePure_discrete (μ : PMF (Word n)) (h : m ≤ n) (A : Set (Word m)) :
    SPG.ObservablePure μ (SPG.prefixObservation h) (SPG.prefixEvent h A) :=
  SPG.prefixObservablePure_prefixEvent μ h A

/-- Zero discrete prefix scan error is equivalent to prefix-observable purity.
    cond:prefix-scan-zero-iff-pure-discrete -/
theorem prefixScanError_zero_iff_observablePure_discrete (μ : PMF (Word n)) (h : m ≤ n)
    (P : Set (Word n)) :
    SPG.prefixScanError μ h P = 0 ↔ SPG.ObservablePure μ (SPG.prefixObservation h) P :=
  SPG.prefixScanError_eq_zero_iff_observablePure μ h P

/-- Zero discrete prefix scan error is equivalent to empty prefix boundary.
    cond:prefix-scan-zero-iff-boundary-discrete -/
theorem prefixScanError_zero_iff_boundaryEmpty_discrete (μ : PMF (Word n)) (h : m ≤ n)
    (P : Set (Word n)) :
    SPG.prefixScanError μ h P = 0 ↔ SPG.prefixBoundaryCells μ h P = ∅ :=
  SPG.prefixScanError_eq_zero_iff_boundaryCells_eq_empty μ h P

/-- Prefix scan error is symmetric under complement (discrete).
    cond:prefix-scan-compl-discrete -/
theorem prefixScanError_compl_discrete (μ : PMF (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    SPG.prefixScanError μ h Pᶜ = SPG.prefixScanError μ h P :=
  SPG.prefixScanError_compl μ h P

/-- Prefix scan error of the empty event is zero (discrete).
    cond:prefix-scan-empty-discrete -/
theorem prefixScanError_empty_discrete (μ : PMF (Word n)) (h : m ≤ n) :
    SPG.prefixScanError μ h ∅ = 0 :=
  SPG.prefixScanError_empty μ h

/-- Prefix scan error of the full event is zero (discrete).
    cond:prefix-scan-univ-discrete -/
theorem prefixScanError_univ_discrete (μ : PMF (Word n)) (h : m ≤ n) :
    SPG.prefixScanError μ h Set.univ = 0 :=
  SPG.prefixScanError_univ μ h

/-- Discrete observable purity is equivalent to measure-theoretic purity under PMF.toMeasure.
    bridge:cond-purity-pmf-measure -/
theorem observablePure_measure_discrete_bridge {α β : Type*} [Fintype α] [Fintype β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    SPG.ObservablePureMeasure μ.toMeasure obs P ↔ SPG.ObservablePure μ obs P :=
  SPG.observablePureMeasure_toMeasure_iff_observablePure μ obs P

/-- Prefix scan error is symmetric under complement (measure).
    cond:prefix-scan-compl-measure -/
theorem prefixScanError_compl_measure [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    SPG.prefixScanErrorMeasure μ h Pᶜ = SPG.prefixScanErrorMeasure μ h P :=
  SPG.prefixScanErrorMeasure_compl μ h P

/-- Prefix scan error of the empty event is zero (measure).
    cond:prefix-scan-empty-measure -/
theorem prefixScanError_empty_measure [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) :
    SPG.prefixScanErrorMeasure μ h ∅ = 0 :=
  SPG.prefixScanErrorMeasure_empty μ h

/-- Prefix scan error of the full event is zero (measure).
    cond:prefix-scan-univ-measure -/
theorem prefixScanError_univ_measure [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) :
    SPG.prefixScanErrorMeasure μ h Set.univ = 0 :=
  SPG.prefixScanErrorMeasure_univ μ h

/-- Finer observation reduces discrete scan error (observation refinement monotonicity).
    cond:observation-refinement-monotonicity -/
theorem scanError_antitone_of_refines {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (μ : PMF α) (obs₁ : α → β) (obs₂ : α → γ) (f : γ → β)
    (hRef : ∀ x, obs₁ x = f (obs₂ x)) (P : Set α) :
    SPG.scanError μ obs₂ P ≤ SPG.scanError μ obs₁ P :=
  SPG.scanError_antitone_of_refines μ obs₁ obs₂ f hRef P

/-- Prefix scan error is monotonically non-increasing in the prefix resolution.
    cond:prefix-scan-error-monotonicity -/
theorem prefixScanError_antitone {m₁ m₂ n : Nat}
    (μ : PMF (Word n)) (h₁ : m₁ ≤ n) (h₂ : m₂ ≤ n) (hm : m₁ ≤ m₂)
    (P : Set (Word n)) :
    SPG.prefixScanError μ h₂ P ≤ SPG.prefixScanError μ h₁ P :=
  SPG.prefixScanError_antitone μ h₁ h₂ hm P

/-- Cell event masses partition the total event mass (discrete).
    cond:cell-event-mass-partition -/
theorem cellEventMass_partition {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    ∑ b, SPG.cellEventMass μ obs P b = SPG.setMass μ P :=
  SPG.cellEventMass_sum_eq_setMass μ obs P

/-- Cell complement masses partition the total complement mass (discrete).
    cond:cell-compl-mass-partition -/
theorem cellComplMass_partition {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    ∑ b, SPG.cellComplMass μ obs P b = SPG.setMass μ Pᶜ :=
  SPG.cellComplMass_sum_eq_setMass_compl μ obs P

/-- Scan error is bounded by the Bayes-optimal error min(μ(P), μ(Pᶜ)) (discrete).
    cond:scan-error-bayes-bound -/
theorem scanError_bayes_bound {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    SPG.scanError μ obs P ≤ min (SPG.setMass μ P) (SPG.setMass μ Pᶜ) :=
  SPG.scanError_le_min_setMass μ obs P

/-- Scan error under a general measure is bounded by the Bayes-optimal bound.
    cond:measure-scan-error-bayes-bound -/
theorem scanError_measure_bayes_bound [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) :
    SPG.scanErrorMeasure μ obs P ≤ min
        (∑ b, SPG.cellEventMeasure μ obs P b) (∑ b, SPG.cellComplMeasure μ obs P b) :=
  SPG.scanErrorMeasure_le_min μ obs P

/-! ### Paper Section 4: Stable Syntax Cardinality & Zeckendorf Bridge -/

/-- |X_m| = F_{m+2} (paper Proposition 4.1: Fibonacci cardinality).
    cond:stable-syntax-fibonacci-cardinality -/
theorem stableSyntax_card_eq_fibonacci (m : Nat) :
    Fintype.card (X m) = Nat.fib (m + 2) :=
  X.card_eq_fib m

/-- |X_{m+2}| = |X_{m+1}| + |X_m| (paper Proposition 4.1: Fibonacci recurrence).
    cond:stable-syntax-fibonacci-recurrence -/
theorem stableSyntax_card_recurrence (m : Nat) :
    Fintype.card (X (m + 2)) = Fintype.card (X (m + 1)) + Fintype.card (X m) :=
  X.card_recurrence m

/-- Active positions of a stable word form a Zeckendorf representation (paper Theorem 4.1).
    cond:zeckendorf-valid -/
theorem stableWord_zeckendorf_valid (x : X m) :
    (X.zeckIndices x).IsZeckendorfRep :=
  X.zeckIndices_isZeckendorfRep x

/-- The stable value equals the Fibonacci-weighted sum at active positions (paper Theorem 4.1).
    cond:stable-value-fibonacci-sum -/
theorem stableValue_eq_fibonacci_weighted_sum (x : X m) :
    stableValue x = ((X.zeckIndices x).map Nat.fib).sum :=
  X.stableValue_eq_sum_fib_zeckIndices x

/-- The Zeckendorf encoding of a stable word sums to its stable value. -/
theorem stableValue_eq_zeckRep_sum (x : X m) :
    ((X.zeckRep x).1.map Nat.fib).sum = stableValue x :=
  X.sum_fib_zeckRep x

/-- Every stable target has a positive fiber cardinality under Fold.
    cond:fold-fiber-card-pos -/
theorem fold_fiber_card_pos (x : X m) :
    0 < (X.fiber x).card :=
  X.fiber_card_pos x

/-! ### Paper Section 6: Stable Value & Modular Arithmetic -/

/-- The stable value map is injective: distinct stable words have distinct values (paper Theorem 6.1).
    cond:stable-value-injective -/
theorem stableValue_injective (m : Nat) :
    Function.Injective (stableValue (m := m)) :=
  Function.HasLeftInverse.injective ⟨X.ofNat m, X.ofNat_stableValue⟩

/-- Constructing a stable word from its value recovers the original word (paper Theorem 6.1).
    cond:stable-value-ofnat-roundtrip -/
theorem stableValue_ofNat_roundtrip (x : X m) :
    X.ofNat m (stableValue x) = x :=
  X.ofNat_stableValue x

/-- Fold followed by ofNat recovers the fold: ofNat m (stableValue (Fold w)) = Fold w. -/
theorem fold_ofNat_roundtrip (w : Word m) :
    X.ofNat m (stableValue (Fold w)) = Fold w :=
  X.ofNat_stableValue (Fold w)

/-! ### Paper Section 3 / Definition 3.5: Boundary Cylinder Count -/

/-- Boundary cylinder count equals zero iff the event is observable-pure (measure, paper Corollary 3.1).
    cond:boundary-count-zero-iff-pure -/
theorem boundaryCylinderCount_zero_iff_pure_measure [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) :
    SPG.boundaryCylinderCount μ obs P = 0 ↔ SPG.ObservablePureMeasure μ obs P :=
  SPG.boundaryCylinderCount_eq_zero_iff_observablePure μ obs P

/-- Zero scan error iff zero boundary cylinder count (measure, paper Corollary 3.1).
    cond:scan-error-zero-iff-boundary-count-zero -/
theorem scanError_zero_iff_boundaryCylinderCount_zero_measure [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) :
    SPG.scanErrorMeasure μ obs P = 0 ↔ SPG.boundaryCylinderCount μ obs P = 0 :=
  SPG.scanErrorMeasure_eq_zero_iff_boundaryCylinderCount_eq_zero μ obs P

/-- Observable-event boundary cylinder count vanishes for any measure. -/
theorem boundaryCylinderCount_observableEvent_zero [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure α) (obs : α → β) (A : Set β) :
    SPG.boundaryCylinderCount μ obs (SPG.observableEvent obs A) = 0 :=
  SPG.boundaryCylinderCount_observableEvent_eq_zero μ obs A

/-- Prefix event boundary cylinder count vanishes for any measure. -/
theorem prefixBoundaryCylinderCount_prefixEvent_zero [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (A : Set (Word m)) :
    SPG.prefixBoundaryCylinderCount μ h (SPG.prefixEvent h A) = 0 :=
  SPG.prefixBoundaryCylinderCount_prefixEvent_eq_zero μ h A

/-- Prefix boundary cylinder count equals zero iff the event is observable-pure (measure). -/
theorem prefixBoundaryCylinderCount_zero_iff_pure_measure [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    SPG.prefixBoundaryCylinderCount μ h P = 0
      ↔ SPG.ObservablePureMeasure μ (SPG.prefixObservation h) P :=
  SPG.prefixBoundaryCylinderCount_eq_zero_iff_observablePure μ h P

/-- Zero prefix scan error iff zero prefix boundary cylinder count (measure). -/
theorem prefixScanError_zero_iff_boundaryCylinderCount_zero_measure
    [MeasurableSpace (Word n)]
    (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    SPG.prefixScanErrorMeasure μ h P = 0 ↔ SPG.prefixBoundaryCylinderCount μ h P = 0 :=
  SPG.prefixScanErrorMeasure_eq_zero_iff_boundaryCylinderCount_eq_zero μ h P

/-- Boundary cylinder count commutes with the PMF-to-measure bridge.
    cond:boundary-count-pmf-bridge -/
theorem boundaryCylinderCount_measure_discrete_bridge {α β : Type*} [Fintype α] [Fintype β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : PMF α) (obs : α → β) (P : Set α) :
    SPG.boundaryCylinderCount μ.toMeasure obs P = (SPG.boundaryCells μ obs P).card :=
  SPG.boundaryCylinderCount_toMeasure_eq μ obs P

/-- Prefix boundary cylinder count commutes with the PMF-to-measure bridge. -/
theorem prefixBoundaryCylinderCount_measure_discrete_bridge
    [MeasurableSpace (Word n)] [MeasurableSingletonClass (Word n)]
    (μ : PMF (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    SPG.prefixBoundaryCylinderCount μ.toMeasure h P
      = (SPG.prefixBoundaryCells μ h P).card :=
  SPG.prefixBoundaryCylinderCount_toMeasure_eq μ h P

/-! ### Paper Section 3: Cell Partition Identity -/

/-- Cell event mass plus complement mass equals total cell mass (paper Proposition 3.2 partition).
    cond:cell-partition-identity -/
theorem cellEventMass_add_cellComplMass_partition {α β : Type*} [Fintype α]
    (μ : PMF α) (obs : α → β) (P : Set α) (b : β) :
    SPG.cellEventMass μ obs P b + SPG.cellComplMass μ obs P b = SPG.cellMass μ obs b :=
  SPG.cellEventMass_add_cellComplMass_eq_cellMass μ obs P b

/-! ### Measure Monotonicity via PMF Bridge (paper Corollary 3.1) -/

/-- Scan error monotonicity under observation refinement, measure version via PMF bridge.
    cond:measure-antitone-observation-refinement -/
theorem scanError_measure_antitone_via_bridge
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : PMF α) (obs₁ : α → β) (obs₂ : α → γ) (f : γ → β)
    (hRef : ∀ x, obs₁ x = f (obs₂ x)) (P : Set α) :
    SPG.scanErrorMeasure μ.toMeasure obs₂ P ≤ SPG.scanErrorMeasure μ.toMeasure obs₁ P := by
  rw [SPG.scanErrorMeasure_toMeasure_eq_scanError,
    SPG.scanErrorMeasure_toMeasure_eq_scanError]
  exact SPG.scanError_antitone_of_refines μ obs₁ obs₂ f hRef P

/-- Prefix scan error under measure is monotonically non-increasing for PMF-lifted measures
    (paper Corollary 3.1: clarity monotonicity).
    cond:prefix-measure-antitone -/
theorem prefixScanError_measure_antitone_via_bridge {m₁ m₂ n : Nat}
    [MeasurableSpace (Word n)] [MeasurableSingletonClass (Word n)]
    (μ : PMF (Word n)) (h₁ : m₁ ≤ n) (h₂ : m₂ ≤ n) (hm : m₁ ≤ m₂)
    (P : Set (Word n)) :
    SPG.prefixScanErrorMeasure μ.toMeasure h₂ P
      ≤ SPG.prefixScanErrorMeasure μ.toMeasure h₁ P := by
  rw [SPG.prefixScanErrorMeasure_toMeasure_eq_prefixScanError,
    SPG.prefixScanErrorMeasure_toMeasure_eq_prefixScanError]
  exact SPG.prefixScanError_antitone μ h₁ h₂ hm P

end

end Omega.Frontier

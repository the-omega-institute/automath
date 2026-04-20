import Mathlib.Tactic

namespace Omega.Folding

/-- The natural extension of `T`, written as a one-sided predecessor history. -/
def NaturalExtension {X : Type*} (T : X → X) :=
  { history : ℕ → X // ∀ n, T (history (n + 1)) = history n }

/-- The natural-extension shift `(x₀, x₋₁, x₋₂, ...) ↦ (T x₀, x₀, x₋₁, ...)`. -/
def naturalExtensionShift {X : Type*} (T : X → X) (s : NaturalExtension T) : NaturalExtension T :=
  ⟨fun
      | 0 => T (s.1 0)
      | n + 1 => s.1 n,
    by
      intro n
      cases n <;> simp [s.2]⟩

/-- The branch-register code keeps the present state together with the predecessor labels. -/
def branchRegisterCode {X : Type*} (T : X → X) (beta : X → ℕ) (s : NaturalExtension T) :
    X × (ℕ → ℕ) :=
  (s.1 0, fun n => beta (s.1 (n + 1)))

/-- The image of the branch-register code. -/
def branchRegisterImage {X : Type*} (T : X → X) (beta : X → ℕ) :=
  Set.range (branchRegisterCode T beta)

/-- The code map viewed as a function into its image subtype. -/
def branchRegisterCodeToImage {X : Type*} (T : X → X) (beta : X → ℕ) :
    NaturalExtension T → branchRegisterImage T beta :=
  fun s => ⟨branchRegisterCode T beta s, ⟨s, rfl⟩⟩

/-- Recursive reconstruction of the predecessor history from the current state and branch labels. -/
def branchRegisterDecode {X : Type*} (decode : X → ℕ → X) (x : X) (a : ℕ → ℕ) : ℕ → X
  | 0 => x
  | n + 1 => decode (branchRegisterDecode decode x a n) (a n)

/-- The recursively reconstructed history always lies in the natural extension. -/
def branchRegisterDecodeExtension {X : Type*} (T : X → X) (decode : X → ℕ → X)
    (hT : ∀ y a, T (decode y a) = y) (x : X) (a : ℕ → ℕ) : NaturalExtension T :=
  ⟨branchRegisterDecode decode x a, by
    intro n
    simp [branchRegisterDecode, hT]⟩

/-- Decoder restricted to the image of the code map. -/
def branchRegisterDecodeImage {X : Type*} (T : X → X) (beta : X → ℕ) (decode : X → ℕ → X)
    (hT : ∀ y a, T (decode y a) = y) (z : branchRegisterImage T beta) : NaturalExtension T :=
  branchRegisterDecodeExtension T decode hT z.1.1 z.1.2

/-- The right-insert update on the branch register. -/
def branchRegisterRightInsert {X : Type*} (T : X → X) (beta : X → ℕ) (p : X × (ℕ → ℕ)) :
    X × (ℕ → ℕ) :=
  (T p.1, fun
    | 0 => beta p.1
    | n + 1 => p.2 n)

/-- The shift transported to the image of the branch-register code. -/
noncomputable def branchRegisterShift {X : Type*} (T : X → X) (beta : X → ℕ) :
    branchRegisterImage T beta → branchRegisterImage T beta
  | ⟨p, hp⟩ =>
      let s := Classical.choose hp
      ⟨branchRegisterRightInsert T beta p, by
        refine ⟨naturalExtensionShift T s, ?_⟩
        have hs : branchRegisterCode T beta s = p := Classical.choose_spec hp
        have hs0 : s.1 0 = p.1 := by
          simpa [branchRegisterCode] using congrArg Prod.fst hs
        have hstail : (fun n => beta (s.1 (n + 1))) = p.2 := by
          simpa [branchRegisterCode] using congrArg Prod.snd hs
        apply Prod.ext
        · simp [branchRegisterCode, branchRegisterRightInsert, naturalExtensionShift, hs0]
        · funext n
          cases n with
          | zero =>
              simp [branchRegisterCode, branchRegisterRightInsert, naturalExtensionShift, hs0]
          | succ n =>
              have hnth := congrArg (fun f => f n) hstail
              simpa [branchRegisterCode, branchRegisterRightInsert, naturalExtensionShift] using hnth⟩

lemma branchRegisterDecode_code_history {X : Type*} (T : X → X) (beta : X → ℕ)
    (decode : X → ℕ → X) (hdecode : ∀ x, decode (T x) (beta x) = x) (s : NaturalExtension T) :
    ∀ n, branchRegisterDecode decode (s.1 0) (fun k => beta (s.1 (k + 1))) n = s.1 n
  | 0 => rfl
  | n + 1 => by
      rw [branchRegisterDecode, branchRegisterDecode_code_history T beta decode hdecode s n, ← s.2 n]
      exact hdecode (s.1 (n + 1))

lemma branchRegisterDecodeImage_codeToImage {X : Type*} (T : X → X) (beta : X → ℕ)
    (decode : X → ℕ → X) (hT : ∀ y a, T (decode y a) = y)
    (hdecode : ∀ x, decode (T x) (beta x) = x) (s : NaturalExtension T) :
    branchRegisterDecodeImage T beta decode hT (branchRegisterCodeToImage T beta s) = s := by
  apply Subtype.ext
  funext n
  simpa [branchRegisterDecodeImage, branchRegisterCodeToImage, branchRegisterCode] using
    branchRegisterDecode_code_history T beta decode hdecode s n

lemma branchRegisterCode_decodeExtension {X : Type*} (T : X → X) (beta : X → ℕ)
    (decode : X → ℕ → X) (hT : ∀ y a, T (decode y a) = y) (hβ : ∀ y a, beta (decode y a) = a)
    (x : X) (a : ℕ → ℕ) :
    branchRegisterCode T beta (branchRegisterDecodeExtension T decode hT x a) = (x, a) := by
  apply Prod.ext
  · rfl
  · funext n
    simp [branchRegisterCode, branchRegisterDecodeExtension, branchRegisterDecode, hβ]

lemma branchRegisterCodeToImage_decodeImage {X : Type*} (T : X → X) (beta : X → ℕ)
    (decode : X → ℕ → X) (hT : ∀ y a, T (decode y a) = y) (hβ : ∀ y a, beta (decode y a) = a)
    (z : branchRegisterImage T beta) :
    branchRegisterCodeToImage T beta (branchRegisterDecodeImage T beta decode hT z) = z := by
  apply Subtype.ext
  exact branchRegisterCode_decodeExtension T beta decode hT hβ z.1.1 z.1.2

/-- Recursive decoding gives an inverse on the image of the branch-register code, so the code map
is bijective onto its image and transports the natural-extension shift to right insertion.
    thm:killo-natural-extension-branch-register -/
theorem paper_killo_natural_extension_branch_register {X : Type*} (T : X → X) (beta : X → ℕ)
    (decode : X → ℕ → X) (hT : ∀ y a, T (decode y a) = y) (hβ : ∀ y a, beta (decode y a) = a)
    (hdecode : ∀ x, decode (T x) (beta x) = x) :
    Function.Bijective (branchRegisterCodeToImage T beta) ∧
      Function.LeftInverse (branchRegisterDecodeImage T beta decode hT)
        (branchRegisterCodeToImage T beta) ∧
      Function.RightInverse (branchRegisterDecodeImage T beta decode hT)
        (branchRegisterCodeToImage T beta) ∧
      ∀ s : NaturalExtension T,
        branchRegisterShift T beta (branchRegisterCodeToImage T beta s) =
          branchRegisterCodeToImage T beta (naturalExtensionShift T s) := by
  have hLeft : Function.LeftInverse (branchRegisterDecodeImage T beta decode hT)
      (branchRegisterCodeToImage T beta) := by
    intro s
    exact branchRegisterDecodeImage_codeToImage T beta decode hT hdecode s
  have hRight : Function.RightInverse (branchRegisterDecodeImage T beta decode hT)
      (branchRegisterCodeToImage T beta) := by
    intro z
    exact branchRegisterCodeToImage_decodeImage T beta decode hT hβ z
  refine ⟨?_, hLeft, hRight, ?_⟩
  · constructor
    · exact hLeft.injective
    · intro z
      exact ⟨branchRegisterDecodeImage T beta decode hT z, hRight z⟩
  · intro s
    apply Subtype.ext
    apply Prod.ext
    · simp [branchRegisterShift, branchRegisterCodeToImage, branchRegisterRightInsert,
        branchRegisterCode, naturalExtensionShift]
    · funext n
      cases n <;> simp [branchRegisterShift, branchRegisterCodeToImage, branchRegisterRightInsert,
        branchRegisterCode, naturalExtensionShift]

end Omega.Folding

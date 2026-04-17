import Mathlib.Data.Rat.Defs
import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.ExplicitLifting
import Omega.TypedAddressBiaxialCompletion.FrontInterface

namespace Omega.TypedAddressBiaxialCompletion

/-- Concrete unitary-slice addresses carrying the typed precision index from the paper. -/
structure AddrUS where
  radius : ℕ
  phase : ℚ
  precision : ℕ
  radius_gt_one : 1 < radius
deriving DecidableEq

/-- Certificates distinguish the two verified non-`NULL` branches. -/
inductive CertifiedRead where
  | nonZero
  | rootInterval
deriving DecidableEq, Repr

/-- A typed certificate records its precision layer, the verified interval, and the semantic
branch certified on that interval. -/
structure TypedCertificate where
  precision : ℕ
  leftEndpoint : ℚ
  rightEndpoint : ℚ
  intervalOrdered : leftEndpoint ≤ rightEndpoint
  verdict : CertifiedRead
deriving DecidableEq

/-- Precision compatibility is the typed-address side condition saying that the certificate lives
at the same explicit precision layer as the queried address. -/
def precisionCompatible (a : AddrUS) (cert : TypedCertificate) : Bool :=
  cert.precision == a.precision

/-- Three-valued `Read_US` output advertised in the paper. -/
inductive ReadUSOutput where
  | NonZero
  | RootInterval
  | NULL
deriving DecidableEq, Repr

/-- Deterministic three-valued readout on the unitary slice: a verified typed certificate returns
either `NonZero` or `RootInterval`, while missing, ill-typed, or rejected certificates return
`NULL`. -/
def Read_US
    (a : AddrUS) (Ver : TypedCertificate → Bool) (cert? : Option TypedCertificate) :
    ReadUSOutput :=
  match cert? with
  | some cert =>
      if precisionCompatible a cert && Ver cert then
        match cert.verdict with
        | .nonZero => .NonZero
        | .rootInterval => .RootInterval
      else
        .NULL
  | none => .NULL

/-- The typed-address front interface specialized to the concrete `Read_US` output above. -/
def readUsFrontInterface
    (Ver : TypedCertificate → Bool) (certs : AddrUS → Option TypedCertificate) : FrontInterfaceData
    where
  XFin := AddrUS
  Xhat := AddrUS
  PComp := AddrUS
  AddrTyped := AddrUS
  Readout := ReadUSOutput
  AuditLedger := ReadUSOutput
  SpecLayer := ReadUSOutput
  comp := id
  phase := id
  addr := id
  Read_US := fun a => Read_US a Ver (certs a)
  audit := id
  spec := id

/-- The three-valued `Read_US` semantics is determined by case analysis on the available typed
certificate witness: verified typed witnesses produce `NonZero` or `RootInterval`, and every other
case collapses to `NULL`.
    prop:typed-address-biaxial-completion-read-us-typed-precision -/
theorem paper_typed_address_biaxial_completion_read_us_typed_precision
    (a : AddrUS) (Ver : TypedCertificate → Bool) (cert? : Option TypedCertificate) :
    (∃ comp : AddrUS → AddrUS,
      ∃ phase : AddrUS → AddrUS,
        ∃ addr : AddrUS → AddrUS,
          ∃ read : AddrUS → ReadUSOutput,
            ∃ audit : ReadUSOutput → ReadUSOutput,
              ∃ spec : ReadUSOutput → ReadUSOutput,
                comp = (readUsFrontInterface Ver (fun x => if x = a then cert? else none)).comp ∧
                  phase = (readUsFrontInterface Ver (fun x => if x = a then cert? else none)).phase ∧
                    addr = (readUsFrontInterface Ver (fun x => if x = a then cert? else none)).addr ∧
                      read = (readUsFrontInterface Ver (fun x => if x = a then cert? else none)).Read_US ∧
                        audit =
                          (readUsFrontInterface Ver (fun x => if x = a then cert? else none)).audit ∧
                        spec =
                          (readUsFrontInterface Ver (fun x => if x = a then cert? else none)).spec) ∧
      (Read_US a Ver cert? = ReadUSOutput.NonZero ∨
        Read_US a Ver cert? = ReadUSOutput.RootInterval ∨
        Read_US a Ver cert? = ReadUSOutput.NULL) ∧
      (Read_US a Ver cert? = ReadUSOutput.NULL ↔
        cert? = none ∨
          ∃ cert, cert? = some cert ∧
            (precisionCompatible a cert = false ∨ Ver cert = false)) := by
  refine ⟨?_, ?_⟩
  · exact
      paper_typed_address_biaxial_completion_front_interface
        (readUsFrontInterface Ver (fun x => if x = a then cert? else none))
  · refine ⟨?_, ?_⟩
    · cases cert? with
      | none =>
          simp [Read_US]
      | some cert =>
          by_cases hTyped : precisionCompatible a cert = true
          · by_cases hVer : Ver cert = true
            · cases hVerdict : cert.verdict <;> simp [Read_US, hTyped, hVer, hVerdict]
            · simp [Read_US, hTyped, hVer]
          · simp [Read_US, hTyped]
    · cases cert? with
      | none =>
          simp [Read_US]
      | some cert =>
          by_cases hTyped : precisionCompatible a cert = true
          · by_cases hVer : Ver cert = true
            · cases hVerdict : cert.verdict <;> simp [Read_US, hTyped, hVer, hVerdict]
            · simp [Read_US, hTyped, hVer]
          · simp [Read_US, hTyped]

end Omega.TypedAddressBiaxialCompletion

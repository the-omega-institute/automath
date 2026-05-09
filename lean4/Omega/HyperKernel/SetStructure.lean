import Std
import Omega.HyperKernel.Op
import Omega.HyperKernel.Analysis
import Omega.HyperKernel.Enum
import Omega.HyperKernel.Closure
import Omega.HyperKernel.Pretty

namespace HyperKernel
namespace SetStructure

open Analysis
open Closure
open Pretty

def isIdempotent (n : Nat) (e : Op n) : Prop :=
  Op.comp n e e = e

def isPoint (n : Nat) (p : Op n) : Prop :=
  isIdempotent n p ∧ rank p = 1

def isSetObj (n : Nat) (e : Op n) : Prop :=
  isIdempotent n e

def isIdempotentB (n : Nat) (e : Op n) : Bool :=
  Op.comp n e e == e

def isPointB (n : Nat) (p : Op n) : Bool :=
  isIdempotentB n p && (rank p == 1)

def isSetObjB (n : Nat) (e : Op n) : Bool :=
  isIdempotentB n e

def pointObjects (n : Nat) : List (Op n) :=
  (Enum.allOps n).filter (isPointB n)

def setObjects (n : Nat) : List (Op n) :=
  (Enum.allOps n).filter (isSetObjB n)

def pointObjectsInClosure (n : Nat) (dict : Dict n) : List (Op n) :=
  (dict.map Prod.fst).filter (isPointB n)

def setObjectsInClosure (n : Nat) (dict : Dict n) : List (Op n) :=
  (dict.map Prod.fst).filter (isSetObjB n)

def memPoint (n : Nat) (p : Op n) (e : Op n) : Prop :=
  Op.comp n e p = p

def memPointB (n : Nat) (p : Op n) (e : Op n) : Bool :=
  Op.comp n e p == p

theorem pointMemSelf (n : Nat) (p : Op n) (hp : isPoint n p) : memPoint n p p := by
  exact hp.1

private def insertSortedUnique (x : Nat) (acc : List Nat) : List Nat :=
  match acc with
  | [] => [x]
  | y :: ys =>
      if x = y then
        acc
      else if x < y then
        x :: acc
      else
        y :: insertSortedUnique x ys

abbrev SetSig (_n : Nat) := List Nat

private def meetSortedUnique (a b : List Nat) : List Nat :=
  match a, b with
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys =>
      if x = y then
        x :: meetSortedUnique xs ys
      else if x < y then
        meetSortedUnique xs (y :: ys)
      else
        meetSortedUnique (x :: xs) ys

private def joinSortedUnique (a b : List Nat) : List Nat :=
  match a, b with
  | [], bs => bs
  | as, [] => as
  | x :: xs, y :: ys =>
      if x = y then
        x :: joinSortedUnique xs ys
      else if x < y then
        x :: joinSortedUnique xs (y :: ys)
      else
        y :: joinSortedUnique (x :: xs) ys

def setSigMeet (n : Nat)
  (a b : SetSig n) : SetSig n :=
  meetSortedUnique a b

def setSigJoin (n : Nat)
  (a b : SetSig n) : SetSig n :=
  joinSortedUnique a b

def pointSet (n : Nat) (points : List (Op n)) (e : Op n) : SetSig n :=
  (List.zipIdx points).foldl
    (fun acc pe =>
      let point := pe.1
      let idx := pe.2
      if memPointB n point e then
        insertSortedUnique idx acc
      else
        acc)
    []

def isMonotonePoints (n : Nat) (points : List (Op n)) (e f : Op n) : Prop :=
  ∀ i, i ∈ pointSet n points e → i ∈ pointSet n points f

abbrev Point (n : Nat) := { p : Op n // isPoint n p }
abbrev SetObj (n : Nat) := { e : Op n // isSetObj n e }

inductive SetSigWithBot (n : Nat)
  | bot : SetSigWithBot n
  | some : SetSig n -> SetSigWithBot n

def belongs (n : Nat) (p : Point n) (s : SetObj n) : Prop :=
  Op.comp n s.1 p.1 = p.1

theorem belongs_self (n : Nat) (p : Point n) :
    belongs n p { val := p.1, property := p.2.1 } := by
  exact p.2.1

theorem memPoint_iff_belongs (n : Nat) (p : Point n) (s : SetObj n) :
    memPoint n p.1 s.1 ↔ belongs n p s := by
  rfl

-- legacy name kept for compatibility with the analyzer output
def subset (n : Nat) (points : List (Op n)) (e f : Op n) : Prop :=
  isMonotonePoints n points e f

theorem subset_refl (n : Nat) (points : List (Op n)) (e : Op n) : subset n points e e := by
  intro idx h
  exact h

theorem subset_trans
  (n : Nat)
  (points : List (Op n))
  {a b c : Op n}
  (hab : subset n points a b)
  (hbc : subset n points b c) : subset n points a c := by
  intro idx habc
  exact hbc idx (hab idx habc)

def pointSignature
  (n : Nat)
  (points : List (Op n))
  (e : Op n) : SetSig n :=
  pointSet n points e

def findByPointSignature
  (n : Nat)
  (dict : Dict n)
  (points : List (Op n))
  (sig : SetSig n) : Option (Op n) :=
  (setObjectsInClosure n dict).find? (fun e => pointSignature n points e = sig)

def retractOpOfSignature
  (n : Nat)
  (dict : Dict n)
  (points : List (Op n))
  (sig : SetSig n) : Option (Op n) :=
  findByPointSignature n dict points sig

def meetObj
  (n : Nat)
  (dict : Dict n)
  (points : List (Op n))
  (e f : Op n) : Option (Op n) :=
  findByPointSignature n dict points (setSigMeet n (pointSet n points e) (pointSet n points f))

def joinObj
  (n : Nat)
  (dict : Dict n)
  (points : List (Op n))
  (e f : Op n) : Option (Op n) :=
  findByPointSignature n dict points (setSigJoin n (pointSet n points e) (pointSet n points f))

def setSignaturesInClosure
  (n : Nat)
  (dict : Dict n) : List (SetSig n) :=
  let points := pointObjectsInClosure n dict
  let signatures := (setObjectsInClosure n dict).map (pointSignature n points)
  let rec dedup (acc : List (SetSig n)) (xs : List (SetSig n)) : List (SetSig n) :=
    match xs with
    | [] => acc
    | s :: ss =>
        let acc' := if acc.contains s then acc else s :: acc
        dedup acc' ss
  dedup [] signatures

def setSignaturesFromAllOps
  (n : Nat) : List (SetSig n) :=
  setSignaturesInClosure n ((Enum.allOps n).map (fun op => (op, [])))

def filterClosureByWordLength
  (n : Nat)
  (dict : Dict n)
  (maxLen : Nat) : Dict n :=
  dict.filter (fun p => p.2.length ≤ maxLen)

def signaturesInClosureByBudget
  (n : Nat)
  (dict : Dict n)
  (maxLen : Nat) : List (SetSig n) :=
  setSignaturesInClosure n (filterClosureByWordLength n dict maxLen)

def signatureCountCurve
  (n : Nat)
  (dict : Dict n)
  (maxLen : Nat) : List (Nat × Nat) :=
  (List.range (maxLen + 1)).map (fun l => (l, (signaturesInClosureByBudget n dict l).length))

def signaturesInClosureByBudgetWithBot
  (n : Nat)
  (dict : Dict n)
  (maxLen : Nat) : List (SetSigWithBot n) :=
  let botElem : SetSigWithBot n := SetSigWithBot.bot
  botElem :: (signaturesInClosureByBudget n dict maxLen).map SetSigWithBot.some

def signatureWithBotCountCurve
  (n : Nat)
  (dict : Dict n)
  (maxLen : Nat) : List (Nat × Nat) :=
  (List.range (maxLen + 1)).map (fun l => (l, (signaturesInClosureByBudgetWithBot n dict l).length))

def pointSetSig (n : Nat) (points : List (Op n)) (e : Op n) : SetSig n :=
  pointSet n points e

def setSigWithBotMeet (n : Nat) (a b : SetSigWithBot n) : SetSigWithBot n :=
  match a, b with
  | SetSigWithBot.bot, _ => SetSigWithBot.bot
  | _, SetSigWithBot.bot => SetSigWithBot.bot
  | SetSigWithBot.some sa, SetSigWithBot.some sb =>
      let i := setSigMeet n sa sb
      if i = [] then SetSigWithBot.bot else SetSigWithBot.some i

def setSigWithBotJoin (n : Nat) (a b : SetSigWithBot n) : SetSigWithBot n :=
  match a, b with
  | SetSigWithBot.bot, x => x
  | x, SetSigWithBot.bot => x
  | SetSigWithBot.some sa, SetSigWithBot.some sb =>
      SetSigWithBot.some (setSigJoin n sa sb)

def signatureToWithBot
  (n : Nat) (sig : SetSig n) : SetSigWithBot n :=
  if sig = [] then SetSigWithBot.bot else SetSigWithBot.some sig

def signatureInClosure
  (n : Nat)
  (dict : Dict n)
  (points : List (Op n))
  (sig : SetSig n) : Bool :=
  (findByPointSignature n dict points sig).isSome

structure SignatureBudgetStat (n : Nat) where
  level : Nat
  signatureCount : Nat
  meetMisses : Nat
  joinMisses : Nat
deriving Repr

private def signaturePairMisses
  (n : Nat)
  (dict : Dict n)
  (points : List (Op n))
  (sigs : List (SetSig n)) : Nat × Nat :=
  sigs.foldl
    (fun (meetAcc, joinAcc) a =>
      sigs.foldl
        (fun (meetAcc', joinAcc') b =>
          let meetSig := setSigMeet n a b
          let joinSig := setSigJoin n a b
          let meetOk := signatureInClosure n dict points meetSig
          let joinOk := signatureInClosure n dict points joinSig
          (if meetOk then meetAcc' else meetAcc' + 1,
           if joinOk then joinAcc' else joinAcc' + 1))
        (meetAcc, joinAcc))
    (0, 0)

def signatureWitness
  (n : Nat)
  (dict : Dict n)
  (sig : SetSig n) : Option (Op n) :=
  let points := pointObjectsInClosure n dict
  findByPointSignature n dict points sig

def signatureExists
  (n : Nat)
  (dict : Dict n)
  (sig : SetSig n) : Bool :=
  (signatureWitness n dict sig).isSome

def signatureBudgetStats
  (n : Nat)
  (dict : Dict n)
  (maxLen : Nat) : List (SignatureBudgetStat n) :=
  let points := pointObjectsInClosure n dict
  (List.range (maxLen + 1)).map (fun l =>
    let sigs := signaturesInClosureByBudget n dict l
    let (meetMisses, joinMisses) := signaturePairMisses n dict points sigs
    { level := l, signatureCount := sigs.length, meetMisses := meetMisses, joinMisses := joinMisses })

def signatureBudgetReport
  (n : Nat)
  (dict : Dict n)
  (maxLen : Nat) : List String :=
  (signatureBudgetStats n dict maxLen).map fun stat =>
    s!"budget {stat.level}: sigs={stat.signatureCount}, meet misses={stat.meetMisses}, join misses={stat.joinMisses}"

def signatureBudgetWithBotReport
  (n : Nat)
  (dict : Dict n)
  (maxLen : Nat) : List String :=
  (signatureWithBotCountCurve n dict maxLen).map fun (level, count) =>
    s!"level {level} (with bot): {count}"

def signaturesReportFromSetObjsByBudget
  (n : Nat)
  (dict : Dict n)
  (maxLen : Nat) : List String :=
  let stats := signatureBudgetStats n dict maxLen
  let preview :=
    (List.take 4 stats).map fun stat => s!"L{stat.level}: σ={stat.signatureCount} mm={stat.meetMisses} jm={stat.joinMisses}"
  let pointReport := pointObjectsInClosure n dict
  let pointSigCounts := signatureCountCurve n dict maxLen
  let withBotCounts := signatureWithBotCountCurve n dict maxLen
  let reportLen := stats.length
  [
    s!"pointObjects (in closure): {pointReport.length}",
    s!"budget levels checked: {reportLen}",
    s!"budget stats preview: {preview}",
    s!"first budgets: {List.take 8 pointSigCounts}",
    s!"first budgets with bot: {List.take 8 withBotCounts}"
  ]

def setSigSubset (a b : SetSig n) : Prop :=
  ∀ i, i ∈ a → i ∈ b

def setSigFromSetObj
  (n : Nat)
  (points : List (Op n))
  (e : Op n) : SetSig n :=
  pointSignature n points e

def signaturesReportFromSetObjs
  (n : Nat)
  (dict : Dict n) : List String :=
  let points := pointObjectsInClosure n dict
  let sigs := setSignaturesInClosure n dict
  let pairCount := sigs.length * sigs.length
  let missesMeet :=
    sigs.foldl
      (fun acc a =>
        acc + sigs.foldl
          (fun acc2 b =>
            if signatureInClosure n dict points (setSigMeet n a b) then acc2 else acc2 + 1) 0) 0
  [
    s!"pointObjects (in closure): {points.length}",
    s!"setObject signatures (nonempty): {sigs.length}",
    s!"pairCount(sigs): {pairCount}",
    s!"signature meet misses: {missesMeet}"
  ]

def signaturesReportFromSetObjsWithBot
  (n : Nat)
  (dict : Dict n) : List String :=
  let points := pointObjectsInClosure n dict
  let sigs := setSignaturesInClosure n dict
  let withBot :=
    SetSigWithBot.bot :: sigs.map SetSigWithBot.some
  let pairCount := withBot.length * withBot.length
  let meetsWithBot :=
    withBot.foldl
      (fun acc x =>
        acc + withBot.foldl
          (fun acc2 y =>
            let ok : Bool :=
              match x, y with
              | SetSigWithBot.bot, _ => true
              | _, SetSigWithBot.bot => true
              | SetSigWithBot.some sx, SetSigWithBot.some sy =>
                  let m := setSigMeet n sx sy
                  if m = [] then true else signatureInClosure n dict points m
            if ok then acc2 else acc2 + 1) 0) 0
  let joinsWithBot :=
    withBot.foldl
      (fun acc x =>
        acc + withBot.foldl
          (fun acc2 y =>
            let ok : Bool :=
              match x, y with
              | SetSigWithBot.bot, SetSigWithBot.bot => true
              | SetSigWithBot.bot, SetSigWithBot.some _ => true
              | SetSigWithBot.some _, SetSigWithBot.bot => true
              | SetSigWithBot.some sx, SetSigWithBot.some sy =>
                  signatureInClosure n dict points (setSigJoin n sx sy)
            if ok then acc2 else acc2 + 1) 0) 0
  [
    s!"pointObjects (in closure): {points.length}",
    s!"setObject signatures (with bot): {withBot.length}",
    s!"pairCount(sig+bot): {pairCount}",
    s!"signature meet misses (with bot): {meetsWithBot}",
    s!"signature join misses (with bot): {joinsWithBot}"
  ]

def latticeCandidateReport (n : Nat) (dict : Dict n) : List String :=
  let points := pointObjectsInClosure n dict
  let sets := setObjectsInClosure n dict
  let pairCount := sets.length * sets.length
  let missesMeet :=
    sets.foldl
      (fun acc a =>
        acc + sets.foldl
          (fun acc2 b =>
            if (meetObj n dict points a b).isSome then acc2 else acc2 + 1) 0) 0
  let missesJoin :=
    sets.foldl
      (fun acc a =>
        acc + sets.foldl
          (fun acc2 b =>
            if (joinObj n dict points a b).isSome then acc2 else acc2 + 1) 0) 0
  [
    s!"pointObjects (in closure): {points.length}",
    s!"setObjects (idempotent): {sets.length}",
    s!"pairCount: {pairCount}",
    s!"meet misses: {missesMeet}",
    s!"join misses: {missesJoin}"
  ]

def printLatticeReport (n : Nat) (dict : Dict n) : IO Unit := do
  let points := pointObjectsInClosure n dict
  let sets := setObjectsInClosure n dict
  if points.length = 0 then
    IO.println "no points found in closure"
  else
    IO.println s!"pointObjects (rank-1 idempotents) in closure = {points.length}"
  IO.println s!"setObjects (idempotent maps) in closure = {sets.length}"
  if points.length > 0 then
    for a in sets do
      for b in sets do
        let meetSig := setSigMeet n (pointSet n points a) (pointSet n points b)
        let joinSig := setSigJoin n (pointSet n points a) (pointSet n points b)
        let meetFound := (findByPointSignature n dict points meetSig).isSome
        let joinFound := (findByPointSignature n dict points joinSig).isSome
        if not meetFound || not joinFound then
          if not meetFound then
            IO.println s!"missing meet: a={opString a} b={opString b} meetSig={meetSig}"
          if not joinFound then
            IO.println s!"missing join: a={opString a} b={opString b} joinSig={joinSig}"

end SetStructure
end HyperKernel

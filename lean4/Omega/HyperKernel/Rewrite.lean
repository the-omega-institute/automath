/-
  HyperKernel.Rewrite
  ~~~~~~~~~~~~~~~~~~~~
  Formalization of the rewrite system from Definition 3.53 of the paper:
  "三生成元片段上的重写规则族"

  In the finite transformation semigroup T_n, the paper's three generators
  (PROJ, LIFT, E) correspond to (g0, g1, g2) with canonical order g0 ≺ g1 ≺ g2.

  The rewrite system sorts generator words toward the normal form
      LIFT ∘ PROJ ∘ E  ↔  g0^a · g1^b · g2^c
  while tracking:
  1. Inversions (逆序度量 μ): pairs violating canonical order
  2. Commutativity failures: adjacent swaps that change the computed function
  3. Anomaly accumulation: total commutativity failures along the normalization path
-/
import Omega.HyperKernel.Op
import Omega.HyperKernel.Analysis

namespace Omega.HyperKernel
namespace Rewrite

open Analysis

/-- Generator type tag, ordered as in the paper: LIFT(g0) ≺ PROJ(g1) ≺ E(g2). -/
inductive GenTag where
  | g0 : GenTag
  | g1 : GenTag
  | g2 : GenTag
deriving BEq, Repr

def GenTag.toNat : GenTag → Nat
  | .g0 => 0
  | .g1 => 1
  | .g2 => 2

/-- Canonical order: g0 < g1 < g2. -/
def GenTag.lt (a b : GenTag) : Bool := a.toNat < b.toNat

/-- A word is a list of generator indices. -/
abbrev Word := List Nat

/-- Count inversions (逆序度量 μ) in a word: pairs (i,j) with i<j but w[i]>w[j].
    This is the termination measure from Proposition 3.55. -/
def inversions (w : Word) : Nat :=
  let rec count (xs : List Nat) : Nat :=
    match xs with
    | [] => 0
    | x :: rest =>
        let inv := rest.filter (· < x) |>.length
        inv + count rest
  count w

/-- Check if a word is in normal form (sorted: all g0 before g1 before g2). -/
def isNormalForm (w : Word) : Bool :=
  let rec sorted : List Nat → Bool
    | [] => true
    | [_] => true
    | a :: b :: rest => a ≤ b && sorted (b :: rest)
  sorted w

/-- Word signature: (count_g0, count_g1, count_g2). -/
structure WordSignature where
  g0Count : Nat
  g1Count : Nat
  g2Count : Nat
deriving BEq, Repr

def wordSignature (w : Word) : WordSignature :=
  { g0Count := w.filter (· == 0) |>.length,
    g1Count := w.filter (· == 1) |>.length,
    g2Count := w.filter (· == 2) |>.length }

/-- A rewrite step record: what happened when we swapped position i and i+1. -/
structure RewriteStep (n : Nat) where
  position : Nat
  beforeWord : Word
  afterWord : Word
  beforeOp : Op n        -- function computed by word before swap
  afterOp : Op n         -- function computed by word after swap
  commutes : Bool        -- true if swap preserves the function
  inversionsBefore : Nat
  inversionsAfter : Nat

/-- Apply a word to get the resulting operation. -/
def evalWord (n : Nat) (gens : List (Op n)) (w : Word) : Op n :=
  applyWord n gens w

/-- Swap elements at positions i and i+1 in a list. -/
def swapAt (w : Word) (i : Nat) : Word :=
  let rec go (xs : List Nat) (pos : Nat) : List Nat :=
    match xs with
    | [] => []
    | [x] => [x]
    | x :: y :: rest =>
        if pos == i then y :: x :: rest
        else x :: go (y :: rest) (pos + 1)
  go w 0

/-- Find the first inversion (leftmost pair where w[i] > w[i+1]).
    Returns the position i, or none if sorted. -/
def findFirstInversion (w : Word) : Option Nat :=
  let rec go (xs : List Nat) (pos : Nat) : Option Nat :=
    match xs with
    | [] => none
    | [_] => none
    | a :: b :: rest =>
        if a > b then some pos
        else go (b :: rest) (pos + 1)
  go w 0

/-- Perform one rewrite step: find first inversion and swap.
    Records whether the swap preserves the function (commutativity). -/
def rewriteStep (n : Nat) (gens : List (Op n)) (w : Word) : Option (RewriteStep n × Word) :=
  match findFirstInversion w with
  | none => none  -- already in normal form
  | some pos =>
      let w' := swapAt w pos
      let opBefore := evalWord n gens w
      let opAfter := evalWord n gens w'
      let step : RewriteStep n :=
        { position := pos,
          beforeWord := w,
          afterWord := w',
          beforeOp := opBefore,
          afterOp := opAfter,
          commutes := opBefore == opAfter,
          inversionsBefore := inversions w,
          inversionsAfter := inversions w' }
      some (step, w')

/-- Full normalization trace: repeatedly apply rewrite steps until sorted.
    Returns the list of steps and the final word.
    Bounded by maxSteps to ensure termination. -/
partial def normalize (n : Nat) (gens : List (Op n)) (w : Word) :
    List (RewriteStep n) × Word :=
  let rec go (current : Word) (steps : List (RewriteStep n)) (fuel : Nat) :
      List (RewriteStep n) × Word :=
    if fuel == 0 then (steps.reverse, current)
    else
      match rewriteStep n gens current with
      | none => (steps.reverse, current)
      | some (step, next) =>
          go next (step :: steps) (fuel - 1)
  go w [] (w.length * w.length + 1)  -- inversions ≤ n*(n-1)/2

/-- Normalization result for a single function. -/
structure NormalizationResult (n : Nat) where
  originalWord : Word
  normalForm : Word
  originalOp : Op n
  normalFormOp : Op n
  steps : Nat
  totalInversions : Nat       -- initial inversions
  commutativityFailures : Nat -- swaps that changed the function
  functionPreserved : Bool    -- does the normal form compute the same function?

/-- Normalize a word and summarize. -/
def normalizeAndSummarize (n : Nat) (gens : List (Op n)) (w : Word) :
    NormalizationResult n :=
  let (steps, nf) := normalize n gens w
  let failures := steps.filter (fun s => !s.commutes) |>.length
  { originalWord := w,
    normalForm := nf,
    originalOp := evalWord n gens w,
    normalFormOp := evalWord n gens nf,
    steps := steps.length,
    totalInversions := inversions w,
    commutativityFailures := failures,
    functionPreserved := evalWord n gens w == evalWord n gens nf }

/-- Analyze the whole dictionary: for each function, normalize its BFS word
    and track commutativity failures. -/
def analyzeRewriting
    (n : Nat)
    (gens : List (Op n))
    (dict : List (Op n × List Nat)) :
    List (NormalizationResult n) :=
  dict.map (fun (_, w) => normalizeAndSummarize n gens w)

/-- Statistics over all normalization results. -/
structure RewriteStats where
  totalFunctions : Nat
  totalPreserved : Nat        -- functions where normalization preserves the function
  totalChanged : Nat          -- functions where normalization changes the function
  avgSteps : Float
  avgFailures : Float
  maxFailures : Nat
  alreadyNormal : Nat         -- words that were already in normal form

def computeRewriteStats (results : List (NormalizationResult n)) : RewriteStats :=
  let total := results.length
  if total == 0 then
    { totalFunctions := 0, totalPreserved := 0, totalChanged := 0,
      avgSteps := 0, avgFailures := 0, maxFailures := 0, alreadyNormal := 0 }
  else
    let preserved := results.filter (·.functionPreserved) |>.length
    let changed := total - preserved
    let sumSteps := results.foldl (fun acc r => acc + r.steps) 0
    let sumFail := results.foldl (fun acc r => acc + r.commutativityFailures) 0
    let maxFail := results.foldl (fun acc r => max acc r.commutativityFailures) 0
    let normal := results.filter (fun r => r.steps == 0) |>.length
    { totalFunctions := total,
      totalPreserved := preserved,
      totalChanged := changed,
      avgSteps := sumSteps.toFloat / total.toFloat,
      avgFailures := sumFail.toFloat / total.toFloat,
      maxFailures := maxFail,
      alreadyNormal := normal }

/-- Print rewrite analysis results. -/
def printRewriteStats (stats : RewriteStats) : IO Unit := do
  IO.println "\n╔══════════════════════════════════════════════════════════════"
  IO.println "  重写系统分析（论文定义 3.53 的有限半群具体化）"
  IO.println "══════════════════════════════════════════════════════════════"
  IO.println s!"函数总数: {stats.totalFunctions}"
  IO.println s!"已在正规形（无需重写）: {stats.alreadyNormal}"
  IO.println s!"重写后函数不变（可交换）: {stats.totalPreserved}"
  IO.println s!"重写后函数改变（不可交换）: {stats.totalChanged}"
  IO.println s!"平均重写步数: {stats.avgSteps}"
  IO.println s!"平均交换失败次数（异常累积）: {stats.avgFailures}"
  IO.println s!"最大交换失败次数: {stats.maxFailures}"
  IO.println "╚══════════════════════════════════════════════════════════════"

/-- Print details of interesting normalization examples. -/
def printExamples (n : Nat) (results : List (NormalizationResult n)) : IO Unit := do
  -- Show examples where function is preserved (zero anomaly)
  let preserved := results.filter (fun r => r.functionPreserved && r.steps > 0)
  IO.println s!"\n=== 零异常示例（重写保持函数不变）==="
  for r in preserved.take 3 do
    IO.println s!"  原始词: {Pretty.wordString r.originalWord} → {Pretty.opString r.originalOp}"
    IO.println s!"  正规形: {Pretty.wordString r.normalForm} → {Pretty.opString r.normalFormOp}"
    IO.println s!"  步数={r.steps}, 逆序={r.totalInversions}, 失败={r.commutativityFailures}"

  -- Show examples where function changed (non-zero anomaly)
  let changed := results.filter (fun r => !r.functionPreserved)
  IO.println s!"\n=== 正异常示例（重写改变了函数）==="
  for r in changed.take 5 do
    IO.println s!"  原始词: {Pretty.wordString r.originalWord} → {Pretty.opString r.originalOp}"
    IO.println s!"  正规形: {Pretty.wordString r.normalForm} → {Pretty.opString r.normalFormOp}"
    IO.println s!"  步数={r.steps}, 逆序={r.totalInversions}, 失败={r.commutativityFailures}"

end Rewrite
end Omega.HyperKernel

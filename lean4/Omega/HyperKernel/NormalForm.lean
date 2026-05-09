/-
  HyperKernel.NormalForm
  ~~~~~~~~~~~~~~~~~~~~~~
  Formalization of Proposition 3.56 (接口正规形):
  "任意三生成元投影词都可重写为 LIFT ∘ PROJ ∘ E"

  In the finite semigroup T_n, we verify:
  1. Which functions can be reached by "sorted words" (g0...g0 g1...g1 g2...g2)?
  2. For each function, what is the shortest sorted word that generates it?
  3. How does the sorted-word reachability relate to the anomaly signature?

  A sorted word corresponds to the paper's normal form: all LIFT gates first,
  then PROJ gates, then E gates.
-/
import Omega.HyperKernel.Op
import Omega.HyperKernel.Closure
import Omega.HyperKernel.Analysis
import Omega.HyperKernel.Pretty

namespace Omega.HyperKernel
namespace NormalForm

open Analysis

/-- Generate all sorted words of length ≤ maxLen over 3 generators.
    A sorted word has form: g0^a · g1^b · g2^c with a+b+c ≤ maxLen. -/
def allSortedWords (maxLen : Nat) : List (List Nat) :=
  let triples := (List.range (maxLen + 1)).flatMap fun a =>
    (List.range (maxLen + 1 - a)).flatMap fun b =>
      (List.range (maxLen + 1 - a - b)).filterMap fun c =>
        if a + b + c > 0 then
          some (List.replicate a 0 ++ List.replicate b 1 ++ List.replicate c 2)
        else none
  triples

/-- Compute the function for each sorted word. Returns (word, resulting_op). -/
def sortedWordDict (n : Nat) (gens : List (Op n)) (maxLen : Nat) :
    List (List Nat × Op n) :=
  let words := allSortedWords maxLen
  words.map (fun w => (w, applyWord n gens w))

/-- For a given target operation, find the shortest sorted word that generates it.
    Returns None if no sorted word of length ≤ maxLen generates the target. -/
def shortestSortedWord (n : Nat) (gens : List (Op n)) (maxLen : Nat) (target : Op n) :
    Option (List Nat) :=
  let dict := sortedWordDict n gens maxLen
  let hits := dict.filter (fun (_, op) => op == target)
  match hits with
  | [] => none
  | _ =>
    let sorted := Pretty.insertSort (fun a b => a.1.length < b.1.length) hits
    sorted.head?.map Prod.fst

/-- Result of normal form analysis for a single function. -/
structure NormalFormResult (n : Nat) where
  op : Op n
  bfsWord : List Nat             -- BFS shortest word
  bfsLength : Nat
  sortedWord : Option (List Nat) -- shortest sorted (normal form) word
  sortedLength : Option Nat
  reachableBySorted : Bool       -- can this function be reached by a sorted word?
  lengthOverhead : Option Nat    -- sorted length - BFS length (cost of normalization)
  rankValue : Nat
  defect : Nat

/-- Analyze the whole dictionary for normal form reachability. -/
def analyzeNormalForms
    (n : Nat)
    (gens : List (Op n))
    (dict : Closure.Dict n)
    (maxLen : Nat) :
    List (NormalFormResult n) :=
  -- Pre-compute all sorted word results
  let swDict := sortedWordDict n gens maxLen
  dict.map (fun (op, bfsW) =>
    let hits := swDict.filter (fun (_, sop) => sop == op)
    let best := match hits with
      | [] => none
      | _ =>
        let sorted := Pretty.insertSort (fun a b => a.1.length < b.1.length) hits
        sorted.head?.map Prod.fst
    let sLen := best.map List.length
    let overhead := sLen.map (· - bfsW.length)
    { op := op,
      bfsWord := bfsW,
      bfsLength := bfsW.length,
      sortedWord := best,
      sortedLength := sLen,
      reachableBySorted := best.isSome,
      lengthOverhead := overhead,
      rankValue := rank op,
      defect := n - rank op })

/-- Statistics over normal form analysis. -/
structure NormalFormStats where
  totalFunctions : Nat
  reachableBySorted : Nat
  unreachable : Nat
  reachableRate : Float
  avgOverhead : Float
  maxOverhead : Nat
  zeroOverhead : Nat              -- functions where sorted word = BFS word length

def computeNFStats (results : List (NormalFormResult n)) : NormalFormStats :=
  let total := results.length
  let reachable := results.filter (·.reachableBySorted) |>.length
  let unreachable := total - reachable
  let overheads := results.filterMap (·.lengthOverhead)
  let sumOH := overheads.foldl (· + ·) 0
  let maxOH := overheads.foldl max 0
  let zeroOH := overheads.filter (· == 0) |>.length
  let avgOH := if overheads.length > 0
    then sumOH.toFloat / overheads.length.toFloat
    else 0
  { totalFunctions := total,
    reachableBySorted := reachable,
    unreachable := unreachable,
    reachableRate := if total > 0
      then reachable.toFloat / total.toFloat * 100
      else 0,
    avgOverhead := avgOH,
    maxOverhead := maxOH,
    zeroOverhead := zeroOH }

/-- Print normal form analysis. -/
def printNFStats (stats : NormalFormStats) : IO Unit := do
  IO.println "\n╔══════════════════════════════════════════════════════════════"
  IO.println "  正规形分析（论文命题 3.56 的有限半群具体化）"
  IO.println "══════════════════════════════════════════════════════════════"
  IO.println s!"函数总数: {stats.totalFunctions}"
  IO.println s!"可达（存在排序词生成）: {stats.reachableBySorted}"
  IO.println s!"不可达: {stats.unreachable}"
  IO.println s!"可达率: {stats.reachableRate}%"
  IO.println s!"排序词长度零开销（最优正规形）: {stats.zeroOverhead}"
  IO.println s!"平均长度开销: {stats.avgOverhead}"
  IO.println s!"最大长度开销: {stats.maxOverhead}"
  IO.println "╚══════════════════════════════════════════════════════════════"

/-- Print examples of reachable/unreachable functions. -/
def printNFExamples (n : Nat) (results : List (NormalFormResult n)) : IO Unit := do
  -- Reachable with zero overhead
  let zeroOH := results.filter (fun r =>
    r.reachableBySorted && r.lengthOverhead == some 0 && r.bfsLength > 0)
  IO.println s!"\n=== 最优正规形（排序词 = BFS 最短词长度）==="
  for r in zeroOH.take 3 do
    IO.println s!"  {Pretty.opString r.op}: BFS={Pretty.wordString r.bfsWord}, 排序={Pretty.wordString (r.sortedWord.getD [])}"

  -- Reachable with overhead
  let posOH := results.filter (fun r =>
    match r.lengthOverhead with | some o => o > 0 | none => false)
  IO.println s!"\n=== 有开销正规形（排序词比 BFS 更长）==="
  for r in posOH.take 3 do
    IO.println s!"  {Pretty.opString r.op}: BFS 长={r.bfsLength}, 排序长={r.sortedLength.getD 0}, 开销={r.lengthOverhead.getD 0}"
    IO.println s!"    rank={r.rankValue}, defect={r.defect}"

  -- Unreachable
  let unreach := results.filter (fun r => !r.reachableBySorted)
  IO.println s!"\n=== 排序词不可达的函数 ==="
  if unreach.isEmpty then
    IO.println "  （全部函数均可由排序词到达）"
  else
    for r in unreach.take 5 do
      IO.println s!"  {Pretty.opString r.op}: rank={r.rankValue}, defect={r.defect}, BFS={Pretty.wordString r.bfsWord}"

  -- By rank breakdown
  IO.println "\n=== 按秩的可达率 ==="
  for rankVal in List.range (n + 1) do
    let byRank := results.filter (fun r => r.rankValue == rankVal)
    if !byRank.isEmpty then
      let reach := byRank.filter (·.reachableBySorted) |>.length
      let rate := reach.toFloat / byRank.length.toFloat * 100
      IO.println s!"  rank={rankVal}: {reach}/{byRank.length} 可达 ({rate}%)"

end NormalForm
end Omega.HyperKernel

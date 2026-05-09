import Std
import Omega.HyperKernel.Op
import Omega.HyperKernel.Closure
import Omega.HyperKernel.Pretty

namespace Omega.HyperKernel
namespace Analysis

def rank (f : Op n) : Nat :=
  f.toList.eraseDups.length

def countGen (w : List Nat) (genIdx : Nat) : Nat :=
  w.filter (· == genIdx) |>.length

def generatorAt (gens : List (Op n)) (idx : Nat) : Option (Op n) :=
  match gens with
  | [] => none
  | g :: gs =>
      if idx = 0 then some g else generatorAt gs (idx - 1)

def applyWord (n : Nat) (gens : List (Op n)) (w : List Nat) : Op n :=
  w.foldl (fun acc i =>
    match generatorAt gens i with
    | some g => Op.comp n g acc
    | none => acc
  ) (Op.id n)

def rankDropsAlongWord (n : Nat) (gens : List (Op n)) (w : List Nat) : Nat :=
  let rec go (cur : Op n) (curRank : Nat) (rest : List Nat) (acc : Nat) : Nat :=
    match rest with
    | [] => acc
    | i :: is =>
        match generatorAt gens i with
        | none =>
            go cur curRank is acc
        | some g =>
            let nxt := Op.comp n g cur
            let r := rank nxt
            let acc' := if r < curRank then acc + 1 else acc
            go nxt r is acc'
  go (Op.id n) n w 0

/-- Dictionary entry for BFS with tracked singular-count dimension. -/
abbrev SingState (n : Nat) := Op n × Nat
abbrev SingDist (n : Nat) := List (SingState n × Nat)

def stateLookup (n : Nat) (dist : SingDist n) (s : SingState n) : Option Nat :=
  dist.find? (fun p => p.1.1 == s.1 && p.1.2 == s.2) |>.map Prod.snd

def stateErase (n : Nat) (dist : SingDist n) (s : SingState n) : SingDist n :=
  dist.filter (fun p => ¬ (p.1.1 == s.1 && p.1.2 == s.2))

def stateSet (n : Nat) (dist : SingDist n) (s : SingState n) (d : Nat) : SingDist n :=
  (s, d) :: stateErase n dist s

def stateSetIfBetter (n : Nat) (dist : SingDist n) (s : SingState n) (d : Nat) : SingDist n × Bool :=
  match stateLookup n dist s with
  | some old =>
      if d < old then
        (stateSet n dist s d, true)
      else
        (dist, false)
  | none =>
      (stateSet n dist s d, true)

/-- BFS in `(op, singularCount)` space, tracking minimal word length. -/
partial def stateDistancesWithSingularBudget
    (n : Nat)
    (gens : List (Op n))
    (singularIdx : Nat)
    (maxSingular : Nat) :
    SingDist n :=
  let start : SingDist n := [((Op.id n, 0), 0)]
  let rec bfs (queue : List (SingState n × Nat)) (dist : SingDist n) : SingDist n :=
    match queue with
    | [] => dist
    | (s, d) :: rest =>
        let (op, singularUsed) := s
        match stateLookup n dist s with
        | some known =>
            if known < d then
              bfs rest dist
            else
              let rec expand
                  (gs : List (Op n))
                  (idx : Nat)
                  (distAcc : SingDist n)
                  (qAcc : List (SingState n × Nat)) :
                  SingDist n × List (SingState n × Nat) :=
                match gs with
                | [] => (distAcc, qAcc)
                | g :: gsTail =>
                    let nextSingular :=
                      if idx = singularIdx then singularUsed + 1 else singularUsed
                    if nextSingular > maxSingular then
                      expand gsTail (idx + 1) distAcc qAcc
                    else
                      let nextState : SingState n := (Op.comp n g op, nextSingular)
                      let (dist', pushed) := stateSetIfBetter n distAcc nextState (d + 1)
                      let qAcc' :=
                        if pushed then qAcc ++ [ (nextState, d + 1) ] else qAcc
                      expand gsTail (idx + 1) dist' qAcc'
              let (dist', newStates) := expand gens 0 dist []
              bfs (rest ++ newStates) dist'
        | none =>
            bfs rest dist
  bfs start start

def shortestLengthWithSingularCount
    (n : Nat)
    (d : SingDist n)
    (op : Op n)
    (k : Nat) :
    Option Nat :=
  stateLookup n d (op, k)

def pruneParetoBySingular (pairs : List (Nat × Nat)) : List (Nat × Nat) :=
  let rec loop (best : Option Nat) (acc : List (Nat × Nat)) : List (Nat × Nat) → List (Nat × Nat)
    | [] => acc
    | (k, l) :: ps =>
        match best with
        | none =>
            loop (some l) ((k, l) :: acc) ps
        | some b =>
            if l < b then
              loop (some l) ((k, l) :: acc) ps
            else
              loop (some b) acc ps
  loop none [] pairs |>.reverse

def paretoBySingular
    (n : Nat)
    (d : SingDist n)
    (op : Op n)
    (kMax : Nat) :
    List (Nat × Nat) :=
  let collected :=
    (List.range (kMax + 1)).foldl
      (fun acc k =>
        match shortestLengthWithSingularCount n d op k with
        | some l => (k, l) :: acc
        | none => acc
      ) []
  pruneParetoBySingular (collected.reverse)

def findSingularIndex (n : Nat) (gens : List (Op n)) : Nat :=
  let rec go (idx : Nat) (xs : List (Op n)) : Nat :=
    match xs with
    | [] => 0
    | g :: gs =>
        if rank g < n then idx else go (idx + 1) gs
  go 0 gens

/-- Per-function analysis record with time and irreversibility metrics. -/
structure FunctionAnalysis (n : Nat) where
  op : Op n
  word : List Nat
  wordLength : Nat
  rankValue : Nat
  defect : Nat
  rankDropCount : Nat
  singularCount : Nat
  excessOverDefect : Nat
  shortestWithDefect : Option Nat
  deltaFromShortest : Option Nat
  g0Count : Nat
  g1Count : Nat
  g2Count : Nat

def analyzeFn
    (n : Nat)
    (gens : List (Op n))
    (singularIdx : Nat)
    (d : SingDist n)
    (op : Op n)
    (w : List Nat) :
    FunctionAnalysis n :=
  let r := rank op
  let dlt := rankDropsAlongWord n gens w
  let s : Nat := n - r
  let sc : Nat := countGen w singularIdx
  let exactDefect := shortestLengthWithSingularCount n d op s
  let delta := exactDefect.map (fun l => l - w.length)
  {
    op := op
    word := w
    wordLength := w.length
    rankValue := r
    defect := s
    rankDropCount := dlt
    singularCount := sc
    excessOverDefect := sc - s
    shortestWithDefect := exactDefect
    deltaFromShortest := delta
    g0Count := countGen w 0
    g1Count := countGen w 1
    g2Count := countGen w 2
  } 

/-- Analyze the whole closure dictionary. -/
def analyzeDict
    (n : Nat)
    (gens : List (Op n))
    (singularIdx : Nat)
    (d : SingDist n)
    (dict : Closure.Dict n) :
    List (FunctionAnalysis n) :=
  dict.map (fun (op, w) => analyzeFn n gens singularIdx d op w)

structure HypothesisResult (n : Nat) where
  matching : Nat
  total : Nat
  counterExamples : List (FunctionAnalysis n)

structure Statistics where
  totalFunctions : Nat
  avgWordLength : Float
  maxWordLength : Nat
  avgRank : Float
  avgDefect : Float
  avgG0Count : Float
  avgG1Count : Float
  avgG2Count : Float
  diameter : Nat

def deltaFailures {n : Nat} (analyses : List (FunctionAnalysis n)) : List (FunctionAnalysis n) :=
  analyses.filter (fun a =>
    match a.deltaFromShortest with
    | some 0 => false
    | none => false
    | some _ => true)

/-- Verify hard lower-bound relation: `singularCount >= defect`. -/
def verifyDefectHypothesis {n : Nat} (analyses : List (FunctionAnalysis n)) : HypothesisResult n :=
  let total := analyses.length
  let counterExamples := analyses.filter (fun a => a.singularCount ≠ a.defect)
  let matching := total - counterExamples.length
  { matching := matching, total := total, counterExamples := counterExamples }

/-- Legacy g2-based check kept for backward compatibility. -/
def verifyLegacyG2Hypothesis {n : Nat} (analyses : List (FunctionAnalysis n)) : HypothesisResult n :=
  let total := analyses.length
  let counterExamples := analyses.filter (fun a => a.g2Count ≠ a.defect)
  let matching := total - counterExamples.length
  { matching := matching, total := total, counterExamples := counterExamples }

def computeStats (analyses : List (FunctionAnalysis n)) : Statistics :=
  let total := analyses.length
  if total = 0 then
    { totalFunctions := 0, avgWordLength := 0, maxWordLength := 0,
      avgRank := 0, avgDefect := 0, avgG0Count := 0, avgG1Count := 0,
      avgG2Count := 0, diameter := 0 }
  else
    let sumLength := analyses.foldl (fun acc a => acc + a.wordLength) 0
    let sumRank := analyses.foldl (fun acc a => acc + a.rankValue) 0
    let sumDefect := analyses.foldl (fun acc a => acc + a.defect) 0
    let sumG0 := analyses.foldl (fun acc a => acc + a.g0Count) 0
    let sumG1 := analyses.foldl (fun acc a => acc + a.g1Count) 0
    let sumG2 := analyses.foldl (fun acc a => acc + a.g2Count) 0
    let maxLen := analyses.foldl (fun acc a => max acc a.wordLength) 0
    { totalFunctions := total
      avgWordLength := sumLength.toFloat / total.toFloat
      maxWordLength := maxLen
      avgRank := sumRank.toFloat / total.toFloat
      avgDefect := sumDefect.toFloat / total.toFloat
      avgG0Count := sumG0.toFloat / total.toFloat
      avgG1Count := sumG1.toFloat / total.toFloat
      avgG2Count := sumG2.toFloat / total.toFloat
      diameter := maxLen
    }

/-- rank distribution: counts by rank. -/
def rankDistribution (analyses : List (FunctionAnalysis n)) : List (Nat × Nat) :=
  let grouped :=
    analyses.foldl (fun acc a =>
      let r := a.rankValue
      match acc.find? (fun p => p.1 == r) with
      | some _ => acc.map (fun p => if p.1 == r then (p.1, p.2 + 1) else p)
      | none => (r, 1) :: acc
    ) []
  Pretty.insertSort (fun a b => a.1 < b.1) grouped

def avgLengthByRank (analyses : List (FunctionAnalysis n)) : List (Nat × Float) :=
  let byRank :=
    analyses.foldl (fun acc a =>
      let r := a.rankValue
      match acc.find? (fun p => p.1 == r) with
      | some (_, sum, cnt) =>
          acc.map (fun p => if p.1 == r then (p.1, sum + a.wordLength, cnt + 1) else p)
      | none => (r, a.wordLength, 1) :: acc
    ) ([] : List (Nat × Nat × Nat))
  byRank.map (fun (r, sum, cnt) => (r, sum.toFloat / cnt.toFloat))
    |> Pretty.insertSort (fun a b => a.1 < b.1)

def printStats (n : Nat) (stats : Statistics) : IO Unit := do
  IO.println "\n╔════════════════════════════════════════════════════════════════"
  IO.println "  统计分析"
  IO.println "═════════════════════════════════════════════════════════════════"
  IO.println s!"状态空间大小: n = {n}"
  IO.println s!"函数总数: {stats.totalFunctions}"
  IO.println s!"平均词长: {stats.avgWordLength}"
  IO.println s!"直径（最大词长）: {stats.diameter}"
  IO.println s!"\n平均 rank: {stats.avgRank}"
  IO.println s!"平均 defect (n-rank): {stats.avgDefect}"
  IO.println s!"\n平均 g0 次数: {stats.avgG0Count}"
  IO.println s!"平均 g1 次数: {stats.avgG1Count}"
  IO.println s!"平均 g2 次数: {stats.avgG2Count}"

def printRankDist (dist : List (Nat × Nat)) : IO Unit := do
  IO.println "\n══════════════════════════════ Rank 分布 ══════════════════════════════"
  for (r, count) in dist do
    IO.println s!"rank={r}: {count} 个函数"

def printAvgLengthByRank (data : List (Nat × Float)) : IO Unit := do
  IO.println "\n══════════════════════════ 各 rank 的平均词长 ══════════════════════════"
  for (r, avgLen) in data do
    IO.println s!"rank={r}: 平均词长 = {avgLen}"

def printDefectVerification {n : Nat} (result : HypothesisResult n) : IO Unit := do
  IO.println "\n════════════════════════════════════════════════════════════════════════"
  IO.println "  [假设验证]singular-count == defect?"
  IO.println "════════════════════════════════════════════════════════════════════════"
  IO.println s!"匹配数: {result.matching}/{result.total}"
  if result.total = 0 then
    IO.println "  无可评估样本"
  else
    let rate := (result.matching.toFloat / result.total.toFloat * 100)
    IO.println s!"匹配率: {rate.floor.toUInt64}%"
  if result.counterExamples.isEmpty then
    IO.println "\n✓ 假设完全成立！所有函数都满足 singular-count = defect。"
  else
    IO.println s!"\n⚠  发现 {result.counterExamples.length} 个反例："
    for ex in result.counterExamples.take 10 do
      IO.println s!"  {Pretty.opString ex.op}: rank={ex.rankValue}, defect={ex.defect}, singular={ex.singularCount}, word={Pretty.wordString ex.word}"

end Analysis
end Omega.HyperKernel

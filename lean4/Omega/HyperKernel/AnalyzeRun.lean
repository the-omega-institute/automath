import Std
import Omega.HyperKernel.Spec
import Omega.HyperKernel.Op
import Omega.HyperKernel.Enum
import Omega.HyperKernel.AutoSeed
import Omega.HyperKernel.Closure
import Omega.HyperKernel.Pretty
import Omega.HyperKernel.Analysis
import Omega.HyperKernel.Rewrite
import Omega.HyperKernel.NormalForm
import Omega.HyperKernel.Run

namespace Omega.HyperKernel
namespace AnalyzeRun

open Analysis
open Pretty
open Run

def banner : String :=
"============================================================\n" ++
"  HyperKernel - 深度结构分析\n" ++
"  从最小核到研究级系统\n" ++
"============================================================"

def run : IO Unit := do
  let n := Spec.n
  let universeSize := Enum.universeSize n

  IO.println banner
  IO.println s!"状态空间大小: n = {n}"
  IO.println s!"宇宙大小: {universeSize}"
  IO.println ""

  IO.println "正在搜索最小生成器集合..."
  match AutoSeed.findMinGenerators n Spec.maxSeedSize with
  | none =>
      IO.println s!"✗ 在 maxSeedSize={Spec.maxSeedSize} 内未找到可生成整宇宙的生成元集合。"
  | some (k, gensFound) =>
      IO.println s!"✓ 找到最小生成器数量: {k}"
      IO.println ""
      let gens := sortOps gensFound
      let singularIdx := findSingularIndex n gens

      IO.println "生成器列表:"
      for (i, g) in Run.enum gens do
        let r := Analysis.rank g
        IO.println s!"  g{i} = {opString g}  (rank={r}, defect={n-r})"
      IO.println s!"奇异生成元索引(按列表): g{singularIdx}"
      IO.println ""

      IO.println "计算闭包..."
      let dict := Closure.closureDict n gens universeSize
      IO.println s!"✔ 闭包大小: {dict.length}"
      let singDist := stateDistancesWithSingularBudget n gens singularIdx n

      -- 分析阶段
      IO.println "\n开始深度结构分析..."
      let analyses := analyzeDict n gens singularIdx singDist dict
      
      -- 统计信息
      let stats := computeStats analyses
      printStats n stats
      
      -- Rank 分布
      let rankDist := rankDistribution analyses
      printRankDist rankDist
      
      -- 每个 rank 的平均长度
      let avgByRank := avgLengthByRank analyses
      printAvgLengthByRank avgByRank
      
      -- 验证 singular-count = defect
      let result := verifyDefectHypothesis analyses
      printDefectVerification result
      
      -- Delta 统计：最短时间实现相对于最小singular下界的代价
      let deltaSamples := analyses.filterMap (fun a => a.deltaFromShortest)
      if deltaSamples.length = 0 then
        IO.println "\n无可比对的 delta 样本（可能未建立有限的奇异预算界）。"
      else
        let d0 := deltaSamples.filter (fun x => x = 0) |>.length
        let dPos := deltaSamples.length - d0
        IO.println "\n================= Δ 统计 ================="
        IO.println s!"delta 样本数: {deltaSamples.length}"
        IO.println s!"Δ = 0: {d0}"
        IO.println s!"Δ > 0: {dPos}"

      -- 展示几个有趣的样本
      IO.println "\n=== 典型样本 ==="
      
      match analyses.find? (fun a => a.wordLength == 0) with
      | some id =>
          IO.println s!"单位元: {opString id.op}"
          IO.println s!"  rank={id.rankValue}, defect={id.defect}, singular={id.singularCount}"
      | none => pure ()
      
      -- 直径函数
      let diameter := analyses.foldl (fun acc a => max acc a.wordLength) 0
      let farthest := analyses.filter (fun a => a.wordLength == diameter)
      IO.println s!"\n最远函数（直径={diameter}）:"
      for f in farthest.take 3 do
        IO.println s!"  {opString f.op}: rank={f.rankValue}, defect={f.defect}"
        IO.println s!"    singular 出现{f.singularCount}次, 词={wordString f.word}"
        match f.deltaFromShortest with
        | some d => IO.println s!"    Δ={d}"
        | none => IO.println "    Δ=none"
      
      -- 按 defect 分组的代表样本
      IO.println "\n按 defect 的代表函数："
      for defectVal in List.range (n + 1) do
        match analyses.find? (fun a => a.defect == defectVal) with
        | some ex =>
            IO.println s!"  defect={defectVal}: {opString ex.op}"
            IO.println s!"    rank={ex.rankValue}, |w|={ex.wordLength}, singular={ex.singularCount}"
            IO.println s!"    word={wordString ex.word}"
            match ex.deltaFromShortest with
            | some d => IO.println s!"    Δ={d}"
            | none => IO.println "    Δ=none"
        | none => pure ()
      
      -- ═══════════════════════════════════════════════════════════
      -- 重写系统分析（论文定义 3.53）
      -- ═══════════════════════════════════════════════════════════
      IO.println "\n\n╔══════════════════════════════════════════════════════════"
      IO.println "  Phase 2: 重写系统分析（论文定义 3.53 的有限半群具体化）"
      IO.println "══════════════════════════════════════════════════════════"

      let rewriteResults := Rewrite.analyzeRewriting n gens dict
      let rewriteStats := Rewrite.computeRewriteStats rewriteResults
      Rewrite.printRewriteStats rewriteStats
      Rewrite.printExamples n rewriteResults

      -- ═══════════════════════════════════════════════════════════
      -- 正规形分析（论文命题 3.56）
      -- ═══════════════════════════════════════════════════════════
      IO.println "\n\n╔══════════════════════════════════════════════════════════"
      IO.println "  Phase 3: 正规形分析（论文命题 3.56 的有限半群具体化）"
      IO.println "══════════════════════════════════════════════════════════"

      -- Use diameter + 2 as max length for sorted word search
      let maxSearchLen := diameter + 2
      IO.println s!"搜索排序词的最大长度: {maxSearchLen}"

      let nfResults := NormalForm.analyzeNormalForms n gens dict maxSearchLen
      let nfStats := NormalForm.computeNFStats nfResults
      NormalForm.printNFStats nfStats
      NormalForm.printNFExamples n nfResults

      IO.println "\n============================================================"
      IO.println "全部分析完成！"

end AnalyzeRun
end Omega.HyperKernel

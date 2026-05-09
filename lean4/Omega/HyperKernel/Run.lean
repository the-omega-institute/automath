import Std
import Omega.HyperKernel.Spec
import Omega.HyperKernel.Op
import Omega.HyperKernel.Enum
import Omega.HyperKernel.AutoSeed
import Omega.HyperKernel.Closure
import Omega.HyperKernel.Pretty

namespace Omega.HyperKernel
namespace Run

def enumFrom (start : Nat) (xs : List α) : List (Nat × α) :=
  match xs with
  | [] => []
  | x :: xs => (start, x) :: enumFrom (start+1) xs

def enum (xs : List α) : List (Nat × α) :=
  enumFrom 0 xs

def banner : String :=
"═══════════════════════════════════════════════════\n" ++
"  HyperKernel - 自动代数结构发现系统（纯 标准库版）\n" ++
"═══════════════════════════════════════════════════"

def run : IO Unit := do
  let n := Spec.n
  let universeSize := Enum.universeSize n

  IO.println banner
  IO.println s!"状态空间大小: n = {n}"
  IO.println s!"宇宙大小（所有可能的函数）: {universeSize}"
  IO.println ""

  IO.println "正在搜索最小生成器集..."
  match AutoSeed.findMinGenerators n Spec.maxSeedSize with
  | none =>
      IO.println s!"✗ 在 maxSeedSize={Spec.maxSeedSize} 内未找到可生成全宇宙的生成器集。"
  | some (k, gensFound) =>
      IO.println s!"✓ 找到最小生成器数量: {k}"
      IO.println ""
      let gens := Pretty.sortOps gensFound

      IO.println "生成器列表:"
      for (i, g) in enum gens do
        IO.println s!"  g{i} = {Pretty.opString g}"
      IO.println ""

      IO.println "计算闭包和最小单词..."
      let dict := Closure.closureDict n gens universeSize
      IO.println s!"✓ 闭包大小: {dict.length}"
      IO.println ""

      IO.println "═══ 每个操作符的最小单词表达式（按字典序 排列）═══"
      IO.println "格式: [函数表] | 长度 | 表达式"
      IO.println "───────────────────────────────────────────────────"

      let pairs := Pretty.sortPairs dict
      for (op, w) in pairs do
        IO.println s!"{Pretty.opString op}  |w|={w.length}  {Pretty.wordString w}"

      IO.println "═══════════════════════════════════════════════════"
      IO.println "✓ 完成！"

end Run
end Omega.HyperKernel

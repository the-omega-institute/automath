import Std
import Omega.HyperKernel.Op
import Omega.HyperKernel.Enum
import Omega.HyperKernel.Closure

namespace HyperKernel
namespace AutoSeed

/-- 组合枚举：从 `xs` 中取 `k` 个元素的所有组合（保持原列表顺序）。-/
def choose (k : Nat) (xs : List α) : List (List α) :=
  match k, xs with
  | 0, _ => [[]]
  | _+1, [] => []
  | k+1, x :: xs =>
      let withX := (choose k xs).map (fun ys => x :: ys)
      let withoutX := choose (k+1) xs
      withX ++ withoutX

/-- 在候选列表里找第一个能覆盖全宇宙的生成器集。-/
def firstGood (n : Nat) (targetFuel : Nat) (targetSize : Nat)
    (cands : List (List (Op n))) : Option (List (Op n)) :=
  match cands with
  | [] => none
  | g :: gs =>
      if Closure.closureSize n g targetFuel == targetSize then
        some g
      else
        firstGood n targetFuel targetSize gs

/-- 在宇宙中搜索一个**最小大小**的生成器集合，使其闭包覆盖整个宇宙。  
返回 `(k, gens)`：`k` 为最小生成器数量，`gens` 为找到的第一组（由宇宙枚举顺序决定）。-/
def findMinGenerators (n maxK : Nat) : Option (Nat × List (Op n)) :=
  let U := Enum.allOps n
  let targetSize := U.length
  let targetFuel := targetSize
  let rec scan (k : Nat) (remaining : Nat) : Option (Nat × List (Op n)) :=
    match remaining with
    | 0 => none
    | Nat.succ r =>
        match firstGood n targetFuel targetSize (choose k U) with
        | some gens => some (k, gens)
        | none      => scan (k+1) r
  scan 1 maxK

end AutoSeed
end HyperKernel

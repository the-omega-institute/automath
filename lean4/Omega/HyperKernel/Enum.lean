import Std
import Omega.HyperKernel.Op

namespace HyperKernel
namespace Enum

/-- 生成所有长度为 `len` 的 base-`n` 数字串（每位在 `[0,n-1]`），按字典序**降序**枚举。-/
def enumListsDesc (n len : Nat) : List (List Nat) :=
  match len with
  | 0 => [[]]
  | len + 1 =>
      let tails := enumListsDesc n len
      let digits := (List.range n).reverse
      digits.flatMap (fun d => tails.map (fun t => d :: t))

/-- 宇宙：所有 `Fin n → Fin n` 的函数表（大小应为 `n^n`），按字典序**降序**枚举。-/
def allOps (n : Nat) : List (Op n) :=
  (enumListsDesc n n).map (fun xs => xs.toArray)

/-- 宇宙大小。-/
def universeSize (n : Nat) : Nat :=
  (allOps n).length

end Enum
end HyperKernel

import Std
import Omega.HyperKernel.Op

namespace HyperKernel
namespace Closure

abbrev Word := List Nat

/-- 使用关联列表代替 HashMap（更简单，更兼容）。-/
abbrev Dict (n : Nat) := List (Op n × Word)

/-- 字典取值（缺省为空词）。-/
def dictGet (dict : Dict n) (k : Op n) : Word :=
  match dict.find? (fun p => p.1 == k) with
  | some (_, v) => v
  | none => []

/-- 字典插入（如果已存在则不覆盖）。-/
def dictInsert (dict : Dict n) (k : Op n) (v : Word) : Dict n :=
  if dict.any (fun p => p.1 == k) then
    dict
  else
    (k, v) :: dict

/-- 检查是否包含某个键。-/
def dictContains (dict : Dict n) (k : Op n) : Bool :=
  dict.any (fun p => p.1 == k)

/-- 从一个 `cur` 扩张一步（按生成器顺序），返回更新后的字典与本层新发现节点（保持顺序）。-/
def addNeighbors (n : Nat)
    (gens : List (Op n)) (cur : Op n) (curW : Word)
    (dict : Dict n)
    : Dict n × List (Op n) :=
  let rec loop (idx : Nat) (gs : List (Op n))
      (dict : Dict n) (newRev : List (Op n))
      : Dict n × List (Op n) :=
    match gs with
    | [] => (dict, newRev.reverse)
    | g :: gs =>
        let nxt := Op.comp n g cur
        if dictContains dict nxt then
          loop (idx+1) gs dict newRev
        else
          let w := curW ++ [idx]
          let dict' := dictInsert dict nxt w
          loop (idx+1) gs dict' (nxt :: newRev)
  loop 0 gens dict []

/-- BFS 闭包：从 `id` 出发，对每个可达算子给出一条**最短词**（作用量=长度）。  
    `fuel` 是安全上界：每处理一个队首节点消耗 1。对有限宇宙取 `fuel = universeSize` 即可。 -/
def closureDict (n : Nat) (gens : List (Op n)) (fuel : Nat) : Dict n :=
  let start := Op.id n
  let dict0 : Dict n := [(start, [])]
  let rec go (fuel : Nat) (queue : List (Op n)) (dict : Dict n)
      : Dict n :=
    match fuel, queue with
    | 0, _ => dict
    | _, [] => dict
    | fuel+1, cur :: rest =>
        let curW := dictGet dict cur
        let (dict', newNodes) := addNeighbors n gens cur curW dict
        go fuel (rest ++ newNodes) dict'
  go fuel [start] dict0

def closureSize (n : Nat) (gens : List (Op n)) (fuel : Nat) : Nat :=
  (closureDict n gens fuel).length

end Closure
end HyperKernel

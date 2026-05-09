import Std
import Omega.HyperKernel.Op

namespace HyperKernel
namespace Pretty

/-- 字典序比较（Nat 列表）。-/
def lexCmp : List Nat -> List Nat -> Ordering
  | [], [] => .eq
  | [], _  => .lt
  | _ , [] => .gt
  | a::as, b::bs =>
      if a < b then .lt
      else if a > b then .gt
      else lexCmp as bs

/-- 算子表的字典序比较。-/
def cmpOp (a b : Op n) : Ordering :=
  lexCmp a.toList b.toList

def ltOp (a b : Op n) : Bool :=
  cmpOp a b == .lt

/-- `[0,1,2]` 形式打印算子表。-/
def opString (op : Op n) : String :=
  let elems := op.toList.map (fun x => toString x)
  "[" ++ String.intercalate "," elems ++ "]"

/-- 词（生成器序列）打印：`g0·g2·g1`，空词为 `ε`。-/
def wordString (w : List Nat) : String :=
  match w with
  | [] => "ε"
  | _ =>
      let parts := w.map (fun i => s!"g{i}")
      String.intercalate "·" parts

/-- 简单插入排序（适用于小列表）。-/
def insertSort {α : Type} (le : α → α → Bool) : List α → List α
  | [] => []
  | x :: xs =>
    let rec insert (y : α) : List α → List α
      | [] => [y]
      | z :: zs => if le y z then y :: z :: zs else z :: insert y zs
    insert x (insertSort le xs)

/-- 按算子表字典序升序排序。-/
def sortPairs (xs : List (Op n × List Nat)) : List (Op n × List Nat) :=
  insertSort (fun a b => ltOp a.1 b.1) xs

def sortOps (xs : List (Op n)) : List (Op n) :=
  insertSort (fun a b => ltOp a b) xs

end Pretty
end HyperKernel

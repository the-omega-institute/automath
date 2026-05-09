import Std

namespace HyperKernel

/-- 语义算子：用长度为 n 的表 `[f(0), f(1), ..., f(n-1)]` 表示一个函数 `Fin n → Fin n`。
    这里直接用 `Array Nat`，并约定生成/组合过程中始终保持：
    - `table.size = n`
    - `table[i] < n`
    这使整个系统完全有限且可枚举。 -/
abbrev Op (n : Nat) := Array Nat

namespace Op

/-- 恒等算子 `[0,1,2,...,n-1]`。-/
def id (n : Nat) : Op n :=
  Array.ofFn (fun i : Fin n => i.val)

/-- 取值：越界时回落到 0（在本系统生成的算子中不会越界）。-/
@[inline] def get (op : Op n) (i : Nat) : Nat :=
  op.getD i 0

/-- 复合：`(g ∘ f)(i) = g(f(i))`。-/
def comp (n : Nat) (g f : Op n) : Op n :=
  Array.ofFn (fun i : Fin n =>
    let x := f.get i.val
    g.get x)

end Op
end HyperKernel

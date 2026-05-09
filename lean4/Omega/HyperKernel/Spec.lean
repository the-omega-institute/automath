namespace HyperKernel
namespace Spec

/-- 状态空间大小 n（默认 3，可自行修改后重新编译）。
    唯一输入：约束本身（写在代码里）。 -/
def n : Nat := 4

/-- 搜索最小生成器集合时允许的最大大小。 -/
def maxSeedSize : Nat := 5

end Spec
end HyperKernel

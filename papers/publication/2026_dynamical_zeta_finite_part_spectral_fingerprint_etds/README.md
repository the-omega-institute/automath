# H. Dynamical ζ Finite Part and Spectral Fingerprint

**方向代号：** H
**论文标题（工作标题）：** 动力学 ζ 函数有限部与谱指纹：从 SFT 语法到扭曲 Chebotarev 等分布
**English title (working):** Dynamical ζ-Function Finite Part and Spectral Fingerprint: From SFT Syntax to Twisted Chebotarev Equidistribution

## 目标期刊

| 优先级 | 期刊 | 理由 |
|---|---|---|
| 首选 | ETDS (Ergodic Theory and Dynamical Systems) | 动力系统顶刊 |
| 高风险高回报 | Journal of the European Mathematical Society | 若谱指纹新意足够 |
| 回退 | Nonlinearity | 若 ETDS desk reject |

## 核心材料

- `zeta_finite_part/syntax/`（4 files, 836 lines）
- `zeta_finite_part/online_kernel/`（11 files, 2822 lines）
- `zeta_finite_part/operator/`（8 files, 1446 lines）
- `zeta_finite_part/finite_part/`（27 files, 5149 lines）

## 核心内容主线

SFT/sofic 上的转移算子/行列式 → 周期轨道计数 → 有限部常数 → 扭曲 Chebotarev 等分布 → Peter-Weyl 非阿贝尔通道化

## 拆法

- 只用 syntax + online_kernel + operator + finite_part 四个子目录
- **完全不包含** `xi/` 目录（889 files, 262k lines）——留给论文 J

## 上游依赖

- F（POM 核心，强依赖）

## 下游被依赖

- J（ζ-completion，强依赖；H 是 J 的必要前驱）

## 对上游主论文的补全/修正建议

以下内容来自本次对主论文源材料的回溯梳理；本发表稿已吸收这些结果，但未直接改动上游源文件。

- 建议把 `finite_part` 中的循环 lift 谱显微镜上升为主定理链，而不是只作为局部技术段落。最核心的链条应明确写成：
  `C(M^{\langle q\rangle})` 闭式公式
  `->` `q` 轴上的倍数求和展开与 M\"obius 反演
  `->` 全序列确定约化谱多项式
  `->` 单一 `q` 层 torsion shell 在 `q \ge d` 时直接重建约化谱。
- 建议在 `operator` 部分把“循环块 Fredholm 实现”与“谱刚性”并排写成一对正反向结果：
  一个给存在性，一个给唯一性层面的非零谱强迫。
- 建议把
  `F_M(t)=\det(I-tM/\rho)/(1-t)`、
  `\Psi_q(M)=\log q+\log C(M^{\langle q\rangle})`、
  `\Lambda_{\mathrm{rel}}(M)=\max_{j\ge 2}|\mu_j|/\rho`
  三个记号提前统一定义。这样后续关于常数层、扭点采样和谱恢复的陈述会明显更干净。
- 建议把两层恢复结论明确区分开：
  全 `q` 轴常数序列 `->` 幂和序列 `->` 约化谱多项式；
  单一 `q` 层扭点数据加上 `C(M)` `->` 离散 Fourier 反演 `->` 直接恢复约化谱。

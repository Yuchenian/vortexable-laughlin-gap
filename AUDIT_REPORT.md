> **AI-assisted research draft — human verification and independent peer review are incomplete.** New proof claims remain provisional. See [HUMAN_REVIEW.md](HUMAN_REVIEW.md).

# Vortexable 1/3-Laughlin 母哈密顿量：审查报告

日期：2026-10-16。原始版本已完整保存在 `audit_20261016/originals/`；旧证明和两个旧检查脚本均未覆盖。此为一次有否证倾向的解析审查、分离实现与原始文献核验，不是外部人工同行审稿。

## 最强结论

在原稿明确的几何与假设内，没有找到推翻其通道迁移或三个例子的反例。原稿的核心可以补成自足证明，并有所加强：平面和球面均可用 **C=14**，双环境项在一般有界二体 frame 下为 **βδ²**。原 `C=20/28` 常数与原三个分数下界仍有效。

比改常数更实质的扩展是用 `Q_(|f|⁴)>=kappa Q` 的可核验二体 coercivity 代替逐点下界。由此获得光滑、有零线的真实周期子空间 `f=2cos(kx)cos(ky)`，普通导数接触母相互作用下有 **gap >0.1763**。还给出非标准 vortex coordinate 的周期保面积 shear，其普通物理导数接触有 **gap >=1/5**，不要求 shear 振幅小。完整模型/单位/零模/几何限制见 `EXAMPLES_AND_BOUNDS.md`。

这些结论没有扩大成“所有 vortexable bands 均有隙”，也没有把完整平面正谱下界说成有限 torus 的目标简并以上的 gap。

## 外部输入和证据等级

1. 已直接查阅 Gao [arXiv:2610.12700v1](https://arxiv.org/html/2610.12700v1)：Theorem 1.1 的球面全 Fock 不等式、Corollary 1.3 的完整平面结论、无序 pair 投影系数 1 的归一化。`gamma*=1401624220840445441298243497/6400000000000000000000000000 ≈0.2190037845063196`，因此可取 1/5。球面阈值 Q0 不依赖 N，但要求 Q 充分大；没有把平面极限换成 finite torus。
2. 下载的作者 `certificate.json` SHA256 与正文所列值一致。已检查作者 `verify.py` 的执行内容并独立重跑：33 个三体 block、四体 D=1..53、尾界与 PSD allowance 的精确检查全部通过，退出码 0。原件与日志保存在 `audit_20261016/literature/`。
3. 这核实了原文陈述及其发布证书的可复现性；并非独立重写 SDP verifier，也不是把文献中所有解析归约形式化验证。关于参考谱隙的使用仍依赖所引用论文的解析定理与归约。
4. 第二篇 arXiv:2610.18854v1 和 vortexability 原文/相关表示与 gap-stability 文献也已查阅；适用条件和未验证事项统一记录在 `LITERATURE_AUDIT.md`。未将第二篇文献作为替代证书输入。

## 逐条主张审查

| 原主张或风险点 | 状态 | 审查证据、修复与限制 |
|---|---|---|
| `Phi_M(H0)=HM` | 支持 | 正规序 pair 的环境湮灭腿杀真空；完整复系数 CAR 解析与精确复有理数分块一致 |
| `Phi_M(H0²)=HM²+X1†X1+X2†X2` | 支持 | 作用环境真空后只出现 0、1、2 粒子正交扇区；graded parity 逐块跟踪 |
| 由 CP 得参考不等式 | 支持，必须全 Fock 输入 | b 模式的粒子数可为 0..N；不能只拿 Laughlin 固定 N gap；Kadison 方向不反转 |
| `X2†X2<=δ²HM` | 投影 frame 下支持 | synthesis S 范数平方为 β；一般版必须 `βδ²HM`，已有删除 β 的精确反例 |
| `X1†X1<=CδHM` | 支持且改进 | E 先作为单粒子算符整体提出，CAR 给系统 creation 范数；算符值 Schur 界不含 N |
| 只凭过滤后 overlap 仍局域 | 不允许 | 证明始终使用未过滤单粒子 overlap；没有假设任意 M/E 保持 Gaussian locality |
| plane frame 对所有 K 为投影 | 补齐证明 | 用二项分布二阶矩恒等式证明全部 K；K=1..40 的检查不是证明 |
| sphere frame 对所有 Q 归一 | 支持 | SU(2) coherent resolution，测度 `(2Q−1)dg`；Q=1 端点单独处理 |
| C_plane=20，C_sphere=28 | 均为有效保守界 | 二框 overlap 的 nuclear norm 核给两个几何统一 `C<8sqrt(3)<14` |
| 无限维域与 Fock 闭包 | 补齐严格表述 | 每个固定总粒子数子空间上先以有界二体 lift 定义，Schur/synthesis 有界延拓，再作全 Fock 直和；无角动量 cutoff 猜极限 |
| `U=fG^(-1/2)` | 支持并扩大 | 对闭像，只需 G 在参考 h0 上一致可逆；不必 ambient 乘法逆有界 |
| 真实接触权重为 f⁴ | 实 f 情形支持 | 从物理投影场出发，`f'` 项乘 `chi²=0`；复 f 时为 `\|f\|⁴`；具体接触归一化已补写 |
| 正比较给 gap | 支持 | 先证明共同 kernel，再在其补空间比较；没有平方 Loewner 不等式 |
| kernel 完整迁移 | 可逆 M 下支持 | 每个 N 的 `wedge^N M^(-1)` 只用于代数识别；未用其指数条件数估计 gap |
| 周期例子的一带/填充 | 加明几何限制 | 一磁通可交换磁平移晶胞 rank=1；填充按 N/N_phi；更小调制周期不能直接当普通单带晶胞 |
| 所有 vortexability 推出 gap | 不成立为本稿结论 | 缺 uniform Gram/local frame/coercivity/global geometry；已给若干不能删除条件的反例 |
| 多轨道求导仍自动消项 | 仅 input rank=1 支持 | rank>1 时显式出现 `chi_mu chi_nu`；归一化 rank-one texture 只是等距嵌入 |
| 任意坐标换元可直接搬 gap | 错误 | 正确接触权重为 `J\|\|DF\|\|_F²/2`，Jacobian、测度与导数均已跟踪 |

完整解析推导见 `TRANSFER_THEOREM_REVISED.md` 和 `ANALYTIC_AUDIT.md`；物理求导、零点、orbital 与坐标例子见 `PHYSICAL_EXTENSIONS.md`。

## 独立计算与主动反例

分离第二实现直接在 2d 个 CAR 模式上构造 `H(b)|0_env>`，与旧脚本的外幂 Stinespring 实现不同。它覆盖同时复数的 frame 和非对角 M、近奇异过滤、非投影与非正交 frame、Slater rank 2，包含精确复有理数检查。51 个浮点全 Fock 实例的最大恒等式残差约 `8.53e-13`；浮点 Loewner 容差明确记录，不能当成严格 PSD 证书。

找到并保存的失败证据：

* 删去 β：两模式、frame 权重 3 的精确例使 `X2†X2/(δ²HM)=3`。
* 删去 M 可逆性：`M=diag(0,1)` 使 pair Hamiltonian 消失，kernel 维数由 3 增至 4。
* 原数值 kernel 阈值：最小 M 本征值为 `1e-6` 的可逆例，数学 kernel 维数为 5，而固定 `1e-9` 阈值报告 8；这是诊断算法失效，原定理没有被反驳。

原两个脚本复跑与既有结果一致。新脚本、随机种子、环境、源码哈希、每次原始输出及一键命令见 `NUMERICAL_AUDIT.md`。测试数是检查覆盖记录，不是用测试替代一般证明。

## 归一化与无隐藏尺寸因子

* plane pair 测度是 `d²R/(pi ell²)`，不是单粒子的 `d²R/(2pi ell²)`；sphere 是 `(2Q−1)dg`。
* Fock creation/annihilation 范数为单粒子向量范数，费米 CAR 不产生 `sqrt(N)`。
* 单环境用参考 overlap 的行/列 Schur 积分；没有对全部 x 标签求绝对总和。
* 双环境用二体 synthesis 的算符范数 β；没有以标签数/轨道数替代它。
* 全 Fock 结论来自固定 N 上同一个常数，再作直和；未隐藏面积、Q 或角动量 cutoff。
* 正权重/二体 coercivity 比较同一 kernel；没有把不同 kernel 的正算符比较误用为 gap 比较。

## 原稿需保留的限制与新增限制

原稿的主要路线未发现最早失效的一步；其不完整处在于一般 K 证明、无限维细节、物理接触归一化及文献证书复跑，这些已补充。它不能扩张到的地方有明确定位：非投影时双环境 synthesis 引入 β；singular M 时零模映射失去可逆性；input rank>1 时场求导多出非零项；一般坐标换元多出几何权重。

原例子的零模/正谱结论可以保留，并使用更强常数。新 nodal 例子是扩大模型类；rank-one orbital texture 是等距重写；shear 是真正超出 standard-z scalar LLL 的几何构造，同时保留其可明确追踪的等价结构。这三者的结论强度不能混为一谈。

仍未完成：finite torus 的统一参考与接触 frame 认证；全部 C=1 vortexable bands 的定量覆盖定理；投影后准局域性及有隙相稳定性；一般矩阵 rank>1 的合适 Laughlin 类母相互作用。本次不宣布这些结论，也不把已发表多磁通 dielectric 讨论当成单磁通例子的直接反例。

所有新结论有清楚的适用类与可复核证明，不声称新颖性已得到文献穷尽证明。

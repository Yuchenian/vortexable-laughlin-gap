> **Review status updated 2026-10-24.** The author reports personally checking the main conclusions and calculations. See [HUMAN_REVIEW.md](HUMAN_REVIEW.md) and the [follow-up audit](RECHECK_20261024.md).

# 原始文献与外部证书审查

审查日期：2026-10-16（Asia/Shanghai）。这是本次独立文献子审查；未修改原始草稿。原文已通过 web 工具读取，并将能够取得的原始 HTML/PDF、附件、哈希与运行日志保存在 `audit_20261016/literature/`。

## 结论与证据等级

草稿使用的 **γ₀=1/5 外部输入有真实、匹配归一化的来源**，并且本次已经独立重跑 Gao 随文发布的精确有理数验证器，退出码为 0。可使用的结论是完整平面各有限粒子数扇区整个 kernel 以上的统一正谱下界，以及充分大球面全 Fock 空间的不等式。它不提供任意有限 torus 的目标三重基态谱隙。

这里区分三个层次：(i) 原文陈述与适用范围已核对；(ii) 原作者证书程序已在本机重跑；(iii) 本次**没有**独立重写原 SDP 验证器、重新证明全部球面有限尺寸比较引理或执行 Lean formalization。采用这一外部定理仍是普通数学论文的引用依赖；不能把证书运行成功描述为本项目完成了外部定理的独立形式化证明。

## 1. 外部输入、版本和归一化

| 来源 | 版本、日期和准确位置 | 本项目可使用的内容 |
|---|---|---|
| Qiang Gao, *Improving the lower bound on the Laughlin gap: An SDP search* | [arXiv:2610.12700v1](https://arxiv.org/html/2610.12700v1)，[提交记录](https://arxiv.org/abs/2610.12700)：2026-10-08 20:31:55 UTC；§1.1，Theorem 1.1，Corollaries 1.2–1.3 | `H_N,Q=Σ_{i<j}P_ij^(1)`，每个无序对的投影系数为 1；`Q` 为磁通数，单粒子维数 `Q+1`。`γ*=1401624220840445441298243497/(64·10^26)>1/5`。Theorem 1.1 是每个 `0<γ<γ*` 均有与 `N` 无关的 `Qγ`，当 `Q≥Qγ` 时在整个 `⊕_{N=0}^{Q+1}∧^N U_Q` 上 `H_Q²≥γH_Q`。阈值是存在性结论。Cor.1.2 在 `Q=3(N−1)` 使用唯一 Laughlin 零模。Cor.1.3 对每个 `N≥2` 的未截断平面给出 `H_N²≥γ*H_N`，对总角动量一致。 |
| Michael G. Scheer and Eslam Khalaf, *A hierarchy of exact lower bounds on the Laughlin spectral gap* | [arXiv:2610.18854v1](https://arxiv.org/html/2610.18854v1)，[提交记录](https://arxiv.org/abs/2610.18854)：2026-10-13 17:59:10 UTC；§I.3，§II Eqs.(4)–(8)，§III，§IV.2 | `s=NΦ/2`；`V1=1`；CG pair annihilator 的双重求和含 `1/√2`，因此与无序对投影归一化一致。§I.3 区分数值 `0.0693` 与声称将发布的 `1/100` 精确证书；§III 专门处理 `t=1/NΦ→0` 的 rank stability。§IV.2 没有证明非均匀场或 torus 推广。它不是 `γ₀=1/5` 的来源。 |
| Ledwith, Vishwanath and Parker, *Vortexability: A Unifying Criterion for Ideal Fractional Chern Insulators* | [arXiv:2209.15023v3](https://arxiv.org/html/2209.15023v3)，[版本史](https://arxiv.org/abs/2209.15023)：v1 2022-09-29，v2 2022-10-09，v3 2024-04-19；[PRB 108, 205144 (2023)](https://doi.org/10.1103/PhysRevB.108.205144) | §II Eq.(2) 是 `P ζψ=ζψ`；Eq.(5) 要求 vortex metric 的两个本征值统一上下有界，故坐标非退化。§III 构造短程母相互作用零模，不证明统一 many-body gap。附录 E Props.1–4 分别涉及平移、holomorphic gauge、vortex function 唯一性及旋转限制；这些不是“所有 vortexable 子空间均为有统一小条件数的 scalar-LLL”定理。 |

日期检查：2610.18854 的 abs 页面和下载的正文 HTML 都标记 **2026-10-13**，早于用户当前日期 2026-10-16；本次没有发现该文的未来日期矛盾。2209.15023 的期刊年份与 arXiv v3 年份不同，应分别记录。不要由 arXiv 流水号反推出提交日。

## 2. Gao 原证书：实际复核结果

取得以下原始附件，均未修改：

- [certificate.json](https://arxiv.org/src/2610.12700v1/anc/certificate.json)
- [verify.py](https://arxiv.org/src/2610.12700v1/anc/verify.py)
- [README.md](https://arxiv.org/src/2610.12700v1/anc/README.md)
- [SHA256SUMS.txt](https://arxiv.org/src/2610.12700v1/anc/SHA256SUMS.txt)

本机计算的 SHA-256 与作者清单逐字一致：

```text
certificate.json b9a94d46c8a90e0206d98b700712686d3f2bc2725efcadab3e6513759abbba81
verify.py        ded1fd1769185bae6df52c95f144832c71c7cfe13d9c36de5556b0f3ec848a45
```

审读 `verify.py` 后确认它只读取证书，使用 Python 标准库的整数与 `Fraction` 运算；不调用 SDP solver，不联网。实际使用 Python **3.14.7**，命令如下（在项目目录运行）：

```powershell
Set-Location '<project-root>\audit_20261016\literature'
& 'python' -u .\verify.py .\certificate.json
```

独立运行输出保存在 `verify_rerun_20261016.log`，末尾有 `process_exit_code=0`。本次运行结果：

- 64 行证书，分母 `10^13`，`T3=35`、`T4=53`。
- 33 个三体 margin 全部严格正；最小值的浮点显示约 `1.999993674496054e−8`，通过判定实际使用有理数。
- 四体 `D=1,…,53` 的实对称矩阵，所有特征多项式系数非负。
- 尾界 `271/4294967296`，allowance `59808781/2500000000000`。
- 重算常数精确等于 `1401624220840445441298243497/6400000000000000000000000000`。
- 作者程序耗时 31.6 秒，最终 `RESULT: PASS`。

本审查的数学解释：对实对称 `M`，若 `det(tI+M)` 的首项为正且其余系数非负，则该多项式对 `t>0` 严格正，所以 `M` 无负本征值。这解释该验证器的 PSD 判据，不依赖浮点最小本征值。证书中的有限 orbital 集只是外部解析比较定理的辅助算符支撑；它不是把最终多体模型截断到这些 orbitals。

Scheer–Khalaf 的 [v1 source archive](https://arxiv.org/src/2610.18854v1) 也已下载并列出全部成员：`00README.json, fig.pdf, main.bbl, main.tex`。该包没有证书数据或 verifier。**该文原始证书独立重跑未完成：目前取得的 source archive 未提供它。** 不把正文将来时的发布说明写成已取得证书。

## 3. 球面到平面的极限次序

除 Gao §6 的 Cor.1.3 证明外，还取得其依赖的 [OpenAI 原稿 PDF（2026-09-24）](https://github.com/openai/math/blob/main/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf)，核读 §7 / Corollary 7.1，正文第 16–17 页，并渲染第 17 页对照公式。

极限先固定 `N` 和总 degree `L`。当 `Q≥max{L,N−1,2}` 时，将有限维的 spherical lowering-deficit `L` 块与 planar degree `L` 块识别；矩阵逐项收敛给出算符范数收敛。对固定 `γ<γ*` 先让 `Q→∞`，再 `γ↑γ*`；随后对 `L` 取 Hilbert direct sum。每个固定 `N` 上 `0≤H_N≤binom(N,2)I`，因此无需假定一个在所有 `N` 上有限的全 Fock 算符范数。

本审查的推论：将这些固定 `N` 的一致不等式再作正算符直和，可得到全 Fock 的谱不等式，但全 Fock Hamiltonian 一般无界，应使用其自然直和定义域或二次型意义。这里没有交换 `N∼Q/3` 和局部平面极限，也没有证明平面到有限 torus 的逆推。平面 quasihole 零模仍属于 kernel；这与球面 Laughlin flux 的唯一零模结论不同。

## 4. 表示结果与能覆盖到哪里

[Estienne–Regnault–Crépel, arXiv:2304.01251v2](https://arxiv.org/html/2304.01251v2)（v2 2023-07-15；[PRResearch 5, L032048](https://doi.org/10.1103/PhysRevResearch.5.L032048)）给出需纳入推广图的表示结果。其 Eq.(2)、“Real-space condition”与附录讨论 periodic `C=1` / 一磁通晶胞，在 isothermal coordinate `Z=F(r)` 中写成 `ψ_k(r)≡e^(−ρ̃(F(r)))φ_k(F(r))/N_k`。Jacobian 出现在内积，且边界 sewing phase 也需跟踪。该工作没有谱隙迁移常数；“equivalent Landau level”允许非均匀度量和磁场。

[Guerci–Wang–Mora, arXiv:2408.12652v1](https://arxiv.org/html/2408.12652v1)，Eq.(1)及§II，说明 ideal `C=1` 的 layer-spinor 分解与磁边界相位补偿。在单 Dirac moiré 情形，非零归一 spinor 承担实空间 skyrmion 结构；普通无零点 scalar 无法独立实现该相位补偿。本审查只把它用作表示和边界条件的证据，不把它当作所有 multiorbital vortexable spaces 的统一覆盖定理。

由此得到的本项目审查要求（独立分析，而非上述论文已证明的新谱隙结论）：

1. 光滑周期且处处正的 scalar 权重在固定晶胞上确实有上下界，但这不保证 Gram 条件数接近 1。若随系统尺寸改变权重，必须要求这些界一致。
2. 对 nonlinear `F`，必须变换测度、导数及母相互作用。直接把普通实验室坐标下的 `V1` 留在原样不属于纯坐标等价。
3. 有界可逆 scalar 表示与小噪声条件是不同假设；由表示结果不能跳到所有 ideal bands 有隙。
4. 从 rank-one 输入到多分量 fiber 的 `T(r)`，共同 scalar annihilator 可能使某些导数项消失，但应从每一个物理接触通道重新验证。该表示与真正多输入分量/更高 band rank 不同。
5. 对非周期、奇异权重、无统一双 Lipschitz 坐标、非平凡 bundle 的一般问题，本次文献不足以提供所需全局统一界。状态为“未覆盖”，不能写成已证明不存在其他表示。

## 5. 2509.18265 的反例边界

[Moitra–Sodemann Villadiego, arXiv:2509.18265v1](https://arxiv.org/html/2509.18265v1) 的提交记录为 2025-09-22；[正式发表版 PRB 113, L161102](https://journals.aps.org/prb/pdf/10.1103/3y87-96dw) 于 2026-04-01 发表。两版内容有差别，审查采用正式发表版的边界说明。其 Eqs.(1)–(4) 是 `m` 磁通/晶胞的周期 solenoid 场，填充 `1/m` 时每晶胞平均一个电子。Eqs.(10)–(14) 通过 plasma/cluster expansion 讨论代数关联与 dielectric regime。第 L161102-4 页明确把一磁通/晶胞情形列为开放问题；同页展开以 `σ/a≪1, 1/m≪1` 为控制参数，指数恢复还使用重指数化。本次未独立补齐其引用的全部 plasma 收敛证明，也未取得正式版独立 supplementary attachment。

因此：它是反对“vortexability 或精确零模自动推出有隙”的直接相关文献证据；不能把其结果升级为本项目一磁通弱形变家族的严格 gap-closing 反例。利用代数关联反推无隙，还要核查所讨论 Hamiltonian 的 locality、热力学态及 exponential-clustering 定理的前提；尤其不能把平面整个 kernel 的 gap 与给定热力学态的 GNS gap 自动等同。

附带版本警示：arXiv v1 HTML 内部显示的稿件日期是 2026-08-24，而版本史是 2025-09-22；本报告不推断这一差异的原因，以 arXiv 版本史和期刊发表日期分别标识。

## 6. 既有稳定性定理：目前为何不能直接替代迁移证明

| 原始来源 | 实际前提 / 结论位置 | 本项目尚须另证的接口 |
|---|---|---|
| [Bravyi–Hastings–Michalakis, arXiv:1001.0344](https://arxiv.org/abs/1001.0344) | 局域量子自旋 lattice、commuting projectors、topological-order 条件下的局域微扰稳定性 | 投影 LLL `V1` 的 pair terms 一般不对易，不能直接套用。 |
| [Michalakis–Zwolak/Pytel, arXiv:1109.1588, Theorem 1](https://arxiv.org/html/1109.1588) | frustration-free、已知 gap、Local-TQO 和 Local-Gap；小的准局域相互作用范数微扰 | 需给出适用的局域代数/相互作用分解，并证明 LTQO、local gap 和微扰范数的尺寸一致界；全 Fock 正谱下界本身不足以完成这些前提。 |
| [Nachtergaele–Sims–Young, arXiv:2102.07209v3](https://arxiv.org/html/2102.07209v3)，Assumptions 2.1–2.6、Theorems 2.8–2.9 | bulk GNS gap 稳定性；有限作用范围初始 interaction、局域 gap 可按幂次衰减、LTQO 和 stretched-exponential 微扰 | 这避免强求有限体积 uniform gap，但仍需指定无限体积态、GNS 表示及局域假设；不是从有限粒子 Fock gap 自动推出同相性。 |

本审查未发现这些定理可在不补前提的情况下直接推出草稿所有几何结论。此检索不是新颖性证明。可主张的新增内容若成立，应是针对明确投影母相互作用的显式相对噪声控制、常数或覆盖范围，而非“首次证明一般谱隙稳定性”。

## 7. 证据索引与未完成项

`audit_20261016/literature/` 中主要证据：

- `download_manifest.json`、`download_manifest_extra.json`：完整 source URLs、下载状态、文件长度与 SHA-256。
- 原始论文 `*.html`、`*_abs.html`，以及原始 PDF 两份。
- `certificate.json`、`verify.py`、`gao_anc_README.md`、`gao_anc_SHA256SUMS.txt`、`verify_rerun_20261016.log`。
- `2610.18854v1_source.gz` 与 `2610.18854_source_members.txt`：没有证书附件的实查记录。
- `OpenAI_planar-17.png`、`PRB_counterexample-4.png`：关键页公式和版本差异的视觉复核。
- `COMMANDS_AND_STATUS.md`、`reproduce_gao_certificate.ps1`：真实命令、环境失败记录和可重复运行入口。

未核实项目：Gao 的完整原证明独立重证 / Lean 重跑；Scheer–Khalaf 的原始精确证书；Moitra–Sodemann 正式版独立 supplement 与全部 plasma 依赖链；任意有限 torus 一致参考 gap；对无额外全局正则性的一般 vortexable space 的全覆盖结论。

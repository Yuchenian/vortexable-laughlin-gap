> **Historical candidate snapshot; human review incomplete.** Consult the current root documents for revised claims. Local machine paths have been redacted in this public copy.

# Vortexable Laughlin gap — first analytic transfer attempt

项目路径：`<project-root>`

## 当前结果

本轮没有新跑大规模 SDP，而是尝试迁移 arXiv:2610.12700 的现有全 Fock 谱隙证书。得到了一份完整候选证明：通过 fermionic vacuum-loss channel，将单粒子 Gram 过滤产生的误差界为 `(C delta + delta^2) H`。这避免了多体过滤的指数条件数。

对 `hf=f hLLL`, `G=P0 f^2 P0`，在 `m<=f^2`, `g_- I<=G<=g_+ I` 下，候选充分条件为

`Delta_f >= (m/g_-)^2 [1/5 - C delta - delta^2]`, `delta=1-g_-/g_+`.

C=20 适用于完整平面 V1；C=28 对球面磁通一致。结论仍须独立审查，不能称为已独立验证的论文级定理。

具体解析下界：

| 几何/形变 | 下界 |
|---|---:|
| 平面双方向第一谐波，`f^2=1+0.01(cos(qx)+cos(qy))/2`, `q^2 lB^2=2pi` | 0.1143265782 |
| 平面双方向第二谐波，振幅 0.5，`q^2 lB^2=8pi` | 0.04008913018 |
| 球面任意光滑形状，`\|f_Q^2-1\|<=0.001`，充分大 Q | 0.1440519520 |

这些是解析不等式代入得到的数，不是 ED 外推值。输入单位为每个无序 pair 的 V1 投影系数 1。

## 文件

- `PROOF_DRAFT.md`：完整推导、归一化、三个例子、外部输入、适用范围。
- `channel_transfer_checks.jl`：102 个代数与有限 Fock 检查，含有理数精确恒等式与独立 Stinespring 检查。
- `analytic_bound_checks.jl`：53 个归一化和常数检查，含三个下界的精确分数。
- `RESULTS_20261016.txt`：实际运行输出。
- `AUDIT_CHECKLIST.md`：优先审查点，禁止扩大结论的边界。
- `AGENTS.md`：本项目工作约定。

## 复现

在本目录执行（仅使用 Julia 标准库，不需安装包）：

```powershell
julia --startup-file=no channel_transfer_checks.jl
julia --startup-file=no analytic_bound_checks.jl
```

环境：Windows，Julia 1.12.7。脚本只输出 stdout，不改项目文件。无后台长跑任务。

## 下一步优先级

先独立审查通道迁移证明与真实接触母哈密顿量的对应，再考虑用 SDP 改善 one-environment noise 常数 C。这一阶段不要把有限 ED 检查当作热力学证书，也不要跳到一般 vortexable/C>1/Coulomb/有限 torus 拓扑简并。

> **AI-assisted research draft — human verification and independent peer review are incomplete.** New proof claims remain provisional. See [HUMAN_REVIEW.md](HUMAN_REVIEW.md).

# 独立审查清单

当前工作是候选解析推广。优先检查下列可能推翻结论的点，而不是仅复跑浮点谱。

## 必须通过

1. **外部输入的粒子数范围**：Gao Theorem 1.1 / Corollary 1.3 必须是全 Fock 不等式。只在 Laughlin 固定 N 上的 gap 不够，Gaussian dilation 会把系统粒子数降低。
2. **channel 方向**：Phi(H0^2)>=Phi(H0)^2 不能直接给谱隙。必须保留并控制两个噪声项。代码独立 Stinespring 与精确有理数检验支持恒等式，但一般证明要审查。
3. **复共轭与 graded tensor product**：c(v) 反线性；一个环境粒子项存在费米子排序相位。需确认该相位不改变 R1^*R1，不能只依赖实基计算。
4. **pair frame 的归一化**：平面测度为 d^2R/(pi*lB^2)，而非单粒子测度 d^2R/(2pi*lB^2)。sphere 测度乘 2Q-1。二体 frame operator 必须是投影，norm=1。
5. **R2 的范数**：应使用 ||wedge^2 E||<=delta，随后平方为 delta^2；不应遗漏或多乘一个 2。
6. **R1 的 Schur 界**：环境 E 应先从合成算符整体提出，再用参考 u/v 的 Gaussian overlap 控制核。不能直接假设经过任意 E 后的 overlaps 仍局域。
7. **Fock 扇区一致性**：使用 ||c(v)||=||v|| 的 fermionic bound，不得隐含 N 或空间体积因子。无限维闭包需要在每个固定总粒子数扇区先定义，再以同一常数控制所有 N。
8. **真实物理模型**：hf=f h0 的正交化为 U=fG^(-1/2)，其 projected derivative contact 确实拉回为 f^4 加权的过滤 pair 母相互作用；不是故意选 f^(-4) 反向补偿相互作用的平凡模型。
9. **共同 kernel**：从 Hf>=lambda HM 到 gap 比较必须证明两个 kernel 相同。外幂 M^(-1) 只用于零模空间识别，不得用其指数条件数估计 gap。
10. **plane vs torus**：本稿的周期例子是完整平面算符不等式。不能不加论证就宣布每个有限 torus 的三重简并及 uniform gap。
11. **不同能标**：gamma0=1/5 是 pair-projector units。将结果写成任何实验/微观相互作用单位前必须转换。
12. **定量边界**：仅覆盖正且有界 scalar-multiplied LLL，以及满足条件的 G。不能宣称所有 vortexable bands 都有隙。已有强非均匀理想 Laughlin dielectric/gapless 工作须在定位时比较。

## 已做但不能替代上述审查的测试

- `channel_transfer_checks.jl`: 102/102，包括一个精确有理数完整通道例子、16 个球面随机实过滤、一个复过滤，以及 kernel 映射。
- `analytic_bound_checks.jl`: 53/53，包括规范化、相对常数、解析例子的 exact fractions。
- 未重跑原始 SDP 附件证书；未进行独立人工审稿；未形式化。

## 后续计算的具体切口

若迁移引理通过审查，可把 `||R_M||^2<=20` 的 triangle/Schur 估计替换成利用 Gaussian CAR 的有限局域 SDP+严格尾界，从而扩大允许的 Gram deformation。此时目标函数和必须控制的算符已经明确，不需要直接重建整个 Hf^2 的大规模旋转分块证书。

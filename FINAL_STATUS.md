> **AI-assisted research draft — human verification and independent peer review are incomplete.** New proof claims remain provisional. See [HUMAN_REVIEW.md](HUMAN_REVIEW.md).

# 审查最终状态 — 2026-10-16

**原三个例子经得起本次审查。** 未找到原假设内的通道或物理投影反例；已补全一般 K、复数 graded 符号、无限维域与共同 kernel 的证明。Gao 原文的全 Fock 输入及归一化已核实，原作者精确证书下载后哈希匹配并重跑通过。该过程不是外部独立人工审稿或完整形式化验证。

**平面和球面都可将常数改为 C=14。** 原三个例子的严格下界提高为：

| 例子 | 下界 |
|---|---:|
| 平面第一谐波、1% 振幅 | 0.1390771833942528… |
| 平面第二谐波、50% 振幅 | 0.0430921361842293… |
| 球面任意光滑 0.1% 形变、充分大磁通 | 0.1720239800159880… |

**真正扩大模型类的结果有两个。**

* 光滑含零线的 `f=2cos(kx)cos(ky)`，`k²ell²=2π`：用二体 frame coercivity 取代逐点正下界，得到普通导数接触母哈密顿量的 **gap >0.1763**，并精确保留乘以 f 的整个零模空间。
* 周期保面积 shear `F(x,y)=(x+(a_s/k)sin(ky),y)`：vortex coordinate 为 F_x+iF_y，任意有限 a_s 下普通物理导数接触满足 **gap ≥1/5**。这是带完整 Jacobian/导数计算的几何推广。

抽象定理还覆盖有界非投影 frame、非正交 frame、多个接触通道及可控制的有限 Slater-rank kernels，并给出一个有精确参考 gap 的 rank-two 分离块家族。该家族验证抽象推广，不称为 Laughlin。rank-one 多轨道嵌入的导数消项已核实，但轨道对称相互作用下它是局域等距重写。

**明确的边界：** 非投影时不能删除 β；singular M 不能保留原 kernel 映射；多输入分量矩阵 T 的导数项一般不消失；vortexability 不保证任一给定 scalar 表示的统一 Gram 下界。均有具体反例或计算定位。原数值固定阈值在近奇异过滤处还会误计零模，失败证据已保存。

**仍未证明：** 任意 finite torus 的统一目标 gap；全部 C=1 vortexable bands 的覆盖；一般多输入分量模型；投影后的准局域性及与参考 Laughlin 相的拓扑同相性。完整平面整个 kernel 以上的正谱下界不自动给出这些结论。相关 dielectric 文献也未被误用为本例一磁通模型的严格反例。

推荐继续：给 nodal 周期族建立磁边界与 aspect ratio 明确的 torus 局域 pair frame/overlap 证书，并补独立 torus 参考 gap。对新例子继续扩大 ED 并不能填补此缺口。

阅读入口：`AUDIT_REPORT.md` → `TRANSFER_THEOREM_REVISED.md` → `EXAMPLES_AND_BOUNDS.md`；覆盖限制见 `GENERALIZATION_MAP.md`。原始文献与作者验证日志见 `LITERATURE_AUDIT.md`，内部独立实现及反例见 `NUMERICAL_AUDIT.md`。所有原文件保留在原处并另有快照；一键重跑新旧检查使用 `run_full_audit.ps1`。

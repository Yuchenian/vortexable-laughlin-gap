> **Review status updated 2026-10-24.** The author reports personally checking the main conclusions and calculations. See [HUMAN_REVIEW.md](HUMAN_REVIEW.md) and the [follow-up audit](RECHECK_20261024.md).

# 可核对的模型与严格下界

日期：2026-10-16。下列数值使用已经查阅原文并重跑作者精确证书验证的参考输入 `gamma0=1/5`。本次迁移证明属于本次解析研究推导，非外部独立人工审稿或形式化证明。原始文献、验证边界见 `LITERATURE_AUDIT.md`。

## 统一约定

统计为单组分费米子；输入是一份均匀磁场 LLL，磁长 ell。完整平面每个无序粒子对的相对角动量一投影系数为 1。实际物理相互作用统一取

`H=4 pi ell^4 integral d²r sum_(j=x,y) [Psi partial_j Psi]^*[Psi partial_j Psi]`，

其中 Psi 是指定改变后子空间的正交投影场。归一化推导见 `PHYSICAL_EXTENSIONS.md`。它是局域导数接触的正二次型；不是人为插入 f^(-4) 的补偿相互作用。多轨道例子对 a,b 轨道指标再求和。

除单独标注的球面例子外，gap 是**完整未截断平面、每个有限 N 上整个 kernel 以上的统一正谱下界**。这既保留 Laughlin 零模，也保留 quasihole 零模。其 N 一致性不自动等于有限 torus、固定边界或固定填充目标简并的谱隙定理。以下没有任何 ED 外推数字。

## 原例子复算与常数改善

取 `a=sqrt(2pi)ell`，`q_n=n sqrt(2pi)/ell`，

`f_(epsilon,n)^2=1+(epsilon/2)[cos(q_n x)+cos(q_n y)]`，`0<=epsilon<1`。

子空间 `h_f=f hLLL`，vortex coordinate 为 z，Gram 满足 `||G-I||<=epsilon exp(-q_n²ell²/4)<=alpha`。令 `m=1-epsilon`，`g_-=1-alpha`，`delta=2alpha/(1+alpha)`。修订定理给

`gap >= [m/(1-alpha)]² [1/5-14delta-delta²]`。

| 模型与严格取值 | 原常数给出的下界（复算） | 修订 C=14 的下界 |
|---|---:|---:|
| n=1，epsilon=1/100，alpha=21/10000 | 0.1143265782023963 | `11493880722000/82643899175161` = **0.1390771833942528** |
| n=2，epsilon=1/2，alpha=1/1000 | 0.0400891301782203 | `1164650000/27026972973` = **0.0430921361842293** |
| 球面任意光滑形状，`abs(f_Q²-1)<=1/1000` | C=28：0.1440519520439600 | `861841/5010005` = **0.1720239800159880** |

球面采用归一化 pair spin `Q−1` 的 V1 投影。半径 R 上对应的真实接触为 `c_Q integral dA sum_(j=1,2)|Psi nabla_j Psi|²`，其中 `c_Q=8pi R⁴(2Q−1)/[Q(Q+1)²]`，不是在有限 Q 直接套用平面系数；推导见 `PHYSICAL_EXTENSIONS.md`。参考定理要求 Q 充分大，其阈值不依赖 N。取 `g_-=m=999/1000`，`g_+=1001/1000`，新 Schur 常数 14 对所有 Q≥1 统一，因此迁移不额外引入 Q 阈值。在 `Q=3(N−1)` 序列上零模唯一，故是唯一形变 Laughlin 基态以上的谱隙。

平面周期例子使用边长 a、面积 `2pi ell²` 的一磁通磁晶胞，rank 为 1。高次谐波的更小实空间周期不意味着该更小晶胞就支持一个普通 Bloch 单带；应在可交换的磁平移晶胞描述。填充 1/3 指 `N/N_phi=1/3`，不是简单按任意选取的微小调制晶胞计数。

这些原例子经审查没有被推翻；新增内容首先是常数改善，不能把这一点本身说成扩大了模型类。

## 新例子：含零线、仍有严格正界的二维周期形变

取

`k=sqrt(2pi)/ell`，`f(x,y)=2cos(kx)cos(ky)`，`h_f=f hLLL`。

f 光滑、实且变号，在两组直线上为零；没有 `inf |f|²>0`。仍取同一个真实导数接触相互作用，vortex coordinate 为 z。

`|f|²=(1+cos(2kx))(1+cos(2ky))`。

以 `r=e^(-2pi)<1/500` 得

`alpha=2/500+1/500²=1001/250000`，`(1-alpha)I<=G<=(1+alpha)I`。

二体接触 frame 的中心质量磁长为 `ell/sqrt(2)`，因此其 Fourier form factor 为 `exp(-|q|²ell²/8)`，不能用单粒子的 `/4` 替换。取 `t=e^(-pi)<1/23`，有限 Fourier 和给

`Q_(|f|⁴)>=kappa Q`，
`kappa=9/2-[3/2+2/23+1/(2*23⁴)]²=310356353097/156621970562`。

于是

`gap >= kappa/(1-alpha)² [1/5-14(2alpha/(1+alpha))-(2alpha/(1+alpha))²]`

`=5992934159531101049706250000000/33988053096870625665692548678809`

`=0.1763247262928069... >0.1763`。

即使只用原 C=20，也得到 0.0807302849700025，说明去掉逐点正下界不依赖新的常数改善。这里扩大的是真正的允许形变类别：用可检验的二体 frame coercivity 替代 `inf |f|²>0`。

由于 G 一致可逆，`f hLLL` 为闭子空间，`fG^(-1/2)` 正交化有效。零模恰为 `product_i f(r_i)` 乘以参考整个零模空间，没有新增零模。物理波函数在 f 的零线上消失，并不妨碍此结论；不能用不光滑的 |f| 替换已经光滑的 f 来讨论导数。

该模型在一磁通平方磁晶胞中仍有 rank 1，Laughlin 填充含义相同。它是连续空间磁 C=1 子空间；本文没有构造零平均磁场 moiré 微观单粒子 Hamiltonian，也不把磁 Bloch 标签自动改称零场 Bloch band。

## 非标准 vortex coordinate：任意有限幅度的周期 shear

取 `F(x,y)=(x+(a_s/k)sin(ky),y)`，`k>0`，`a_s` 为任意有限实数。定义

`h_F={phi(F(r)):phi in hLLL}`，`zeta(r)=F_x(r)+iF_y(r)`。

这里 `J=det DF=1`，映射在 L2 中酉。取物理 r 坐标的同一各向同性导数接触。严格链式法则和测度变化给拉回权重

`w_F=J||DF||_F²/2=1+(a_s²/2)cos²(ky)`。

因此 `H_F>=H0` 且共同 kernel 相同，得到

**`gap(H_F)>=1/5`，对所有有限 a_s 及所有有限 N 一致。**

零模为参考 Laughlin/quasihole 波函数的坐标 pullback。`zeta` 对标准 z 非全纯，非零 shear 无法写成全局标量乘以标准 LLL：否则两个轨道的比值应 meromorphic，而该比值正比于 zeta。它确实扩大了 vortex coordinate 的覆盖范围；同时应准确称为一个显式几何构造与接触权重比较，不是全体 vortexable bands 的表示定理。

选 `k=2pi/a`、`a²=2pi ell²` 时，F 对磁周期格子 equivariant。拉回 Landau gauge 与标准 gauge 相差一个周期 exact one-form，能用周期相位移除，故继承一磁通 rank 1 和 C=1。非保面积 F 则必须保留 J；例如 `F=lambda r` 的接触权重为 `lambda⁴`，遗漏 J 会给错能标。

## 多轨道例子及其结论强度

取上一 nodal f，令 `t=f(cos theta,exp(ikx)sin theta)^T`。输入 fiber rank=1，输出 orbital fiber rank=2，磁 band rank=1。轨道对称导数接触

`4pi ell⁴ integral sum_(a,b,j) |Psi_a partial_j Psi_b|²`

拉回权重 `(t†t)²=|f|⁴`，得到相同严格下界 0.1763247262928069。对 t 求导的额外项均为单个标量场的平方，严格为零。

这是局域等距嵌入，保留标量模型的谱；不把它称为新增一般多轨道拓扑序。若输入有两个独立场，导数项不再自动消失，需重新分析。

## 复现与证书性质

运行 `julia --startup-file=no --project=. extension_bound_checks.jl` 可重算本页所有有理数界。保存输出：`audit_20261016/logs/extension_bounds.log`。指数界来自 `pi>157/50` 与有限 Taylor 和，Fourier 和有限，无截断余项；小数仅用于阅读。

Schur 常数的证明用解析积分和严格上界 `8sqrt(3)<14`，浮点积分只作为诊断。原始外部 SDP 的有理证书、SHA256 及重跑日志在 `audit_20261016/literature/`，与本页的迁移/例子证书分开。

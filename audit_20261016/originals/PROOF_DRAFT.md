> **Historical candidate snapshot; human review incomplete.** Consult the current root documents for revised claims. Local machine paths have been redacted in this public copy.

# Vortexable Laughlin 母哈密顿量的谱隙迁移：证明草稿

日期：2026-10-16。

**状态：本轮推导的候选解析推广，已进行独立实现的代数与常数检查，但尚未经独立研究者审查。不是新的 SDP 优化结果，也没有声称完成形式化证明或确认新颖性。**

外部输入是 Gao, arXiv:2610.12700v1, Theorem 1.1 / Corollary 1.3 的全 Fock 空间谱隙结论。我们取保守常数 gamma0=1/5，而不使用其更大的最优证书常数。此次核对了正文定理和归一化；没有独立重跑原论文的附属 SDP 有理数验证程序。

## 1. 要证明的对象

令 h0 为平面均匀磁场 LLL，P0 为其正交投影。取光滑、正且有统一上下界的实函数 f(r)，并定义真正改变后的单粒子子空间

    hf = f h0,     G = P0 f^2 P0 |h0.

它仍满足 z-vortexability，因为 z f phi = f z phi。其自然母哈密顿量是投影到 hf 的、按参考 V1 归一化的导数接触赝势；不是保持 P0 不变后仅调节相互作用。

设

    0 < m <= f(r)^2,
    0 < g_- I <= G <= g_+ I,
    delta = 1 - g_-/g_+.

本草稿推导的充分条件为

    Delta_f >= (m/g_-)^2 [ gamma0 - C delta - delta^2 ],

只要右侧为正。其中：

- 平面完整、未截断的 V1：可取 C=20；较精确的解析常数是 4 sqrt(2 pi)+16 exp(-1/2)=19.731003653926...。
- 球面 V1：可取 C=28，对磁通 Q 一致。只要参考全 Fock 不等式成立，迁移就成立；因此可覆盖充分大球面的热力学极限。

结论中的 gap 是整个零模空间以上的正谱下界。球面在 Q=3(N-1) 时参考零模唯一，故是相应形变 Laughlin 基态以上的 many-body gap。平面不应把包含 quasihole 的整个零模空间误说成唯一基态。

常数均为 pair-projector normalization：每个无序粒子对的相对角动量一投影系数为 1。

## 2. 抽象引理：全 Fock 谱隙在弱单粒子过滤下的迁移

### 2.1 可分解二粒子 frame

在单粒子 Hilbert 空间 h 中，取测度空间 (X,nu) 上的正交归一对 u_x,v_x，令

    p_x = u_x wedge v_x,
    S a = integral p_x a(x) dnu(x),
    h2 = S S^* = integral |p_x><p_x| dnu(x).

假定 h2 是一个正交投影，并令 B(p_x) 为二粒子湮灭算符，

    H0 = integral B(p_x)^* B(p_x) dnu(x) = L2(h2).

定义非负对称标量核

    k(x,y) = |<u_x,u_y>| + |<u_x,v_y>|
           + |<v_x,u_y>| + |<v_x,v_y>|.

假定 Schur 常数

    C = sup_x integral k(x,y) dnu(y)

有限。对称性同时给出列方向的 Schur 界。参考模型满足

    H0^2 >= gamma0 H0

在所有粒子数扇区成立，而非只在一个固定 N 扇区成立。

### 2.2 过滤后的母哈密顿量

取正的单粒子压缩算符 0<M<=I，设

    E = sqrt(I-M^2),      delta_M = ||I-M^2||.

用 c(Mu_x),c(Mv_x) 定义

    B_x^M = c(Mv_x)c(Mu_x),
    HM = integral (B_x^M)^* B_x^M dnu(x).

这里 c(v) 对 v 反线性，c^*(v) 对 v 线性。于是 HM=L2[(wedge^2 M) h2 (wedge^2 M)]。

欲证

    HM^2 >= [gamma0-C delta_M-delta_M^2] HM.        (T)

### 2.3 真空损耗通道：保留算符序的正确方向

引入独立环境费米子 d，并令

    b(v) = c(Mv) + d(Ev).

由于 M^2+E^2=I，b 满足参考 CAR。把参考算符用 b 表示，再在环境真空中取期望，得到完全正、保单位映射 Phi_M。

二体正规序结构给出

    Phi_M(H0) = HM.

注意不能直接用 Kadison 不等式来推出谱隙：Kadison 的方向是 Phi_M(H0^2)>=HM^2。必须定量控制差值。

将 H0(b) 作用于环境真空。输出只包含环境粒子数 0、1、2 三部分：

    H0(b)(psi tensor |0>)
      = HM psi tensor |0> + X1 psi + X2 psi.

三部分正交，故是精确恒等式

    Phi_M(H0^2) = HM^2 + X1^*X1 + X2^*X2.          (V)

另一方面，完全正性与全 Fock 输入不等式给出

    Phi_M(H0^2) >= gamma0 HM.

于是只需证明噪声是相对有界的：

    X1^*X1 + X2^*X2 <= (C delta_M+delta_M^2) HM.  (R)

### 2.4 两个环境粒子的噪声

定义 pair-analysis 映射

    (A_M psi)(x) = B_x^M psi,
    ||A_M psi||^2 = <psi,HM psi>.

两个环境粒子的部分为

    X2 = [(wedge^2 E) S tensor I] A_M,

忽略一个不影响范数的固定费米子排序约定。由于

    ||S||^2 = ||h2|| = 1,
    ||wedge^2 E|| <= ||E||^2 = delta_M,

得到

    X2^*X2 <= delta_M^2 HM.

这里没有粒子数 N 或单粒子维数因子。

### 2.5 一个环境粒子的噪声

先把环境腿上的 E 提出。剩余 synthesis 算符 R_M 的列为

    (R_M)_x = u_x tensor c^*(Mv_x)
             -v_x tensor c^*(Mu_x).

因此

    X1 = (E tensor I) R_M A_M.

其 Gram 核 (R_M)_x^*(R_M)_y 含四项：每项是一个参考单粒子重叠，乘两个过滤后的系统费米子算符。费米 CAR 给出

    ||c(Mu_x)|| <= ||Mu_x|| <=1,
    ||c(Mv_x)|| <=1.

所以该算符值核的范数至多 k(x,y)。算符值 Schur test 给出

    ||R_M||^2 <= C,
    X1^*X1 <= C delta_M HM.

与上一节合并得到 (R)，再代入 (V) 得到 (T)。这一步是避免原先多体过滤条件数指数增长的关键。

### 2.6 无限单粒子 Hilbert 空间的适用范围

上述推导先在 frame 标签和态的稠密有限线性组合上理解。Schur 界使 R_M 有界，S S^*=h2 使 S 有界。对任意固定有限 N，二体投影之和 H0 在 0..N 粒子扇区上有界，而费米 Gaussian dilation 保持系统加环境的总粒子数。因此可在这些扇区上取闭包并应用 CP 不等式。

全 Fock 输入覆盖损耗产生的全部粒子数扇区。证明没有先固定角动量 cutoff 再据连续性猜测热力学极限。

若 h2 不是投影而仅满足 ||h2||<=beta，则同一证明的二环境项为 beta delta_M^2 HM；本文具体应用的 beta=1。

## 3. 平面 LLL frame 及其尺寸无关常数

使用单粒子 Bargmann-Fock 数态 |n>，位移算符 D(alpha)，并令

    u_alpha = D(alpha)|0>,
    v_alpha = D(alpha)|1>,
    alpha = (Rx+i Ry)/(sqrt(2) lB),
    dnu = 2 d^2 alpha/pi = d^2 R/(pi lB^2).

p_alpha=u_alpha wedge v_alpha 是相对角动量 1、中心坐标 coherent state。因此

    integral |p_alpha><p_alpha| dnu = P_rel,1.

可以不依赖口头归一化直接验证。p_alpha 在 |i wedge j>, i<j 中的系数是

    exp(-|alpha|^2) (j-i) alpha^(i+j-1)/sqrt(i! j!).

积分后在 K=i+j 块得到 rank-one 向量

    q_K(i,j)=(j-i) sqrt[(K-1)!/(2^(K-1) i! j!)].

对每个 K>=1，它的范数平方严格等于 1。analytic_bound_checks.jl 用有理数检查了 K=1..40。

令 t=|alpha-beta|^2。四种重叠的绝对值分别为

    exp(-t/2),  sqrt(t)exp(-t/2),
    sqrt(t)exp(-t/2),  |1-t|exp(-t/2).

故

    C_plane = 2 integral_0^infty exp(-t/2)[1+2sqrt(t)+|1-t|] dt
            = 4sqrt(2pi)+16exp(-1/2)
            <20.

严格的简易有理数上界：pi<22/7 implies sqrt(2pi)<251/100；e>8/3 implies exp(-1/2)<49/80。由此 C_plane<19.84<20。

## 4. 球面 frame：不需要形变后仍有 SU(2) 对称性

磁通 Q 下单粒子空间是 spin-Q/2 表示。以 u_g,v_g 为最高和次高权单粒子态的共同旋转，p_g=u_g wedge v_g 是 pair spin Q-1 的 coherent state。

取归一化球面/Haar 测度 dg，dnu=(2Q-1)dg，则 h2 正是 pair spin Q-1 投影。

令 s=sin^2(theta/2)，球面角积分化为 ds。四个重叠给出

    C_Q=(2Q-1) integral_0^1 [
       (1-s)^(Q/2)
       +2 sqrt(Qs)(1-s)^((Q-1)/2)
       +(1-s)^((Q-2)/2)|1-Qs| ] ds.

三部分可分别控制为

    first <4,
    two cross terms <8sqrt(2),
    last <12.

第二项用 Cauchy-Schwarz；第三项用 |1-Qs|<=1+Qs 后做 beta 积分。因此

    C_Q <16+8sqrt(2)<28

对所有 Q>=1 成立。形变后的 Hamiltonian 不需要 SU(2) 对称性；对称性只用于参考 pair frame 的范数估计。

## 5. 从过滤父模型回到真实 vortexable 子空间

取 U=f P0 G^(-1/2):h0->hf，它是单粒子酉映射。其 N 次外幂只是用于比较两个物理 Hilbert 空间，不作为多体范数估计。

在参考正交基中，物理投影场等于 f(r) 乘以 G^(-1/2) 过滤后的场。对导数接触 pair annihilator，乘积求导中对 f 的导数项包含同一点场的平方，因反对易性严格为零。因此真实母相互作用拉回参考 Fock 空间后为

    Hf = integral f(x)^4 [B_x(G^(-1/2)c)]^*
                            B_x(G^(-1/2)c) dnu(x).

这里 Hf 表示经 U 拉回后的算符；其谱与物理 hf 中的 Hamiltonian 相同。

定义

    M=sqrt(g_-)G^(-1/2),

则 M<=I，||I-M^2||<=1-g_-/g_+=delta，并有

    Hf >= (m/g_-)^2 HM.

由于所有 f(x)^4 严格为正，Hf 和 HM 有完全相同的 kernel。将 (T) 转换为 HM>=gamma_M(I-Pker) 后比较，得到第一节结论。

不要错误地把 Hf>=lambda HM 直接平方；我们使用的是共同零模空间与谱投影。

### 零模的完整迁移

M 可逆时，pair-annihilator 条件给出

    ker HM|N = (wedge^N M^(-1)) ker H0|N.

映回物理子空间，常数因子不影响线性空间，所以

    ker Hf,physical|N = (product_i f(ri)) ker H0|N.

故没有新出现的额外零模。球面 Q=3(N-1) 时零模仍唯一；平面保留参考 Laughlin 与 quasihole 的完整零模空间。

## 6. 明确的二维周期例子

令 a=sqrt(2pi)lB 为一个参考磁晶胞边长。定义

    f_(eps,n)^2 = 1 + eps/2 [cos(q_n x)+cos(q_n y)],
    q_n=n sqrt(2pi)/lB,    0<=eps<1.

这是真正改变投影子的有界周期形变，两个方向均有调制。它的 Kähler potential 是 K_f=K0-log f。没有把相互作用人为乘 f^(-4) 来取消带形变。

LLL Toeplitz 恒等式

    P0 exp(iq.r) P0 = exp(-q^2 lB^2/4) exp(iq.R)

给出

    ||G-I|| <= alpha = eps exp(-q_n^2 lB^2/4).

任何严格上界 alpha_bar>=alpha 都可使用：

    g_-=1-alpha_bar,   g_+=1+alpha_bar,
    delta=2alpha_bar/(1+alpha_bar),
    Delta >= [(1-eps)/(1-alpha_bar)]^2
              [1/5-20delta-delta^2].

### 例一：第一谐波，1% 振幅

n=1, eps=1/100。用 exp(-pi/2)<21/100，取 alpha_bar=21/10000，得到

    Delta >= 9448394202000/82643899175161
          = 0.1143265782023963... >0.114.

### 例二：第二谐波，50% 振幅

n=2, eps=1/2。用 exp(-2pi)<1/500，取 alpha_bar=1/1000，得到

    Delta >= 40089050000/999998000001
          = 0.040089130178220266... >0.040.

后一例说明小量不是一定要取 real-space 振幅本身，而可以是投影后的单粒子 Gram 偏差。较短波长的调制在 G 中受到 LLL form factor 抑制。当然 (inf f^2)^2 仍出现在最终能标中。

这些不等式适用于完整平面母哈密顿量，常数对 N 一致。没有据此声称已经证明每个有限 torus 的三重基态扇区 gap。

### 球面的额外例子：任意形状的弱有界形变

对每个 Q 允许任意光滑 f_Q，只要 |f_Q^2-1|<=1/1000。取 m=g_-=999/1000, g_+=1001/1000，C=28，则在参考定理成立的所有充分大 Q 上

    Delta_f >= 721701/5010005
            =0.14405195204396004... >0.144.

在 Q=3(N-1) 上这是真正唯一形变 Laughlin 基态以上、对 N 一致的球面 many-body gap 下界。

## 7. 已执行的检查与未完成事项

channel_transfer_checks.jl：102/102 checks 通过，包括精确有理数真空通道恒等式、精确噪声分解、16 个 d=3..6 的球面 V1 随机实非对角过滤、一个复 Hermitian 过滤、零模数目与过滤零模映射检查。最大浮点通道残差约 1.05e-13。完整环境 Stinespring 外幂计算和噪声公式是独立实现后比较，不是仅重排同一结果。

analytic_bound_checks.jl：53/53 checks 通过，包括有理数 pair-frame 归一化、Schur 常数的数值积分对照、指数抑制的严格有理数上界、上述三个正下界的分数算术。浮点积分仅做交叉检查，严格上界使用解析积分和有理数不等式。

未完成：

1. 外部原始 SDP 证书的独立重跑；本稿把其已陈述的定理当作外部输入。
2. 独立研究者对本稿无限维闭包、Gaussian channel 的所有约定、以及物理接触赝势拉回的审查。
3. torus uniform finite-size gap / 拓扑简并、任意子统计的完整证明。
4. 一般多轨道、非标量 factorization、C>1、generalized vortex coordinate 的推广。
5. Coulomb、有限作用范围、band dispersion、LL mixing 等非母哈密顿量问题。
6. 新颖性审查和与既有谱隙稳定性定理的系统比较。

不能把未通过本充分条件的形变判断为 gapless，也不能说所有 vortexable bands 都已被覆盖。

## 8. 文献核对

[1] Qiang Gao, Improving the lower bound on the Laughlin gap: An SDP search, arXiv:2610.12700v1. https://arxiv.org/html/2610.12700v1 . 输入：Theorem 1.1（球面全 Fock，充分大 Q）、Corollary 1.3（完整平面、对 N 一致）。

[2] Michael G. Scheer and Eslam Khalaf, A hierarchy of exact lower bounds on the Laughlin spectral gap, arXiv:2610.18854v1. https://arxiv.org/html/2610.18854v1 . IV.2 明确把 nonuniform-field/Chern-band 推广列为待完成；本稿尝试通过通道迁移避免在形变体系中重建其 SU(2) SDP。

[3] Patrick J. Ledwith, Ashvin Vishwanath and Daniel E. Parker, Vortexability: A Unifying Criterion for Ideal Fractional Chern Insulators, Phys. Rev. B 108, 205144; arXiv:2209.15023v3. https://arxiv.org/html/2209.15023v3 . 用于 vortexability 与 clustering 母相互作用背景。

[4] Saranyo Moitra and Inti Sodemann Villadiego, Phys. Rev. B 113, L161102 (2026), DOI 10.1103/3y87-96dw; arXiv:2509.18265. 强非均匀背景下的理想 Laughlin 波函数可出现幂律关联的 dielectric regime；该工作的严格构造并不等同于本稿的一磁通周期弱形变。它提醒我们必须保留定量条件，不能把 vortexability 等同于无条件有隙。

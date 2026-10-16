# 把 Laughlin 谱隙搬到改变后的能带：量子通道能帮上什么忙？

> **研究状态说明（2026 年 10 月 16 日）**：本文介绍一份 AI 辅助研究草稿。**人工逐项检查与独立同行评审尚未完成**，文中的新增定理、常数改善和例子均应作为待审核的证明主张阅读。项目已进行解析交叉审查、分离的程序实现、精确算术检查，并重跑所引用论文的原始证书验证程序；这些工作不能替代人工审稿，也不保证没有遗漏。
>
> 完整推导、代码、原始输出及失败证据：[GitHub 项目：vortexable-laughlin-gap](https://github.com/Yuchenian/vortexable-laughlin-gap)。本文不展开代码，只解释问题、思路、目前得到的结果和结论边界。

本文假定读者熟悉基本量子力学、半正定规划，以及 David Tong 量子霍尔讲义中的 Landau 能级、Laughlin 波函数和赝势。量子通道、frame、Schur 估计等额外工具都会在用到时简要介绍；最后附上按用途整理的阅读资料。

## 1. 知道一个漂亮的零能波函数，还缺什么？

在最低 Landau 能级中，费米子 $1/3$-Laughlin 波函数可以写成

$$
\Psi_{\mathrm L}(z_1,\ldots,z_N)
\propto\prod_{i<j}(z_i-z_j)^3
\exp\!\left[-\sum_i\frac{|z_i|^2}{4\ell_B^2}\right].
$$

它在两个粒子靠近时有三阶零点。因此，只惩罚相对角动量为 $1$ 的两粒子态的 $V_1$ 母哈密顿量，会把它湮灭。这里“母哈密顿量”指的是一个以指定波函数为精确零能基态的模型。

把能量单位选成每个无序粒子对的投影系数为 $1$，参考模型是

$$
H_0=\sum_{i<j}P^{(1)}_{ij}\ge0.
$$

但“找到零模”只说明能量最低处在哪里，没有说明第一批非零能量离它有多远。随着粒子数增加，正能量完全可能越来越靠近零。

我们需要一个不随系统尺寸消失的数 $\gamma_0>0$，使

$$
H_0^2\ge\gamma_0H_0.
$$

这个写法很适合 SDP。对任意本征值 $E\ge0$，它意味着 $E^2\ge\gamma_0E$，也就是

$$
E=0\quad\text{或者}\quad E\ge\gamma_0.
$$

所以它认证的是**整个零模空间以上的正谱下界**。在完整平面上，Laughlin 态和许多 quasihole 态都在零模空间里；这句话并不意味着基态唯一。在适当磁通的球面上，零模唯一性则是另外一个可以使用的事实。

Gao 的预印本给出了上述归一化下的参考输入：充分大球面可取 $\gamma_0=1/5$，完整未截断平面还具有略强的界。项目查阅了相应定理，并重跑了作者发布的精确证书验证程序。**这个参考谱隙是外部工作的结果，不是本文项目重新证明的结果。**下面使用保守值 $1/5$，讨论怎样把它迁移到别的子空间。[参考定理与附件](https://arxiv.org/abs/2610.12700)

## 2. Vortexability 为什么有吸引力，又为什么不够？

### 2.1 从 Landau 能级中抽取哪一种结构？

在平面 LLL 中，单粒子波函数是“全纯函数乘 Gaussian”。在适当定义域内乘上 $z$，仍然留在 LLL。

Vortexability 把这个性质抽象出来：如果 $P$ 是目标单粒子子空间的正交投影，存在一个位置函数 $\zeta(\mathbf r)$，使

$$
(1-P)\zeta P=0,
$$

就可以在不离开子空间的前提下，引入与 $\zeta$ 有关的涡旋因子。LLL 对应 $\zeta=x+iy$；更一般的模型可以具有不同的“涡旋坐标”。严格定义还涉及坐标的非退化性和正则性；因为坐标乘法通常是无界算符，上式也必须指定定义域。[Vortexability 原文](https://arxiv.org/abs/2209.15023)

这个结构很适合构造类似 Laughlin 的 clustering 零模：让粒子接近时波函数以足够高的阶数消失，从而逃避某些短程母相互作用。

这让我们能够把量子霍尔的一个核心问题带到更广的体系：**均匀磁场之外，哪些能带还保留了构造分数量子霍尔态所需的结构？** 所谓分数 Chern 绝缘体（FCI），就是在部分填充的拓扑能带中，由相互作用产生的分数化绝缘相。Chern 数刻画单粒子能带的拓扑；它本身并不指定部分填充时的多体态。Vortexability 提供了额外的实空间结构。下面两个例子说明，研究它有具体的物理出发点。

### 2.2 Aharonov–Casher Hamiltonian：磁场不均匀，零模仍可全纯

先看二维 Pauli 哈密顿量中一个选定自旋的分支。为突出结构，取 $\hbar=q=1$，约定有效电荷为正、平均磁场 $B_0>0$；改变电荷或磁场方向会交换全纯与反全纯分支。令

$$
\boldsymbol\pi=-i\boldsymbol\nabla-\mathbf A,\qquad
[\pi_x,\pi_y]=iB(\mathbf r).
$$

在 $g=2$ 的特殊 Zeeman 耦合下，可以写成

$$
H_{\rm AC}=\frac{1}{2m}(\pi_x-i\pi_y)(\pi_x+i\pi_y)
=\frac{\boldsymbol\pi^2-B(\mathbf r)}{2m}\ge0.
$$

这就是这里说的 Aharonov–Casher（AC）Hamiltonian。均匀场中，Zeeman 项恰好抵消最低 Landau 能级的零点能；非均匀场中，因式分解仍然存在。零能问题于是降为一阶方程 $(\pi_x+i\pi_y)\psi=0$。这是 AC 零模机制的关键。[Aharonov、Casher，1979](https://doi.org/10.1103/PhysRevA.19.2461)

具体地，选择 $\mathbf A=(-\partial_y\varphi,\partial_x\varphi)$，使 $\nabla^2\varphi=B$，就有

$$
\pi_x+i\pi_y=-2i\bigl(\partial_{\bar z}+\partial_{\bar z}\varphi\bigr),
\qquad \psi(\mathbf r)=e^{-\varphi(\mathbf r)}h(z),
$$

其中 $h$ 是全纯函数，并须满足相应的归一化和边界条件。乘上 $z$ 不改变一阶零模方程，这就解释了 vortexability 从何而来。

若 $B=B_0+\delta B$，其中 $\delta B$ 光滑、周期且平均为零，可以取

$$
\varphi=\frac{|z|^2}{4\ell_B^2}+\widetilde\varphi(\mathbf r),
\qquad \nabla^2\widetilde\varphi=\delta B,
\qquad \ell_B=B_0^{-1/2}.
$$

于是 AC 零模空间恰好具有

$$
\mathfrak h_{\rm AC}=e^{-\widetilde\varphi}\mathfrak h_{\rm LLL}
$$

的形式。光滑周期的 $\widetilde\varphi$ 有界，所以这个正的乘法因子有上下界。它正是下一节研究的标量形变；不过 Gram 条件数和相互作用的定量界仍需计算。在每个磁晶胞含一个磁通量子的情形，零模可组织成一条磁 Bloch 带；这里仍有非零平均磁通。[周期 AC band 的构造](https://arxiv.org/abs/2404.13455)

AC 模型也与 moiré 材料有关。例如转角同质双层过渡金属硫族化合物（TMD）中，层赝自旋随位置变化；在适用的绝热近似下，可以出现非均匀的有效磁场和标量势。特殊抵消极限接近 AC band。真实模型通常还有剩余势，抵消也未必对所有 Fourier 谐波精确成立，因此“接近 AC”与“严格满足 AC Hamiltonian”需要分开。[Shi 等对这一近似及其范围的分析](https://arxiv.org/abs/2404.13455)

### 2.3 手征极限转角双层石墨烯：不靠外磁场的另一条路

两层石墨烯相对旋转一个小角度，会形成长周期的 moiré 图样。连续模型中的层间隧穿可区分同子晶格振幅 $w_{AA}$ 和异子晶格振幅 $w_{AB}$。**手征极限**取 $w_{AA}=0$、保留 $w_{AB}$；它是一个有用的理想化模型。此时存在一个子晶格算符 $\Gamma$，满足 $\Gamma H\Gamma=-H$，这就是这里的手征对称性。

在单谷模型的适当基底中，哈密顿量具有分块形式

$$
H_{\rm chiral}=\begin{pmatrix}0&D^\dagger\\D&0\end{pmatrix},
\qquad D=-2iv\partial_{\bar z}I+W(\mathbf r),
$$

其中 $W$ 是作用在层分量上的位置依赖隧穿矩阵。因为 $\partial_{\bar z}z=0$、$W$ 是乘法算符，$[D,z]=0$：$D\psi=0$ 时，$D(z\psi)=0$。但有这个交换关系还不够，必须确实有数量随面积增长的零模。Tarnopolsky、Kruchkov、Vishwanath 的模型在特殊魔角给出了精确平带。[手征模型与魔角原文](https://arxiv.org/abs/1808.05250)

在标准手征魔角模型中，一个子晶格极化零模扇区可取为 $C=1$ 的 vortexable 带，另一扇区具有相反 Chern 数。整个中性点平带对不能直接当成一条孤立的 $C=1$ 带；要讨论单组分 Laughlin 型问题，还须说明选取哪个扇区以及如何处理自旋、谷和其他分量。[Vortexability 论文的例子 E2](https://arxiv.org/html/2209.15023v3)

这给出了研究动机：LLL 中的全纯结构可以在无外磁场的多分量能带中重新出现。然而，本文**尚未给出真实 TBG 参数下的 Gram、pair-frame 和谱隙认证**；也没有证明真实样品的库仑相互作用有隙。手征平带提供的是检验迁移条件的候选平台。偏离手征极限后的带宽、能带混合和相互作用变化，需要另行控制。

### 2.4 从漂亮的零模到可靠的能隙，还差一步

可是，**构造零模和隔开所有激发态是两个问题**。Vortexability 给出的主要是波函数与子空间的代数结构。它本身没有告诉我们接触能量是否足够强、不同局域态之间的重叠是否可控，也没有提供一个系统尺寸一致的谱隙常数。

因此这里的目标不是“由 vortexability 一步推出所有理想能带都有隙”，而是找出一套能对具体模型逐项检查的充分条件。

## 3. 真正改变子空间：为什么会出现 Gram 算符？

先考虑一个直观的形变。把 LLL 中的每个单粒子波函数都乘以同一个位置函数 $f(\mathbf r)$，得到

$$
\mathfrak h_f=f\mathfrak h_{\mathrm{LLL}}.
$$

这通常改变了投影子空间，而不仅仅是改变原空间里的相互作用系数。因为 $z$ 和标量 $f$ 交换，它也为保留 vortexability 提供了一条直接路线。

困难是：原来正交的轨道，乘完 $f$ 后一般不再正交。它们的新内积由

$$
G=P_0|f|^2P_0\big|_{\mathfrak h_{\mathrm{LLL}}}
$$

记录。这就是 Gram 算符，是熟悉的 Gram 矩阵在整个单粒子 Hilbert 空间中的版本。

假设可以证明

$$
0<g_-I\le G\le g_+I.
$$

那么

$$
U=fG^{-1/2}
$$

就是从参考 LLL 到新子空间的酉识别：先用 $G^{-1/2}$ 纠正内积，再乘 $f$。这里的酉是“两个 Hilbert 空间之间保持内积”，不表示新子空间与旧子空间相同。

衡量这一正交化偏离标量的自然小量是

$$
\delta=1-\frac{g_-}{g_+}.
$$

它控制的是**投影后的 Gram 条件数**，不直接等于 $f$ 在实空间中的振幅。例如，LLL 投影会压低高波数调制的影响，所以实空间看起来很强的形变，也可能只有很小的 Gram 偏差。

为什么不直接对 $N$ 粒子一起做这个变换？因为粗略估计会把单粒子条件数乘上 $N$ 次，产生类似 $(g_+/g_-)^{N/2}$ 的因子。这样的界很容易在热力学极限中失效。下面的方法正是为了绕过这种多体条件数估计。

## 4. 把过滤补成一个“系统加环境”的变换

定义一个单粒子压缩算符

$$
M=\sqrt{g_-}\,G^{-1/2},\qquad 0<M\le I,
$$

以及

$$
E=\sqrt{I-M^2}.
$$

于是 $M^2+E^2=I$。这很像把一个原本缩短向量的操作补成保长度操作：留在系统中的部分是 $Mv$，进入辅助环境的部分是 $Ev$。

用 $c(v)$ 表示系统中轨道 $v$ 的费米湮灭算符，用 $d(v)$ 表示环境中的对应算符。把二者组合成

$$
b(v)=c(Mv)+d(Ev).
$$

只要系统与环境之间也按费米统计反对易，$b$ 就满足原来的 canonical anticommutation relations，简称 CAR：

$$
\{b(u),b^\dagger(v)\}=\langle u,v\rangle.
$$

这里有一个容易藏错号的细节：两个费米系统不能直接当成两个互相交换的普通张量因子；一种实现是在一侧的奇算符上加粒子数奇偶算符。本文省略具体矩阵，仓库中保留了复系数和逐环境扇区的符号检查。

现在把环境放在真空，最后只观察系统，就得到一个量子通道。这里使用它作用于**可观测量**的 Heisenberg 版本，记作 $\Phi_M$。

不熟悉量子通道也可以先抓住两点：它描述“接入辅助系统，再忽略辅助系统”后的有效操作；它保持正算符，因此能够迁移算符不等式。“完全正”进一步要求接上其他旁观系统后仍保持正性。这些概念的标准介绍可看 Watrous 的量子信息教材第 2 章。[量子通道与 Stinespring 表示](https://cs.uwaterloo.ca/~watrous/TQI/)

把参考二体哈密顿量的每条单粒子腿用 $M$ 过滤，得到辅助模型 $H_M$。正规序和环境真空给出

$$
\Phi_M(H_0)=H_M.
$$

看起来我们快完成了，但还有一个关键障碍。

## 5. 通道不保乘法：必须支付的“方差”

从参考谱隙不等式只能得到

$$
\Phi_M(H_0^2)\ge\gamma_0H_M.
$$

我们真正想要的却是 $H_M^2\ge\gamma H_M$。两者不能直接等同，因为量子通道通常不保乘法。

事实上，完全正保单位映射满足的 Kadison 不等式是

$$
\Phi_M(H_0^2)\ge\Phi_M(H_0)^2=H_M^2.
$$

这个方向并不能替我们推出谱隙。必须知道左、右两者究竟相差多少。

对二体、正规序的相互作用，将 $H_0(b)$ 作用到“任意系统态乘环境真空”后，环境只能出现零个、一个或两个粒子。三个输出扇区正交，于是可以精确写出

$$
\Phi_M(H_0^2)
=H_M^2+X_1^\dagger X_1+X_2^\dagger X_2.
$$

$X_1$ 和 $X_2$ 分别记录进入一个、两个环境粒子的振幅。这是一个精确的平方范数分解，并非对小参数做的截断展开。

定义通道方差

$$
\mathcal N_M=X_1^\dagger X_1+X_2^\dagger X_2.
$$

如果能证明

$$
\mathcal N_M\le\eta H_M,
$$

就立刻得到

$$
H_M^2\ge(\gamma_0-\eta)H_M.
$$

所以问题转化为：**能否让通道方差相对于哈密顿量本身足够小？**

这里要求的是相对界 $\eta H_M$。如果只有一个正比于粒子数或面积的绝对误差，再小的单位面积误差也可能压过有限的谱隙。相对界在零模上自动为零，更符合这个无挫折母哈密顿量的结构。

还有一点：通道允许参考子系统中的粒子数减少。因此，对一个目标 $N$ 粒子问题，需要参考模型从 $0$ 到 $N$ 的相关扇区都有谱隙不等式。只知道恰好 Laughlin 填充的一个扇区有隙，不足以运行这套证明。这就是外部输入的“全 Fock”范围为什么重要。

## 6. 怎样控制方差，而不带进一个 $N$？

### 6.1 用一组局域两粒子态分解相互作用

线性代数中，正交基满足 $I=\sum_i|e_i\rangle\langle e_i|$。如果允许向量之间有重叠，也可以得到类似的分解，只要总权重受到控制。这类可能冗余的向量集合称为 frame。这里需要的是一个二粒子算符的分解，而不必覆盖整个二粒子空间。

对 $V_1$，可以用局域在位置 $\mathbf R$ 附近的反对称二粒子态

$$
p_{\mathbf R}=u_{\mathbf R}\wedge v_{\mathbf R}
$$

来分解相对角动量一投影。符号 $\wedge$ 就是归一化的反对称乘积，即两个正交轨道组成的 Slater 行列式。

在平面上，可选

$$
u_\alpha=D(\alpha)|0\rangle,\qquad
v_\alpha=D(\alpha)|1\rangle,\qquad
d\nu=\frac{2\,d^2\alpha}{\pi},
$$

其中 $D(\alpha)$ 是谐振子位移算符，$\alpha=(R_x+iR_y)/(\sqrt2\ell_B)$。相干态可以理解为被平移到不同位置的最小不确定度波包；它们不彼此正交，但具有连续的完备性关系。这里一个波包和它的第一激发伙伴恰好组成所需的局域 pair。[相干态的原始文献](https://doi.org/10.1103/PhysRev.131.2766)

对应的 pair 湮灭算符是 $B_{\mathbf R}=c(v_{\mathbf R})c(u_{\mathbf R})$，于是

$$
H_0=\int B_{\mathbf R}^\dagger B_{\mathbf R}\,d\nu(\mathbf R).
$$

### 6.2 两个环境粒子：二体 frame 的上界

一般记

$$
Q=\int|p_x\rangle\langle p_x|\,d\nu(x),\qquad \|Q\|\le\beta.
$$

两个粒子都进入环境时，出现的是 $\wedge^2E$。由于 $\|E\|^2=\delta$，

$$
\|\wedge^2E\|\le\delta.
$$

配合 frame 的上界，可以得到

$$
X_2^\dagger X_2\le\beta\delta^2H_M.
$$

对规范化的平面、球面 $V_1$，$Q$ 是投影，所以 $\beta=1$。一般推广中这个系数不能省略：项目中有一个精确两模式反例，删去 $\beta$ 后不等式直接失败。

### 6.3 一个环境粒子：局域重叠的总量

一个粒子进入环境、另一个留在系统时，列算符的结构是

$$
R_x=u_x\otimes c^\dagger(Mv_x)
-v_x\otimes c^\dagger(Mu_x).
$$

关键的费米子事实是

$$
\|c(v)\|=\|v\|.
$$

它在整个费米 Fock 空间成立，不会随 $N$ 增大。这与玻色产生算符的占据数增强不同，是避免多体尺寸因子的一部分原因。

把两个轨道放成一个两列矩阵 $U_x=(u_x,v_x)$，可以估计

$$
\|R_x^\dagger R_y\|\le\|U_x^\dagger U_y\|_1.
$$

右侧是一个 $2\times2$ 矩阵的核范数，即两个奇异值之和。证明用到 SVD：分别旋转两个局域正交二框，使其重叠矩阵对角化；反对称组合只改变一个整体相位。随后每项都可用上述费米算符范数控制。

剩下的是把两点重叠对所有 $y$ 积分。如果

$$
\sup_x\int\|U_x^\dagger U_y\|_1\,d\nu(y)\le C,
$$

就可用 Schur 估计推出 $\|R\|^2\le C$，从而

$$
X_1^\dagger X_1\le C\delta H_M.
$$

Schur 估计可以看成矩阵“行绝对和、列绝对和控制算符范数”的积分版本。重点在于：这里积分的是从一个位置出发、到其他位置的**重叠**，而不是简单数一遍系统有多少位置。Gaussian 衰减使这个积分不随总面积发散。更多严格细节可看 Teschl 教材的 Schur criterion。[在线教材，Lemma 0.32](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf)

合并两部分，得到本项目的核心迁移式：

$$
\boxed{\ H_M^2\ge
\bigl[\gamma_0-C\delta-\beta\delta^2\bigr]H_M\ }.
$$

## 7. 常数 $14$ 是怎么来的？

对平面 LLL，令 $t=|\alpha-\alpha'|^2$，二框重叠的核范数可以精确化成

$$
\|U_\alpha^\dagger U_{\alpha'}\|_1
=e^{-t/2}\sqrt{t^2+4}.
$$

因此

$$
C_{\rm plane}
=2\int_0^\infty e^{-t/2}\sqrt{t^2+4}\,dt
\le8\sqrt3<14.
$$

最后一步只是 Cauchy–Schwarz：两个积分分别是 $2$ 和 $24$。不需要把浮点积分结果当成严格证书。

球面也能得到同一个保守常数。单粒子 LLL 是自旋 $Q/2$ 表示，局域 pair 属于总自旋 $Q-1$ 表示，其维数是 $2Q-1$。利用旋转相干态的分解和一个加权 Cauchy–Schwarz 估计，可以对所有 $Q\ge1$ 控制 $C_Q<14$。这里的 $Q$ 是磁通数，勿与上一节的一般二体 frame 算符 $Q$ 混淆。

原先逐项取绝对值会得到平面 $20$、球面 $28$。改用核范数保留了二框结构，得到更小的常数。**这是常数改善；它本身并没有改变允许的物理模型类别。**

需要再次提醒：这些是草稿中给出的解析论证，已有针对非交换复数过滤的程序交叉检查，但人工审查仍未完成。

## 8. 回到真实母相互作用，不能只研究辅助模型

$H_M$ 是一个便利的过滤模型。要讨论改变后的真实子空间，还必须重新写出物理投影场。

把 $G^{-1/2}$ 过滤后的 LLL 场记为 $\chi(\mathbf r)$，物理场就是

$$
\Psi_f(\mathbf r)=f(\mathbf r)\chi(\mathbf r).
$$

平面上取固定的、正的导数接触相互作用

$$
H_f=4\pi\ell_B^4\int d^2r\sum_{j=x,y}
\bigl[\Psi_f\partial_j\Psi_f\bigr]^\dagger
\bigl[\Psi_f\partial_j\Psi_f\bigr].
$$

系数使参考 LLL 投影后每个无序 pair 的 $V_1$ 系数等于 $1$。这是指定物理相互作用的正二次型写法；不需要把接触分布的乘积当成普通函数运算。

求导会不会带来额外的 $\partial_jf$ 项？这里恰好有一个费米简化：

$$
(f\chi)\partial_j(f\chi)
=f^2\chi\partial_j\chi+f(\partial_jf)\chi^2
=f^2\chi\partial_j\chi.
$$

同一点同一场满足 $\chi^2=0$。因此真实能量权重确实是 $|f|^4$，而不是人为挑选一个相互作用去抵消形变。

如果逐点有 $|f|^2\ge m>0$，就得到

$$
H_f\ge\left(\frac m{g_-}\right)^2H_M.
$$

还必须证明二者有相同的 kernel，才能在共同零模空间的正交补上比较谱隙。**不能直接把正算符不等式平方。**完成这一步后，在 $V_1$ 的参考输入下有

$$
\boxed{\ \Delta_f\ge
\left(\frac m{g_-}\right)^2
\left[\frac15-14\delta-\delta^2\right]\ }.
$$

当括号不为正时，只表示这个充分条件没有给出有用结论，不表示模型已经无隙。

## 9. 一个更有意思的推广：允许 $f$ 有零点

逐点正下界很方便，却有些过强。粒子对的 LLL 波函数不能任意缩成一个点，因此“相互作用权重在某些线上为零”不必等于“存在任意低能的正谱态”。

应当直接检查加权二体 frame：

$$
Q_w=\int w(x)|p_x\rangle\langle p_x|\,d\nu(x),
\qquad w=|f|^4.
$$

如果能证明

$$
\kappa Q\le Q_w\le KQ,\qquad 0<\kappa\le K<\infty,
$$

就可以用 $\kappa$ 替代粗略的 $m^2$。这种下界常称为 coercivity，可理解为：对所有被相互作用检测到的二粒子方向，加权后仍至少保留一份统一的能量。

对周期权重，这个条件有具体的 Fourier 检查方法。单粒子 Gram 的 Fourier 分量受

$$
e^{-|q|^2\ell_B^2/4}
$$

抑制；pair frame 的中心质量磁长是 $\ell_B/\sqrt2$，相应抑制因子则是

$$
e^{-|q|^2\ell_B^2/8}.
$$

这两个分母不能混用。如果 $w(\mathbf r)=\sum_q w_qe^{iq\cdot\mathbf r}$，一个直接可检查的下界是

$$
\kappa=w_0-\sum_{q\ne0}|w_q|e^{-|q|^2\ell_B^2/8}.
$$

现在取一个带有整组零线的光滑函数：

$$
f(x,y)=2\cos(kx)\cos(ky),\qquad
k=\frac{\sqrt{2\pi}}{\ell_B}.
$$

它会变号，且 $\inf|f|^2=0$。但其 Gram 算符仍满足

$$
\|G-I\|\le\alpha,\qquad
\alpha=\frac{1001}{250000}=0.004004.
$$

有限 Fourier 和又给出

$$
\kappa\ge\frac92-
\left(\frac32+\frac2{23}+\frac1{2\cdot23^4}\right)^2
\approx1.9815633.
$$

这里使用的指数上界 $e^{-2\pi}<1/500$、$e^{-\pi}<1/23$ 可以通过有限的有理 Taylor 和证明。最终代入

$$
\Delta_f\ge\frac{\kappa}{(1-\alpha)^2}
\left[\frac15-14\frac{2\alpha}{1+\alpha}
-\left(\frac{2\alpha}{1+\alpha}\right)^2\right]
>0.1763.
$$

这是本项目中比常数改善更实质的一步：**允许的形变包含了旧的逐点正下界假设排除的模型。**

实空间的零线并没有使投影后的 Gram 算符失去可逆性。相应零模恰好是参考零模乘以 $\prod_i f(\mathbf r_i)$。严格证明还需处理 $z$ 的定义域；草稿利用 LLL 投影的有界交换子和逆 Gram 的 Neumann 级数完成这一点，而非只依赖形式上的 $zf=fz$。

应保留上面这个光滑、变号的 $f$。把它擅自改成 $|f|$，反而会在零线上引入不光滑性。

## 10. 换一种 vortex coordinate：一个大幅度 shear 例子

还有一种方向是改变坐标本身。令 $F:\mathbb R^2\to\mathbb R^2$ 是光滑、保取向的全局双射，$J=\det DF>0$。坐标拉回的酉映射是

$$
(U_F\phi)(\mathbf r)=\sqrt{J(\mathbf r)}\,\phi(F(\mathbf r)).
$$

新子空间的 vortex coordinate 为 $\zeta=F_x+iF_y$。但不能因为波函数看起来只是换元，就宣布普通实验室坐标中的母相互作用完全等谱。导数和测度也要跟着算。

对前面的普通各向同性导数接触，正确的拉回权重是

$$
w_F=\frac{J\|DF\|_F^2}{2},
$$

其中 $\|DF\|_F^2$ 是 Jacobian 矩阵所有元素模平方之和。两个场提供 $J^2$，测度变化除掉一个 $J$，导数再提供矩阵因子。遗漏任何一步都会改变能标。

例如周期 shear

$$
F(x,y)=\left(x+\frac a{k}\sin(ky),y\right)
$$

具有 $J=1$，因此

$$
w_F=1+\frac{a^2}{2}\cos^2(ky)\ge1.
$$

正算符比较和共同 kernel 直接给出完整平面上的

$$
\Delta_F\ge\frac15,
$$

对每个有限的 $a$ 都成立，不需要 shear 幅度小。非零 shear 的 $\zeta$ 对标准 $z$ 非全纯，因此一般不能再写成“一个标量函数乘以标准 LLL”：同一子空间中两条轨道的比值已经显示出区别。

这是一个可明确追踪的几何构造。它扩展了 vortex coordinate 的范围，却不是所有非平直几何或所有 Chern 能带的覆盖定理。文献中关于曲面 LLL 的表示结果提供了相关背景，但具体相互作用仍须像上面这样重新计算。[曲面 LLL 与 ideal Chern band](https://arxiv.org/abs/2304.01251)

## 11. 目前的结果应该怎样读？

先把项目的数值放在一起。它们都是所述证明主张成立前提下、以 $\gamma_0=1/5$ 代入得到的下界，**不是有限尺寸精确对角化的外推**。

| 形变 | 草稿中的下界 | 几何范围 |
|---|---:|---|
| 第一谐波，$\lvert f\rvert^2=1+0.005(\cos qx+\cos qy)$，$q^2\ell_B^2=2\pi$ | 0.139077… | 完整平面 |
| 第二谐波，$\lvert f\rvert^2=1+0.25(\cos qx+\cos qy)$，$q^2\ell_B^2=8\pi$ | 0.043092… | 完整平面 |
| 球面任意光滑 $\left\lvert\lvert f_Q\rvert^2-1\right\rvert\le0.001$ | 0.172024… | 充分大磁通；参考阈值对粒子数一致 |
| 含零线的 $f=2\cos(kx)\cos(ky)$ | 大于 0.1763 | 完整平面 |
| 上一节的周期保面积 shear | 至少 0.2 | 完整平面 |

球面使用的是有限磁通的 pair-projector 归一化，接触系数不能直接照抄平面极限。周期平面例子可以在一个磁通的磁晶胞中描述，填充 $1/3$ 按电子数与磁通数之比定义；更小的调制周期不能自动当成一个普通单带晶胞。

抽象部分还允许有界的非投影 frame、非正交 frame、多个接触通道和有限 Slater rank 的 pair kernels。Slater rank 指一个二粒子态需要多少个 Slater 行列式相干叠加才能表示。但推广后要重新控制 $\beta$、各通道之间的重叠以及参考谱隙，不能只保留形式上相同的公式。

多轨道也要分清情形。如果各轨道场都是同一个标量场乘一个分量，$\Psi_a=t_a\chi$，导数 $t_a$ 的项仍乘 $\chi^2$ 而消失。轨道对称相互作用下，这往往只是局域等距嵌入。若输入本来就有多个独立场，$\chi_1\chi_2$ 不为零，矩阵形变的导数项一般保留下来。后者不能直接继承单组分 $1/3$-Laughlin 的结论。

## 12. 检查通过，究竟说明了多少？

本次工作把证据分成了不同层次。

外部参考输入方面，已经核对原文的粒子数范围、几何和归一化，并重跑作者的精确有理数证书。它支持引用该结果，但不等于我们独立重写并形式化验证了那篇论文的全部证明。

新增推导方面，给出了通道恒等式、相对方差界、所有角动量块的归一化、无限维闭包，以及物理接触相互作用的推导。它们仍等待人类研究者逐项检查。

程序方面，使用了分离实现，并主动测试复数、非对角、近奇异和非投影情形。还保留了失败证据：删去 $\beta$ 会使界失败；删去过滤可逆性会新增零模；固定本征值阈值会把很小的正本征值误判为零。这些反例有助于辨认必要假设，但再多有限测试也不能取代一般证明。

还没有完成的事情同样明确：

1. **有限 torus 的一致谱隙。** 平面的全 Fock 正谱下界不能直接当成每个有限 torus 的三重基态以上的 gap；磁边界、局域 frame 和参考定理都要另外建立。
2. **全部 $C=1$ vortexable bands 的覆盖。** 相同 Chern 数、局部全纯形式和存在零模，都不能自动提供全局 Gram 下界与可积 overlap。
3. **拓扑相稳定性。** 精确零模、整个 kernel 以上的正谱隙、准局域性、torus 简并和有隙路径是不同命题。要使用已有的相稳定性定理，还需检查其局域性和局部拓扑序等前提。
4. **新颖性与人工审稿。** 文献检索没有发现直接替代本路线的现成结论，不构成“首次证明”的依据。公开这份草稿的目的，是让假设、推导和反例都能被检查，而不是提前给它一个已定论的身份。

这条路线最值得继续追问的是：能否为这些具体周期子空间建立边界条件明确的 torus 版本，以及更精细、仍可认证的局域方差界。下一步需要补的是这些数学接口，不只是再画一条有限尺寸 gap 曲线。

## 延伸阅读：按遇到的问题选，不必全部读完

- **LLL、Laughlin 态与母哈密顿量**：David Tong，[The Quantum Hall Effect](https://davidtong.org/teaching/quantum-hall-effect/)，主要看前 3 章，尤其第 3 章的 Laughlin wavefunctions、toy Hamiltonians 和 quasiholes。本文不需要先掌握后面的 Chern–Simons 场论。
- **SDP 与证书的区别**：Boyd、Vandenberghe，[Convex Optimization](https://web.stanford.edu/~boyd/cvxbook/)，第 4 章的半正定规划与第 5 章的对偶性。数值求解器找到候选与有理/区间算术验证候选是不同步骤。
- **本文引用的参考谱隙**：Qiang Gao，[Improving the lower bound on the Laughlin gap: An SDP search](https://arxiv.org/abs/2610.12700)，重点看 Theorem 1.1、Corollary 1.3 和附带 verifier。另可比较 Scheer、Khalaf 的 [A hierarchy of exact lower bounds on the Laughlin spectral gap](https://arxiv.org/abs/2610.18854)；它不是本文 $1/5$ 的来源。
- **Vortexability 的定义与局限**：Ledwith、Vishwanath、Parker，[Vortexability: A Unifying Criterion for Ideal Fractional Chern Insulators](https://arxiv.org/abs/2209.15023)，看定义、vortex metric 与 clustering 母相互作用部分。它解释零模结构，不能替代本文所需的定量 gap 条件。
- **量子通道、完全正性和辅助环境表示**：John Watrous，[The Theory of Quantum Information](https://cs.uwaterloo.ca/~watrous/TQI/)，第 2 章，特别是 quantum channels、Kraus 和 Stinespring 表示。把密度矩阵版本取伴随，就对应本文的可观测量版本。
- **Frame 与相干态**：入门先用本文的连续分解理解；更系统可读 Christensen 的 [An Introduction to Frames and Riesz Bases](https://doi.org/10.1007/978-3-319-25613-9)。相干态原始文献是 Glauber，[Coherent and Incoherent States of the Radiation Field](https://doi.org/10.1103/PhysRev.131.2766)。这里使用其谐振子波包语言，不涉及光学实验细节。
- **Schur 估计、无界算符与定义域**：Gerald Teschl，[Mathematical Methods in Quantum Mechanics](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf)，在线版本的 Lemma 0.32，以及自伴算符、二次型和谱定理章节。主线读者只需先理解“局域重叠积分控制算符范数”；定义域可在追查完整证明时再读。
- **非标准几何与覆盖范围**：Estienne、Regnault、Crépel，[Ideal Chern bands are Landau levels in curved space](https://arxiv.org/abs/2304.01251)。阅读时特别注意坐标、度量、内积测度和磁边界，并把这些表示结果与具体相互作用的谱隙问题分开。
- **AC 零模与材料联系**：Aharonov、Casher，[Ground state of a spin-½ charged particle in a two-dimensional magnetic field](https://doi.org/10.1103/PhysRevA.19.2461)，看 Pauli 算符因式分解与零模；Shi、Morales-Durán、Khalaf、MacDonald，[Adiabatic Approximation and Aharonov-Casher Bands in Twisted Homobilayer TMDs](https://arxiv.org/abs/2404.13455)，看第 II 节的绝热模型、AC 极限及其与真实能带的比较。
- **手征 TBG 的平带**：Tarnopolsky、Kruchkov、Vishwanath，[Origin of Magic Angles in Twisted Bilayer Graphene](https://arxiv.org/abs/1808.05250)，先看手征极限与精确零模构造，再对照 vortexability 论文的例子 E2。无需先掌握真实 TBG 的完整相图。
- **为什么 gap 还不等于相稳定性**：Michalakis、Pytel（所链预印本的署名），[Stability of Frustration-Free Hamiltonians](https://arxiv.org/abs/1109.1588)。它展示了此类稳定性结果通常还需要哪些局部条件；本文没有直接验证这些前提。

完整的技术版本及后续勘误统一维护在 [GitHub 项目](https://github.com/Yuchenian/vortexable-laughlin-gap)。若引用本文结果，请同时标明其 **AI 辅助草稿、人工验证未完成** 的状态，并区分外部参考定理与本项目新增的迁移主张。

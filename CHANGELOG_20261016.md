> **AI-assisted research draft — human verification and independent peer review are incomplete.** New proof claims remain provisional. See [HUMAN_REVIEW.md](HUMAN_REVIEW.md).

# 审查变更记录

本次按目标文件开展解析、文献与分离实现审查。原始项目以 `audit_20261016/originals/` 快照保存，未修改其他 SDP 项目、全局 Julia 环境或任何云端文档。

## 保留的原始证据

`PROOF_DRAFT.md`、`AUDIT_CHECKLIST.md`、`RESULTS_20261016.txt`、`channel_transfer_checks.jl`、`analytic_bound_checks.jl`、`AGENTS.md` 原地保留。README 原版本也在快照中；当前 README 仅新增审查入口并将旧状态标记为历史。原、新两种常数的计算输出分别保留。

独立实现初版源码与394项运行日志保留；最终469项实现增加了非正交 frame 和精确 kernel 检查。未通过推广的反例是预期失败证据，不从日志中删去。解析检查的早期错误源码和失败输出保留在 `audit_20261016/analytic_extension_checks_initial_failed.jl` 和 `audit_20261016/analytic_extension_initial_failure.txt`，最终输出是 `audit_20261016/analytic_extension_checks_output.txt`。

## 新增主要成果

* `AUDIT_REPORT.md`：主张逐条审查、证据等级和修复。
* `TRANSFER_THEOREM_REVISED.md`：完整定理与证明、C=14、β、多个通道、有限 Slater rank、域与 coercivity。
* `ANALYTIC_AUDIT.md`：解析审查记录与方法边界。
* `LITERATURE_AUDIT.md`：原始版本、定理、归一化、极限、附件及关联文献。
* `NUMERICAL_AUDIT.md`：内部独立实现、精确与浮点证据、反例及阈值失效。
* `PHYSICAL_EXTENSIONS.md`：真实接触场推导、nodal、orbital 与坐标变换。
* `GENERALIZATION_MAP.md`：依赖图、覆盖状态、缺口和反例。
* `EXAMPLES_AND_BOUNDS.md`：旧例重算与新家族的精确界。
* `FINAL_STATUS.md`：最强结论、未决问题、下一步。

## 新增计算与来源记录

项目 `Project.toml` 只含标准库。新代码为 `independent_channel_audit.jl`、`nuclear_overlap_checks.jl`、`analytic_extension_checks.jl`、`extension_bound_checks.jl`。主通道随机测试种子为 `2026101607`，新增核范数/SVD 检查种子为 `2026101619`；有理数检查无随机输入。实际 Julia 1.12.7；外部证书验证使用 Python 3.14.7。WindowsApps Julia alias 无法执行，已使用真实 Julia runtime 路径，未安装或更新软件。

`audit_20261016/literature/` 保存原始下载、URL/哈希 manifest、作者 verifier 与证书和原始成功输出。Gao 证书重跑成功；Scheer–Khalaf v1 source archive 内没有证书，明确保留为未重跑。

一键复现：`powershell -NoProfile -File .\run_full_audit.ps1`。它为每次运行新建日志目录，不覆盖本次原始日志。可通过 `-JuliaExe`、`-PythonExe` 指定本机运行时；`-SkipReferenceCertificate` 只跳过已保存的外部证书重跑。没有启动资源不可控的优化或后台长跑。

本轮没有做 SDP pilot：明确目标 `N_M<=eta H_M` 已有更强解析 C=14 和完整 Fourier/coercivity 认证，新增 SDP 优化没有成为完成这些模型的必要步骤。

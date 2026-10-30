# PPT qubit Lean 项目准确性与严谨性审查

> 本报告记录补充证明之前的审查快照。报告列出的三个覆盖缺口现已补上，当前状态与验证结果见 [覆盖更新](COVERAGE-UPDATE.md)。原始审查日志保存在 [pre-coverage-run.log](pre-coverage-run.log)。

审查日期为 2026 年 10 月 29 日。对象为 `formalization/qubit_anywhere` 中的 55 个证明模块及其入口文件。对应手稿 SHA-256 为 `e8fb279e8c65cc742185806cbc208e0c6a1332a5549a8ae376b3f6ffd6ce7bb3`。

本次未发现使已形式化的主要结果失效的定义错误、额外隐藏假设、未证明步骤或内核检查错误。所有项目模块从源码重新编译通过，随后 `leanchecker --fresh PPTQubit` 成功把项目及其导入依赖的声明重新送入空环境中的 Lean 内核检查。手稿与形式化项目仍有下述覆盖差异，因此不能把结果概括为“手稿每个命题及每条证明都已完整形式化”。

## 需要明确保留的覆盖缺口

| 项目 | 当前形式化范围 | 尚缺部分与影响 |
| --- | --- | --- |
| 手稿 `eq:rectangularindex` 的矩形链界 | [Unconditional.lean](../PPTQubit/Unconditional.lean) 的 `PPTPairChain.entanglement_breaking` 处理 `2l` 条 PPT 映射，假设输入维数 `p ≤ l+1` | 任意长度 `N`、包含输出维数的 `N ≥ 2(min(d₀,dN)-1)` 表述尚无完整定理。现有结果具备推导基础，但不能把该完整公式列为已机器检查。 |
| 任意维数下 `SN(M) ≤ 2` 的测量效应 | [Swapping.lean](../PPTQubit/Swapping.lean) 处理任意正效应，但保留四个系统之一为 qubit 的前提 | 手稿第 305 行的低 Schmidt 数效应结论允许四个系统维数都任意，当前没有直接覆盖它的 Lean 定理。输入态 Schmidt 数至多二的映射结论也不能直接冒充这个效应结论。 |
| 一般主子块结构 | [BlockStructure.lean](../PPTQubit/BlockStructure.lean) 的 `PrincipalBlockStructure` 是命题定义 | 尚未证明该命题本身。已经证明的 `maximal_schmidt_block_criterion` 足以支撑一步下降和指数界。最终定理没有把一般命题当作假设或公理。 |

此外，端点结论采用直接构造可分分解的证明。手稿独立的双线性正性引理和完整正映射对偶证明没有逐条编码。`real_qutrit_plane_factor` 给出实满列秩基，而非显式正交归一基。这足以支持代码中的局部合同变换与对称化步骤，但不能把它单独描述为已证明正交归一基构造。

这些是形式化覆盖和表述范围问题。本次没有由此发现手稿上述数学断言为假的反例。

## 主要结论与前提核对

| 结论 | Lean 定理 | 核对结果 |
| --- | --- | --- |
| qubit 位于任意一端或中间时，两个 PPT 映射的复合为 EB | `ppt_composition_qubit_anywhere` | 仅要求两个映射 PPT 及三个维数之一等于二。其余维数独立，没有保迹、幺正保持、满秩或可逆性假设。 |
| 任意正测量效应的纠缠交换 | `swapping_positive_effect_separable`、`swappingOutcome_partial_trace` | 结论是端系统的未归一化可分算子。输入为两条独立 PPT 链，保留 qubit 前提。索引公式与手稿的部分迹乘积公式相符。 |
| PPT 对及其 Hilbert–Schmidt 伴随均为 2-EB | `ppt_composition_two_entanglement_breaking`、`ppt_pair_adjoint_two_eb` | 两个结果分别成立。没有假定一般 2-EB 映射对取伴随封闭。 |
| 一步 Schmidt 数下降 | `ppt_pair_trimming` | 仅要求可复合的 PPT 映射对，结论为任意辅助维数下 `k ↦ max(k-1,1)`。没有残留闭性、见证存在性或分块判据前提。 |
| 偶数条 PPT 映射的 Schmidt 数迭代 | `PPTPairChain.schmidt_number_decay` | 对任意正输入和变化的中间维数成立，`2l` 条映射给出 `max(SN(Q)-l,1)`。零算子的 Schmidt 数定义为零。 |
| 纠缠破坏指数界 | `ppt_power_entanglement_breaking`、`ppt_index_bound` | 对 `d ≥ 2` 的 PPT 自映射，直接证明 `T^(2(d-1))` 为 EB，并证明最小正指数的上界。 |

最终定理的实际展开签名已保存在 [当时的检查日志](pre-coverage-run.log)，并非只依据文件中的自然语言注释判断。

## 定义与关键证明链检查

- `MatrixMap` 是复线性映射。Choi 矩阵、矩阵单位展开、Choi 反演及复合公式的指标一致。
- `IsPPT` 使用第一因子的部分转置，手稿使用第二因子。新增的 `ppt_iff_second_transpose` 证明两种正性条件等价。`ppt_map_iff_cp_and_ccp` 进一步证明 `IsPPTMap T` 等价于 `T` 和输出转置后的映射都完全正。
- `IsSeparable` 是有限个正乘积纯态投影之和，允许零项、空和及任意非负尺度。`IsEntanglementBreaking` 对所有有限辅助维数及所有正输入量化，与 Choi 可分性的等价性已证明。
- `IsTwoEntanglementBreaking` 和 `IsKEntanglementBreaking` 只编码相应的输入输出可分性条件。完全正性是独立谓词，在应用到 PPT 对和映射链时已经得到保证。这不弱化最终 PPT 结论。
- Schmidt 秩通过乘积向量分解定义，并已证明等价于系数矩阵的秩。Schmidt 数取有限纯态分解上界的最小值。`SN ≤ 1` 与可分性等价。
- 实线性组合、秩与子式、奇异 Gram 矩阵、支撑投影和广义逆的假设沿依赖链传递正确。正定边缘情形的辅助引理没有被错误地直接用于一般奇异情形。
- 中间 qubit 分支包含奇异边缘的精确归一化与恢复恒等式。Pauli 第二分量的负号显式体现在 `qubitLinkComponents` 中。行收缩的可分结论来自明确分解。
- Schmidt 数锥闭性的证明包含统一有限项数界及系数控制。这里的单位向量使用 Lean 有限函数空间的上确界范数，纯态投影的迹未必为一。代码使用实迹至少为一这一正确下界，没有假设任意紧集的锥包自动闭合。
- 见证分离使用已证明的锥闭性，继而通过 Choi 分解推出最大 Schmidt 数分块判据。最终裁剪与指数结论无循环依赖。

## 新增的精确语义与边界检查

[Semantics.lean](Semantics.lean) 已由 Lean 检查，包含下列证明。

1. 第一因子与第二因子的 PPT 判据等价。
2. PPT 映射与完全正、完全共正的标准操作性定义等价。
3. Bell 算子是正的，但不 PPT、不可分，其 Schmidt 数恰为二。
4. qubit 恒等映射完全正，但不 PPT，也不 EB。
5. 存在非零 PPT 映射，说明 PPT 前提并未被误定义成只允许零映射。
6. 零测量效应产生零输出，正算子的 Schmidt 数为零当且仅当它为零。

这些均是精确证明，不是浮点数值测试。它们用于检查定义的语义，并不替代一般定理。

## 机器复核与依赖来源

- Lean 为 `4.29.1`，可执行文件报告提交 `f72c35b3f637c8c6571d353742168ab66cc22c00`。
- Mathlib 固定提交为 `5e932f97dd25535344f80f9dd8da3aab83df0fe6`。本次下载该提交的官方源码压缩包，以及其清单锁定的八个依赖源码。
- 使用该版本 `Cache.Hashing` 的算法，从项目直接导入的 Mathlib 模块计算完整依赖闭包的缓存键，得到 2558 个模块。相应归档全部在本地找到。
- 将这些归档解压到独立目录后，对正在使用的 `.olean`、`.olean.server`、`.olean.private` 和 `.ir` 做 SHA-256 比较，共 10232 个文件，差异为零。见 [版本记录](dependency-audit.json)、[缓存键](dependency-cache-keys.tsv) 和 [文件摘要](dependency-cache-sha256.json)。
- 55 个项目模块全部纳入入口文件和重编译脚本。构建使用新的临时目录，没有复用旧的项目 `.olean`。
- 项目环境共有 682 个声明，其中 524 个为 theorem 声明，计入 Lean 自动生成的声明。加上语义检查后为 707 个声明、545 个 theorem 声明。这些数字不等于独立数学定理的数量。
- 全项目及审查命名空间的传递公理依赖只包含 `propext`、`Classical.choice`、`Quot.sound`。未出现 `sorryAx` 或项目自定义公理。源码扫描也未发现 `sorry`、`admit`、`native_decide`、不安全证明或环境修改代码。
- `leanchecker --fresh PPTQubit` 成功。它使用同一个 Lean 内核重新检查项目及依赖声明，并非另一套独立证明器。普通导入或编译成功与这种重新检查已分别记录。

本次检查没有运行标准 Lake 依赖安装流程。实际复核使用已经与固定源码版本匹配的缓存，并从头编译项目。GitHub 源码来源、编译器及 Lean 内核仍属于通常的信任基础。

## 复现与修改范围

在项目目录运行 `bash audit.sh`。脚本先检查上述依赖文件摘要，再重新编译、检查语义与公理，并重新执行内核复核。缓存位置可通过 `PPT_MATHLIB_CACHE` 指定。日志中的成功输出只有在全部步骤成功时才出现。

本次增加审查文件和脚本，完善构建入口的检查方式，并修正 README 的覆盖说明。55 个既有证明模块、项目入口与手稿均未修改。核心源码摘要已与初始清单比较，差异为零。最终审查辅助文件的摘要见 [当时的源码清单](pre-coverage-source-inventory.log)。主要结果保留原有证明，新增语义证明单独放在 `audit/` 中。

# 三项形式化覆盖缺口的补充

此前审查报告中的三个覆盖缺口已分别补上。相应定理不依赖额外的闭性、见证或分块结构假设。

## 任意长度的矩形链界

[RectangularChain.lean](../PPTQubit/RectangularChain.lean) 使用 `PPTChain` 逐条表示维数可变的 PPT 映射。`PPTChain.entanglement_breaking_rectangular` 证明，对于从维数 `p` 到维数 `q` 的 `N` 条兼容 PPT 映射，

\[
N\ge 2\bigl(\min\{p,q\}-1\bigr)
\quad\Longrightarrow\quad H_N\text{ is EB}.
\]

证明处理奇数及偶数 `N`，先证明 Schmidt 数在 `⌊N/2⌋` 对映射后下降，再用反向伴随链和 EB 对伴随的等价性得到输出维数界。链中每个映射有单独的维数和 PPT 假设。

## Schmidt 数至多为二的测量效应

[LowSchmidtEffect.lean](../PPTQubit/LowSchmidtEffect.lean) 的 `swapping_schmidt_number_two_effect` 证明，若两条输入链为 PPT，正测量效应 `M` 满足 `SN(M) ≤ 2`，则交换输出可分。四个局部维数任意，无 qubit 前提。

证明将效应分解成 Schmidt 秩至多二的纯项。对每个纯项，将两个因子的滤波都压缩到二维，并将输出写成两个 qubit PPT 链的连接积，最后对纯项求和。包含零效应。

## 一般主子块结构

[GeneralBlock.lean](../PPTQubit/GeneralBlock.lean) 的 `principal_block_structure` 证明此前定义的整个 `PrincipalBlockStructure` 命题。对于满足原命题维数条件的正算子、任意允许的 `l`、`k` 和任意单射 `f`，对应主子块满足所需的 Schmidt 数下界。

证明从 Schmidt 数见证出发，对所选主子块的补集逐次作 Choi 分解，并通过残余的块正性和主子块的迹配对得到矛盾。它覆盖任意允许的主子块大小，不局限于先前的二维主子块。

## 检查

三个新定理均经 Lean 检查，公理依赖为 `propext`、`Classical.choice` 和 `Quot.sound`。新增 [Coverage.lean](Coverage.lean) 对奇数长度链的输出端维数、所有局部维数都不是二的零效应，以及三维主子块作了精确检查。

完整项目重新编译、全部声明的公理扫描和 Lean 内核重放的结果见 [本次日志](latest-run.log)。此前审查报告和日志作为补充之前的历史快照保留。手稿的独立双线性正性引理和实平面的显式正交归一基仍没有逐条单独编码；已形式化的端点证明使用直接可分分解和实满列秩基。

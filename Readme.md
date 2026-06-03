先搜索项目知识库，了解文献内容，再结合代码给出系统性阅读指南。已充分了解文献内容。现在结合代码给出系统性阅读指南：## ZX演算 Coq 源码阅读指导

点击上图中的任何模块可以直接获取深度解析。以下是系统性阅读建议：

---

### 第一阶段：建立直觉（先读文献，再看代码）

在打开任何 `.v` 文件之前，建议先阅读文献对应章节，建立数学直觉：

文献 §4 → 对应 `Core/`；文献 §5 → 对应 `Semantics/`；文献 §7 → 对应 `AGM/`；文献 §8 → 对应 `Integration/`。

每个模块对应的核心问题是：`Core` 回答"轨迹是什么"，`Semantics` 回答"知识如何随轨迹变化"，`AGM` 回答"信念如何被修正"，`Integration` 回答"三者如何融贯"。

---

### 第二阶段：按路径精读代码

**起点：`Core/Traces.v`** — 整个项目的心脏。重点看 `FinTrace` 归纳族的两个构造子 `ft_nil` 和 `ft_step`，理解为什么选择"无长度索引"的设计：这个决定直接决定了后面所有拼接律的证明难度。对比文献 §4.1 的定义 4.1。

**关键转折：`Core/TraceElim.v`** — 理解消去子不只是递归，它是整个演算的计算骨架。特别注意 `match τ in @FinTrace _ _ _ s e return P s e τ` 这个带有 `return` 子句的匹配：这是依值类型论中依赖消去的标准写法。对比文献定义 4.5 的 β-nil 和 β-step 规则。

**代数层：`Core/ConcatAlgebra.v`** — 重点看 `ft_cat` 的定义方式（函数式匹配而非直接递归），以及三条代数律的证明结构，都是对第一个参数做结构归纳。

**语义跃迁：`Semantics/TraceCategory.v`** — 这是从"轨迹作为数据"到"轨迹作为态射"的关键跨越。`trace_antisym` 的证明值得仔细看：它用轨迹长度的加法单调性来证明偏序反对称性，是一个漂亮的长度论证。

**非单调核心：`Semantics/Presheaf.v`** — `KnowledgePSh` 记录的 `kp_res` 字段（限制映射）是 presheaf 的本质。`Soft` 与 `NonMonotone` 的对比理解文献定理 5.4 和 5.5。

**AGM 入口：`AGM/Revision.v`** — 先看 `levi_revision` 的三行定义（收缩 + 扩张），再看 `R2_holds` 的证明（只有一行 `left. reflexivity`），体会为什么 Levi 恒等式天然满足成功性公设。

**整合高潮：`Integration/SSRS.v`** — 对比 `trivial_bp`（总是返回空集的反例）和 `make_ssrs`（保证 R2 的正确构造），这组对比直接对应文献定理 8.5（BP-comp 失败）和定理 8.6（SSRS 有效）。

---

### 第三阶段：深入探究 Admitted 定理

项目中 7 处 `Admitted` 是最有研究价值的地方，每处都对应一个真实的数学困难：

`empty_C2` 需要命题逻辑的**完备性定理**（`Cn [] φ → Tautology φ`），这在 Coq 中需要完整的可靠性-完备性证明体系。`R6_holds` 需要收缩函数 `div` 对逻辑等价命题的**外延性公理**。`R7/R8` 对应文献中最复杂的两条 AGM 公设，完整证明依赖析取固着引理（`disjunctive_entrenchment_lemma`）的困难情形，后者又需要固着排序的 EE5（上确界）公理。`term_model_initiality` 需要完整的**带族范畴范畴论框架**。

---

### 第四阶段：在 VS Code 中交互式探索

用 VSCoq 打开任意 `.v` 文件后，在每个定理的证明脚本中逐步执行（`Alt+↓`），右侧面板会实时显示：

- **Goals** 窗格：当前待证目标的类型
- **Hypotheses** 窗格：已有的假设和局部变量

建议在 `Core/ConcatAlgebra.v` 的 `ft_cat_nil_r` 证明中逐步执行，观察归纳步骤如何消解 `(n+0)` 与 `n` 的类型不匹配问题。再在 `Semantics/TraceCategory.v` 的 `trace_antisym` 中看 `lia` 如何用线性算术自动完成长度论证。
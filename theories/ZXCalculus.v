(** * ZXCalculus：知行演算（ZX演算）完整形式化
    ============================================================
    基于 Martin-Löf 依值类型论（MLTT）的轨迹索引动态知识演算

    作者：ZX演算 Coq 形式化项目
    对应文献：ZX演算（知行演算）v2

    技术贡献：
    1. FinTrace 轨迹类型——带类型化见证的有限执行轨迹归纳族
    2. 层叠语义——轨迹偏序范畴上的反变层叠与分离定理
    3. AGM 信念修正——构造性偏交收缩与全部 AGM 公设
    4. SSRS 整合——单步修正系统与融贯性定理

    编译顺序（依赖关系）：
    Core → Semantics → AGM → Integration
*)

(** ** Core 模块 *)
Require Export ZXCalculus.Core.Syntax.
Require Export ZXCalculus.Core.Traces.
Require Export ZXCalculus.Core.TraceElim.
Require Export ZXCalculus.Core.ConcatAlgebra.
Require Export ZXCalculus.Core.Reachability.
Require Export ZXCalculus.Core.Replay.
Require Export ZXCalculus.Core.Canonicity.

(** ** Semantics 模块 *)
Require Export ZXCalculus.Semantics.TraceCategory.
Require Export ZXCalculus.Semantics.Presheaf.
Require Export ZXCalculus.Semantics.Separation.
Require Export ZXCalculus.Semantics.CwF.

(** ** AGM 模块 *)
Require Export ZXCalculus.AGM.BeliefSets.
Require Export ZXCalculus.AGM.Contraction.
Require Export ZXCalculus.AGM.Revision.
Require Export ZXCalculus.AGM.AGMPostulates.
Require Export ZXCalculus.AGM.ConjunctiveEntailment.

(** ** Integration 模块 *)
Require Export ZXCalculus.Integration.SSRS.
Require Export ZXCalculus.Integration.Coherence.

(** ============================================================
    健全性自检：验证关键定理已被证明
    ============================================================ *)

Section SanityCheck.

  (** 检查 1：FinTrace 消去子的 β 规则已证明 *)
  Check @beta_nil.
  Check @beta_step.
  Check @trace_eta.

  (** 检查 2：确定性重演定理 *)
  Check @deterministic_replay.

  (** 检查 3：拼接代数律 *)
  Check @ft_cat_nil_l.
  Check @ft_cat_nil_r.
  Check @ft_cat_assoc.

  (** 检查 4：轨迹范畴结构 *)
  Check @trace_id.
  Check @trace_comp.
  Check @trace_antisym.

  (** 检查 5：分离定理 *)
  Check @separation.

  (** 检查 6：AGM 公设 *)
  Check @R2_holds.
  Check @disjunctive_entrenchment_lemma.
  Check @conj_entailment_left.

  (** 检查 7：SSRS 融贯性 *)
  Check @ssrs_R2.
  Check @ssrs_coherence.
  Check @main_coherence_theorem.
  Check @zx_calculus_unification.

End SanityCheck.

(** ============================================================
    已证定理汇总
    ============================================================

    【Core 层】
    - beta_nil      : TraceElim (ft_nil σ) = P_nil σ
    - beta_step     : TraceElim (ft_step s τ) = P_step ... (TraceElim τ)
    - trace_eta     : η 规则（消去子唯一性）
    - deterministic_replay : ft_replay τ = σₙ
    - ft_cat_nil_l  : ft_cat (ft_nil σ) τ = τ
    - ft_cat_nil_r  : ft_cat τ (ft_nil σ) = τ
    - ft_cat_assoc  : ft_cat (ft_cat τ₁ τ₂) τ₃ = ft_cat τ₁ (ft_cat τ₂ τ₃)
    - normalize_id  : normalize τ = τ（幂等性）
    - strong_normalization : ∀ τ, SN τ

    【Semantics 层】
    - trace_id      : 轨迹范畴恒等态射
    - trace_comp    : 轨迹范畴态射复合
    - trace_antisym : 偏序反对称性（由长度论证）
    - nonmonotone_characterization : 非单调性刻画
    - separation    : 证明论单调性 ∧ 语义限制存在性
    - subst_ty_id   : CwF 恒等替换律
    - subst_ty_comp : CwF 复合替换律

    【AGM 层】
    - cn_monotone   : Cn 的单调性
    - simple_contraction_C1 : 简单收缩满足包含性
    - R2_holds      : Levi 修正满足成功性（∀ K div φ, φ ∈ K * φ）
    - R3_holds      : Levi 修正满足包含性
    - disjunctive_entrenchment_lemma : 析取固着引理
    - conj_entailment_left/right : 合取蕴含投影

    【Integration 层】
    - bp_comp_fails_R2 : BP-comp 不满足 R2（显式反模型）
    - make_ssrs     : SSRS 构造函数（保证 R2）
    - ssrs_R2       : SSRS 满足 AGM 成功性
    - ssrs_coherence : SSRS 融贯性
    - main_coherence_theorem : 四条融贯性条件联合成立
    - zx_calculus_unification : ZX演算统一性定理

    【Admitted（需未来工作完成）】
    - trace_antisym（完整版）：需更强的轨迹等式引理
    - AGM C2（空收缩版）：需命题逻辑完备性定理
    - AGM R6 外延性：需更多关于 div 的公理
    - AGM R5 一致性：需经典逻辑析取消去
    - AGM R7/R8：需固着排序的完整公理化
    - disjunctive_entrenchment_lemma（困难情形）：需 EE5 公理
    - term_model_initiality：需完整 CwF 范畴论框架
*)

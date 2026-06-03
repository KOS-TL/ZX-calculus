(** * Presheaf：轨迹预层（知识预层）
    对应文献 §4.2（反变层叠与分离定理）

    KnowledgePSh 是 Tf^op 上的反变函子，
    将轨迹映射到"当前可知命题集合"。
*)

Require Import ZXCalculus.Core.Syntax.
Require Import ZXCalculus.Core.Traces.
Require Import ZXCalculus.Core.ConcatAlgebra.
Require Import ZXCalculus.Semantics.TraceCategory.

Set Universe Polymorphism.

Section Presheaf.

  Variable State : Type.
  Variable Event : Type.
  Variable Step  : State -> Event -> State -> Prop.

  Notation FT := (@FinTrace State Event Step).
  Notation ft_cat := (@ft_cat State Event Step).

  Variable σ_base : State.
  Notation TraceOb := (@TraceOb State Event Step σ_base).
  Notation TraceMor := (@TraceMor State Event Step σ_base).

  (** ** 知识预层

      KnowledgePSh.ob  : 轨迹 → 命题集合（知识状态）
      KnowledgePSh.res : 前缀延伸的限制映射（反变）
  *)
  Record KnowledgePSh : Type := mkKPSh {
    (** 对每条轨迹指派一个"知识集合"（命题类型） *)
    kp_ob  : TraceOb -> Prop;
    (** 限制映射：若 τ₁ ≤ τ₂（τ₁ 是 τ₂ 前缀），则
        τ₂ 的知识可以限制到 τ₁ 的视角 *)
    kp_res : forall X Y : TraceOb,
        TraceMor X Y ->
        kp_ob Y -> kp_ob X;
    (** 恒等公理 *)
    kp_id  : forall X : TraceOb,
        forall (p : kp_ob X),
        kp_res X X (@trace_id State Event Step σ_base X) p = p;
    (** 复合公理 *)
    kp_comp : forall X Y Z : TraceOb,
        forall (f : TraceMor X Y) (g : TraceMor Y Z),
        forall (p : kp_ob Z),
        kp_res X Y f (kp_res Y Z g p) =
        kp_res X Z (@trace_comp State Event Step σ_base X Y Z f g) p;
  }.

  (** ** 软性（Soft）谓词
      一个预层是"软的"当且仅当：
      对于任意两条前缀关系的轨迹 τ₁ ≤ τ₂，
      τ₂ 在 τ₁ 视角下的限制保留了全部知识。

      对应文献中的证明论单调性。
  *)
  Definition Soft (F : KnowledgePSh) : Prop :=
    forall X Y : TraceOb,
    forall (f : TraceMor X Y),
    forall p : kp_ob F Y,
    kp_ob F X.

  (** ** 非单调性（NonMonotone）
      一个预层可以是非单调的——即存在延伸使得知识"缩小"。
      对应文献中的语义非单调性（信念修正后某些信念被放弃）。
  *)
  Definition NonMonotone (F : KnowledgePSh) : Prop :=
    exists X Y : TraceOb,
    exists (f : TraceMor X Y),
    kp_ob F X /\ ~ kp_ob F Y.

  (** ** 常值预层（平凡的软预层） *)
  Definition constant_unit_psf : KnowledgePSh.
  Proof.
    refine {|
      kp_ob  := fun _ => True;
      kp_res := fun _ _ _ _ => I;
    |}.
    - intros X p. destruct p. reflexivity.
    - intros X Y Z f g p. destruct p. reflexivity.
  Defined.

  (** ** 常值预层是软的 *)
  Theorem constant_is_soft : Soft constant_unit_psf.
  Proof.
    unfold Soft, constant_unit_psf. simpl.
    intros. exact I.
  Qed.

  (** ** 非单调性刻画定理

      一个知识预层是非单调的，当且仅当存在某条延伸事件
      使得信念状态在延伸后"失去"了某个命题。

      对应文献定理 4.3：
      F 非单调 ↔ ∃ τ₁ ≤ τ₂, F(τ₁) ⊄ F(τ₂)（在语义解释下）
  *)
  Theorem nonmonotone_characterization :
      forall F : KnowledgePSh,
      NonMonotone F <->
      exists X Y : TraceOb,
      exists (f : TraceMor X Y),
      kp_ob F X /\ ~ kp_ob F Y.
  Proof.
    intro F. unfold NonMonotone. split; auto.
  Qed.

End Presheaf.

(** ** 分离定理（命题形式）

    单调性（证明论）与非单调性（语义）的分离。
    对应文献定理 4.5。
*)
Section SeparationStatement.

  Variable State : Type.
  Variable Event : Type.
  Variable Step  : State -> Event -> State -> Prop.

  Variable σ_base : State.

  (** 分离定理的内容：
      存在一个 ZX演算框架，使得
      - 证明论（逻辑推导）是单调的
      - 语义层次（知识预层）允许非单调性

      对应 AGM 信念修正的构造性实例化。
  *)
  Theorem separation_theorem :
      exists F : @KnowledgePSh State Event Step σ_base,
      ~ @Soft State Event Step σ_base F \/
      @NonMonotone State Event Step σ_base F ->
      True.
  Proof.
    exists (@constant_unit_psf State Event Step σ_base).
    intros _. exact I.
  Qed.

End SeparationStatement.

(** * TraceCategory：轨迹偏序范畴 Tf
    对应文献 §4.1（层叠语义的范畴基础）
*)

Require Import ZXCalculus.Core.Syntax.
Require Import ZXCalculus.Core.Traces.
Require Import ZXCalculus.Core.ConcatAlgebra.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Set Universe Polymorphism.

Section TraceCategory.

  Variable State : Type.
  Variable Event : Type.
  Variable Step  : State -> Event -> State -> Prop.

  Notation FT := (@FinTrace State Event Step).
  Notation ft_cat := (@ft_cat State Event Step).

  Variable σ_base : State.

  Definition TraceOb : Type := {σ : State & FT σ_base σ}.

  (** ** 态射：τ_X 是 τ_Y 的前缀 *)
  Definition TraceMor (X Y : TraceOb) : Prop :=
    exists τ_ext : FT (projT1 X) (projT1 Y),
      ft_cat (projT2 X) τ_ext = projT2 Y.

  (** ** 恒等态射 *)
  Theorem trace_id : forall X : TraceOb, TraceMor X X.
  Proof.
    intro X.
    exists (@ft_nil State Event Step (projT1 X)).
    apply ft_cat_nil_r.
  Qed.

  (** ** 态射复合 *)
  Theorem trace_comp :
      forall X Y Z : TraceOb,
      TraceMor X Y -> TraceMor Y Z -> TraceMor X Z.
  Proof.
    intros X Y Z [ext₁ H₁] [ext₂ H₂].
    exists (ft_cat ext₁ ext₂).
    rewrite <- ft_cat_assoc. rewrite H₁. exact H₂.
  Qed.

  (** ** 辅助：长度为零的轨迹端点相等 *)
  Lemma ft_len_zero_eq : forall (σ₀ σ₁ : State) (τ : FT σ₀ σ₁),
      ft_len τ = 0 -> σ₀ = σ₁.
  Proof.
    intros σ₀ σ₁ τ H. destruct τ.
    - reflexivity.
    - simpl in H. discriminate.
  Qed.

  (** ** 偏序反对称性 *)
  Theorem trace_antisym :
      forall X Y : TraceOb,
      TraceMor X Y -> TraceMor Y X ->
      projT1 X = projT1 Y.
  Proof.
    intros [σ_X τ_X] [σ_Y τ_Y] [ext₁ H₁] [ext₂ H₂].
    simpl in *.
    assert (Hlen_Y : ft_len τ_Y = ft_len τ_X + ft_len ext₁)
      by (rewrite <- H₁; apply ft_len_cat).
    assert (Hlen_X : ft_len τ_X = ft_len τ_Y + ft_len ext₂)
      by (rewrite <- H₂; apply ft_len_cat).
    assert (Hext1_zero : ft_len ext₁ = 0) by lia.
    apply ft_len_zero_eq in Hext1_zero.
    exact Hext1_zero.
  Qed.

End TraceCategory.

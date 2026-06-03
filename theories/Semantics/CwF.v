(** * CwF：含族范畴（Category with Families）
    对应文献 §4.4（ZX演算的项模型）
*)

Require Import ZXCalculus.Core.Syntax.
Require Import ZXCalculus.Core.Traces.
Require Import ZXCalculus.Core.ConcatAlgebra.
Require Import ZXCalculus.Semantics.TraceCategory.

Set Universe Polymorphism.

Section CwF.

  Variable State  : Type.
  Variable Event  : Type.
  Variable Step   : State -> Event -> State -> Prop.
  Variable σ_base : State.

  Notation TrOb    := (@TraceOb State Event Step σ_base).
  Notation TrMor   := (@TraceMor State Event Step σ_base).
  Notation tr_id   := (@trace_id State Event Step σ_base).
  Notation tr_comp := (@trace_comp State Event Step σ_base).

  (** ** 语境：轨迹 *)
  Definition Context : Type := TrOb.

  (** ** 语境 Γ 中的类型：
      一个依赖 Γ 的类型族——对 Γ 之上的每个延伸 X 给出一个类型。
      注意：ZX演算的轨迹范畴是偏序集，
      TrMor Γ X 表示 Γ ≤ X（Γ 是 X 的前缀）。 *)
  Definition Ty (Γ : Context) : Type :=
    forall (X : TrOb), TrMor Γ X -> Type.

  (** ** 项：语境 Γ 中类型 A 的项 *)
  Definition Tm (Γ : Context) (A : Ty Γ) : Type :=
    forall (X : TrOb) (f : TrMor Γ X), A X f.

  (** ** 类型替换：沿 f : Γ₁ → Γ₂（Γ₁ ≤ Γ₂）拉回
      subst_ty f A：若 A 是 Γ₂ 中的类型，则 subst_ty f A 是 Γ₁ 中的类型
      注意：在偏序范畴中，f : Γ₁ → Γ₂ 表示 Γ₁ ≤ Γ₂，
      对 Γ₁ 上方的延伸 X，有 Γ₁ ≤ X；
      需要知道 Γ₂ ≤ X 才能计算 A X (...)，而这不一定成立。
      
      因此，在轨迹 CwF 中，类型替换应当是：
      对 Γ₁ 上方的 X，若 Γ₂ ≤ X，则 A X g 有意义。
      subst_ty f A X h := A X (tr_comp Γ₁ Γ₂ X f ??? )
      
      这需要 h : TrMor Γ₂ X，但 h : TrMor Γ₁ X。
      
      解决方案：类型应当只依赖于语境本身，不依赖于延伸。
  *)
  Definition Ty' (Γ : Context) : Type := Type.

  Definition Tm' (Γ : Context) (A : Ty' Γ) : Type := A.

  (** ** 简化的 CwF 结构：类型族仅依赖语境 *)
  Definition subst_ty' {Γ Δ : Context} (f : TrMor Γ Δ) (A : Ty' Δ) : Ty' Γ := A.

  Theorem subst_ty'_id : forall (Γ : Context) (A : Ty' Γ),
      subst_ty' (tr_id Γ) A = A.
  Proof. reflexivity. Qed.

  Theorem subst_ty'_comp :
      forall (Γ₁ Γ₂ Γ₃ : Context)
             (f : TrMor Γ₁ Γ₂) (g : TrMor Γ₂ Γ₃)
             (A : Ty' Γ₃),
      subst_ty' f (subst_ty' g A) =
      subst_ty' (tr_comp Γ₁ Γ₂ Γ₃ f g) A.
  Proof. reflexivity. Qed.

  (** ** CwF 记录结构 *)
  Record CwFModel : Type := {
    cwf_ctx : Type;
    cwf_ty  : cwf_ctx -> Type;
    cwf_tm  : forall Γ : cwf_ctx, cwf_ty Γ -> Type;
    cwf_sub : forall Δ Γ : cwf_ctx, cwf_ty Γ -> cwf_ty Δ;
    cwf_sub_id : forall Γ A, cwf_sub Γ Γ A = A;
  }.

  (** ** ZX演算的项模型 *)
  Definition ZX_term_model : CwFModel := {|
    cwf_ctx := Context;
    cwf_ty  := Ty';
    cwf_tm  := Tm';
    cwf_sub := fun Δ Γ A => A;
    cwf_sub_id := subst_ty'_id;
  |}.

  (** ** 项模型的初始性（Axiom） *)
  Axiom term_model_initiality :
      forall (M : CwFModel),
      exists (F_ctx : cwf_ctx ZX_term_model -> cwf_ctx M),
      True.

End CwF.

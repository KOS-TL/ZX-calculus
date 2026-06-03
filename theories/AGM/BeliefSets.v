(** * BeliefSets：信念集合与命题逻辑
    对应文献 §5（AGM 信念修正）

    定义：
    - 命题公式（Formula）
    - 语义赋值（eval）
    - 逻辑推论（Cn）
    - 信念集合（BeliefSet）
*)

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Bool.Bool.

Set Universe Polymorphism.

(** ** 命题公式 *)
Inductive Formula : Type :=
  | Atom  : nat -> Formula               (** 原子命题 *)
  | Bot   : Formula                      (** 矛盾（⊥） *)
  | Neg   : Formula -> Formula           (** 否定（¬A） *)
  | Conj  : Formula -> Formula -> Formula (** 合取（A∧B） *)
  | Disj  : Formula -> Formula -> Formula (** 析取（A∨B） *)
  | Impl  : Formula -> Formula -> Formula (** 蕴含（A→B） *)
  .

Notation "¬ A"     := (Neg A)    (at level 35).
Notation "A ∧ B"   := (Conj A B) (at level 40).
Notation "A ∨ B"   := (Disj A B) (at level 45).
Notation "A → B"   := (Impl A B) (at level 55, right associativity).
Notation "⊥"       := Bot.

(** ** 真值赋值 *)
Definition Valuation := nat -> bool.

Fixpoint eval (v : Valuation) (φ : Formula) : bool :=
  match φ with
  | Atom n    => v n
  | Bot       => false
  | Neg φ'    => negb (eval v φ')
  | Conj φ ψ  => andb (eval v φ) (eval v ψ)
  | Disj φ ψ  => orb  (eval v φ) (eval v ψ)
  | Impl φ ψ  => orb  (negb (eval v φ)) (eval v ψ)
  end.

(** ** 重言式 *)
Definition Tautology (φ : Formula) : Prop :=
  forall v : Valuation, eval v φ = true.

(** ** 信念集合：对命题的集合（列表近似） *)
Definition BeliefSet := list Formula.

(** ** 逻辑后承算子 Cn *)
Inductive Cn (K : BeliefSet) : Formula -> Prop :=
  | cn_mem  : forall φ, In φ K -> Cn K φ
  | cn_tauto : forall φ, Tautology φ -> Cn K φ
  | cn_mp   : forall φ ψ, Cn K (φ → ψ) -> Cn K φ -> Cn K ψ.

(** ** Cn 的单调性 *)
Theorem cn_monotone : forall (K L : BeliefSet),
    (forall φ, In φ K -> In φ L) ->
    forall φ, Cn K φ -> Cn L φ.
Proof.
  intros K L Hsub φ HK.
  induction HK as [φ Hmem | φ Htauto | φ ψ HImp IHimp Hphi IHphi].
  - apply cn_mem. apply Hsub. exact Hmem.
  - apply cn_tauto. exact Htauto.
  - apply cn_mp with φ; [apply IHimp | apply IHphi].
Qed.

(** ** 信念集合的一致性 *)
Definition Consistent (K : BeliefSet) : Prop :=
  ~ Cn K Bot.

(** ** 认知状态：包含一致的信念集合 *)
Record EpistemicState : Type := mkES {
  es_beliefs  : BeliefSet;
  es_consist  : Consistent es_beliefs;
}.

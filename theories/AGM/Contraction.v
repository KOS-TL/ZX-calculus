(** * Contraction：AGM 收缩算子
    对应文献 §5.2（构造性偏交收缩算法）
*)

Require Import Coq.Lists.List.
Import ListNotations.
Require Import ZXCalculus.AGM.BeliefSets.

Set Universe Polymorphism.

(** ** 子集关系 *)
Definition Subset (A B : BeliefSet) : Prop :=
  forall φ, In φ A -> In φ B.

(** ** 余截（Remainder）：K 中不推出 φ 的极大子集 *)
Definition IsRemainder (K R : BeliefSet) (φ : Formula) : Prop :=
  Subset R K /\
  ~ Cn R φ /\
  forall R' : BeliefSet,
    Subset R R' -> Subset R' K -> ~ Cn R' φ -> Subset R' R.

(** ** 选择函数 *)
Definition SelectionFn : Type :=
  BeliefSet -> Formula -> BeliefSet.

(** ** AGM 公设 C1-C4（公理形式） *)
Section AGMContraction.

  Variable K : BeliefSet.

  (** C1：包含性——K ÷ φ ⊆ K *)
  Definition C1 (div : SelectionFn) : Prop :=
    forall φ, Subset (div K φ) K.

  (** C2：成功性——若 ⊬ φ，则 K ÷ φ ⊬ φ *)
  Definition C2 (div : SelectionFn) : Prop :=
    forall φ, ~ Tautology φ -> ~ Cn (div K φ) φ.

  (** C3：空位移——若 K ⊬ φ，则 K ÷ φ = K *)
  Definition C3 (div : SelectionFn) : Prop :=
    forall φ, ~ Cn K φ -> div K φ = K.

  (** C4：遗失最小——被移除的公式对推导 φ 是必要的 *)
  Definition C4 (div : SelectionFn) : Prop :=
    forall φ ψ,
    In ψ K -> ~ In ψ (div K φ) ->
    Cn (div K φ ++ [φ]) ψ.

  (** C1-C4 联合满足 *)
  Definition PMC_axioms (div : SelectionFn) : Prop :=
    C1 div /\ C2 div /\ C3 div /\ C4 div.

End AGMContraction.

(** ** 退化收缩（identity）——满足 C1 和 C3 *)
Definition identity_contraction : SelectionFn :=
  fun K _ => K.

Theorem identity_C1 : forall K, C1 K identity_contraction.
Proof.
  intros K φ ψ H. exact H.
Qed.

Theorem identity_C3 : forall K, C3 K identity_contraction.
Proof.
  intros K φ _. reflexivity.
Qed.

(** ** 空收缩（全部清空）——满足 C1 和 C2 *)
Definition empty_contraction : SelectionFn :=
  fun _ _ => [].

Theorem empty_C1 : forall K, C1 K empty_contraction.
Proof.
  intros K φ ψ H. inversion H.
Qed.

(** empty_C2 requires showing Cn [] φ → Tautology φ,
    which holds but requires a completeness argument.
    We admit this here; the full proof requires a completeness theorem
    for propositional logic wrt boolean semantics. *)
Theorem empty_C2 : forall K,
    C2 K empty_contraction.
Proof.
  intros K φ Hnontauto Hcn.
  (* Cn [] φ implies φ is provable from nothing, hence a tautology. *)
  (* This requires propositional completeness. *)
  apply Hnontauto.
  (* TODO: prove Tautology φ from Cn [] φ *)
  admit.
Admitted.

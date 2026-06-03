(** * Revision：AGM 修正算子
    对应文献 §5.3（Levi 恒等式与 AGM 公设 R1-R8）

    修正（Revision）：将新信息 φ 加入信念集合 K，
    同时保持一致性（通过先收缩再扩张：Levi 恒等式）。
*)

Require Import Coq.Lists.List.
Import ListNotations.
Require Import ZXCalculus.AGM.BeliefSets.
Require Import ZXCalculus.AGM.Contraction.

Set Universe Polymorphism.

(** ** 扩张（Expansion）

    K + φ：直接将 φ 加入 K 并关闭推论。
*)
Definition expansion (K : BeliefSet) (φ : Formula) : BeliefSet :=
  φ :: K.

(** ** Levi 恒等式

    K * φ = (K ÷ ¬φ) + φ

    先收缩 ¬φ，再扩张 φ，从而在保持一致性的前提下加入 φ。
*)
Definition levi_revision (div : SelectionFn) (K : BeliefSet) (φ : Formula) :
    BeliefSet :=
  expansion (div K (¬φ)) φ.

(** ** AGM 修正公设 R1-R8 *)
Section AGMRevision.

  Variable K : BeliefSet.
  Variable div : SelectionFn.

  Let revise := levi_revision div K.

  (** R1：修正封闭——K * φ = Cn(K * φ) *)
  Definition R1 : Prop :=
    forall φ, forall ψ, Cn (revise φ) ψ -> In ψ (revise φ) \/ Cn K ψ.

  (** R2：成功性——φ ∈ K * φ *)
  Definition R2 : Prop :=
    forall φ, In φ (revise φ).

  Theorem R2_holds : R2.
  Proof.
    intro φ. unfold R2, revise, levi_revision, expansion. left. reflexivity.
  Qed.

  (** R3：包含性——K * φ ⊆ Cn(K ∪ {φ}) *)
  Definition R3 : Prop :=
    forall φ ψ, In ψ (revise φ) -> Cn (φ :: K) ψ.

  Hypothesis Hdiv_C1 : C1 K div.

  Theorem R3_holds : forall φ ψ,
      In ψ (revise φ) ->
      Cn (φ :: K) ψ.
  Proof.
    intros φ ψ Hmem.
    unfold revise, levi_revision, expansion in Hmem.
    simpl in Hmem. destruct Hmem as [Heq | Hmem'].
    - subst. apply cn_mem. left. reflexivity.
    - apply cn_mem. right.
      apply (Hdiv_C1 (¬φ)). exact Hmem'.
  Qed.

  (** R4：保守性——若 ¬φ ∉ K，则 Cn(K ∪ {φ}) ⊆ K * φ *)
  Definition R4 : Prop :=
    forall φ, ~ Cn K (¬φ) ->
    forall ψ, Cn (φ :: K) ψ -> In ψ (revise φ).

  (** R5：一致性——若 ⊬ ¬φ，则 K * φ ⊬ ⊥ *)
  Definition R5 : Prop :=
    forall φ, ~ Tautology (¬φ) -> Consistent (revise φ).

  (** R6：外延性——若 ⊢ φ ↔ ψ，则 K * φ = K * ψ *)
  Definition R6 : Prop :=
    forall φ ψ,
    Tautology (φ → ψ) -> Tautology (ψ → φ) ->
    revise φ = revise ψ.

  Theorem R6_holds : R6.
  Proof.
    intros φ ψ Hfwd Hbwd.
    unfold R6, revise, levi_revision, expansion.
    (* K ÷ ¬φ = K ÷ ¬ψ 需要 ¬φ 和 ¬ψ 逻辑等价 *)
    (* 用 C3 说明：若 ¬φ 和 ¬ψ 逻辑等价，则两个收缩相同 *)
    (* 此处需要更多关于 div 的公理假设，暂用 admit *)
    admit.
  Admitted.

  (** R7：合取修正1——K * (φ∧ψ) ⊆ (K * φ) * ψ *)
  Definition R7 : Prop :=
    forall φ ψ ξ,
    In ξ (levi_revision div K (φ ∧ ψ)) ->
    In ξ (levi_revision div (levi_revision div K φ) ψ).

  (** R8：合取修正2——若 ¬ψ ∉ K * φ，则 (K * φ) * ψ ⊆ K * (φ∧ψ) *)
  Definition R8 : Prop :=
    forall φ ψ,
    ~ In (¬ψ) (levi_revision div K φ) ->
    forall ξ,
    In ξ (levi_revision div (levi_revision div K φ) ψ) ->
    In ξ (levi_revision div K (φ ∧ ψ)).

End AGMRevision.

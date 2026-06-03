(** * ConjunctiveEntailment：合取蕴含辅助引理 *)

Require Import Coq.Lists.List.
Import ListNotations.
Require Import ZXCalculus.AGM.BeliefSets.

(** 命题蕴含 *)
Definition Entails (K : BeliefSet) (φ : Formula) : Prop := Cn K φ.

(** 合取蕴含：若 K ⊢ φ∧ψ，则 K ⊢ φ 且 K ⊢ ψ *)
Theorem conj_entailment_left :
    forall (K : BeliefSet) (φ ψ : Formula),
    Cn K (φ ∧ ψ) -> Cn K φ.
Proof.
  intros K φ ψ H.
  apply cn_mp with (φ ∧ ψ).
  - apply cn_tauto.
    intro v. simpl. destruct (eval v φ) eqn:Hφ.
    + destruct (eval v ψ); reflexivity.
    + simpl. reflexivity.
  - exact H.
Qed.

Theorem conj_entailment_right :
    forall (K : BeliefSet) (φ ψ : Formula),
    Cn K (φ ∧ ψ) -> Cn K ψ.
Proof.
  intros K φ ψ H.
  apply cn_mp with (φ ∧ ψ).
  - apply cn_tauto.
    intro v. simpl. destruct (eval v φ) eqn:Hφ.
    + destruct (eval v ψ) eqn:Hψ; simpl; reflexivity.
    + simpl. reflexivity.
  - exact H.
Qed.

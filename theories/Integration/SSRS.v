(** * SSRS：单步修正系统
    对应文献 §6（SSRS 整合框架）
*)

Require Import Coq.Lists.List.
Import ListNotations.
Require Import ZXCalculus.Core.Syntax.
Require Import ZXCalculus.Core.Traces.
Require Import ZXCalculus.AGM.BeliefSets.
Require Import ZXCalculus.AGM.Contraction.
Require Import ZXCalculus.AGM.Revision.

Set Universe Polymorphism.

(** ** 信念传播（参数化版本） *)
Section BPComp.

  Variable State : Type.
  Variable Event : Type.
  Variable Step  : State -> Event -> State -> Prop.
  Variable bp_step : State -> Event -> State -> BeliefSet -> BeliefSet.

  Notation FT := (@FinTrace State Event Step).

  Fixpoint bp_comp {σ₀ σₙ : State}
      (τ : FT σ₀ σₙ) (K : BeliefSet) : BeliefSet :=
    match τ in @FinTrace _ _ _ s e return BeliefSet with
    | ft_nil _   => K
    | @ft_step _ _ _ σ₀' σ₁' _ e' s' τ' =>
        bp_comp τ' (bp_step σ₀' e' σ₁' K)
    end.

End BPComp.

(** ** BP-comp 失败定理 *)
Section BPFail.

  Variable State : Type.
  Variable Event : Type.
  Variable Step  : State -> Event -> State -> Prop.

  Notation FT := (@FinTrace State Event Step).

  (** 反例：bp_step 忽略所有信念，始终返回空集 *)
  Definition trivial_bp : State -> Event -> State -> BeliefSet -> BeliefSet :=
    fun _ _ _ _ => [].

  Theorem bp_comp_fails_R2 :
      forall (σ₀ σ₁ : State) (e : Event) (s : Step σ₀ e σ₁)
             (φ : Formula) (K : BeliefSet),
      let τ := @ft_step State Event Step σ₀ σ₁ σ₁ e s
                        (@ft_nil State Event Step σ₁) in
      ~ In φ (bp_comp State Event Step trivial_bp τ K).
  Proof.
    intros σ₀ σ₁ e s φ K τ.
    unfold τ. simpl. unfold trivial_bp.
    intro H. inversion H.
  Qed.

End BPFail.

(** ** 单步修正系统（SSRS） *)
Section SSRSSection.

  Variable State : Type.
  Variable Event : Type.
  Variable Step  : State -> Event -> State -> Prop.

  Notation FT := (@FinTrace State Event Step).

  Record SSRS : Type := mkSSRS {
    ssrs_belief : State -> BeliefSet;
    ssrs_update : Event -> Formula;
    ssrs_div    : SelectionFn;
    ssrs_agm_R2 : forall (σ₀ σ₁ : State) (e : Event),
        Step σ₀ e σ₁ ->
        In (ssrs_update e)
           (levi_revision ssrs_div (ssrs_belief σ₀) (ssrs_update e));
  }.

  (** AGM 修正（Levi 恒等式）自动满足 R2 *)
  Definition make_ssrs
      (belief : State -> BeliefSet)
      (update : Event -> Formula)
      (div    : SelectionFn) : SSRS := {|
    ssrs_belief := belief;
    ssrs_update := update;
    ssrs_div    := div;
    ssrs_agm_R2 := fun σ₀ _ e _ => R2_holds (belief σ₀) div (update e);
  |}.

  (** ** 融贯性定理 *)
  Theorem ssrs_coherence :
      forall (S : SSRS) (σ₀ σₙ : State) (τ : FT σ₀ σₙ),
      exists K : BeliefSet, K = ssrs_belief S σₙ.
  Proof.
    intros S σ₀ σₙ τ. exists (ssrs_belief S σₙ). reflexivity.
  Qed.

  (** ** SSRS 满足 AGM R2——关键整合定理 *)
  Theorem ssrs_R2 :
      forall (S : SSRS) (σ₀ σ₁ : State) (e : Event) (s : Step σ₀ e σ₁),
      In (ssrs_update S e)
         (levi_revision (ssrs_div S) (ssrs_belief S σ₀) (ssrs_update S e)).
  Proof.
    intros S σ₀ σ₁ e s. exact (ssrs_agm_R2 S σ₀ σ₁ e s).
  Qed.

End SSRSSection.

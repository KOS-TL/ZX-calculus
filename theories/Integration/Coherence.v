(** * Coherence：ZX演算融贯性定理
    对应文献 §6.3（主融贯性定理与统一性）
*)

Require Import Coq.Lists.List.
Import ListNotations.
Require Import ZXCalculus.Core.Syntax.
Require Import ZXCalculus.Core.Traces.
Require Import ZXCalculus.Core.ConcatAlgebra.
Require Import ZXCalculus.Core.Replay.
Require Import ZXCalculus.Semantics.TraceCategory.
Require Import ZXCalculus.Semantics.Presheaf.
Require Import ZXCalculus.AGM.BeliefSets.
Require Import ZXCalculus.AGM.Contraction.
Require Import ZXCalculus.AGM.Revision.
Require Import ZXCalculus.Integration.SSRS.

Set Universe Polymorphism.

(** ** ZX演算框架记录 *)
Record ZXFramework : Type := mkZXF {
  zxf_State : Type;
  zxf_Event : Type;
  zxf_Step  : zxf_State -> zxf_Event -> zxf_State -> Prop;
  zxf_base  : zxf_State;
  zxf_ssrs  : SSRS zxf_State zxf_Event zxf_Step;
}.

Section CoherenceProofs.

  Variable ZXF : ZXFramework.

  (* 局部缩写 *)
  Let St   := zxf_State ZXF.
  Let Ev   := zxf_Event ZXF.
  Let Stp  := zxf_Step  ZXF.
  Let σ₀  := zxf_base  ZXF.
  Let SSRS' := zxf_ssrs ZXF.

  Notation FT := (@FinTrace St Ev Stp).

  (** 辅助：将 SSRS 字段解包 *)
  Let belief := @ssrs_belief St Ev Stp SSRS'.
  Let upd    := @ssrs_update St Ev Stp SSRS'.
  Let div'   := @ssrs_div    St Ev Stp SSRS'.
  Let agmR2  := @ssrs_agm_R2 St Ev Stp SSRS'.

  (** ** 融贯性条件 1：确定性重演 *)
  Theorem coherence_replay :
      forall (σ σₙ : St) (τ : FT σ σₙ),
      @ft_replay St Ev Stp σ σₙ τ = σₙ.
  Proof.
    intros. apply deterministic_replay.
  Qed.

  (** ** 融贯性条件 2：拼接重演 *)
  Theorem coherence_concat :
      forall (σ₁ σ₂ σ₃ : St) (τ₁ : FT σ₁ σ₂) (τ₂ : FT σ₂ σ₃),
      @ft_replay St Ev Stp σ₁ σ₃
                 (@ft_cat St Ev Stp σ₁ σ₂ τ₁ σ₃ τ₂) =
      @ft_replay St Ev Stp σ₂ σ₃ τ₂.
  Proof.
    intros. apply replay_cat.
  Qed.

  (** ** 融贯性条件 3：AGM 成功性 *)
  Theorem coherence_agm_R2 :
      forall (σ₁ σ₂ : St) (e : Ev) (s : Stp σ₁ e σ₂),
      In (upd e) (levi_revision div' (belief σ₁) (upd e)).
  Proof.
    intros σ₁ σ₂ e s. exact (agmR2 σ₁ σ₂ e s).
  Qed.

  (** ** 融贯性条件 4：层叠限制 *)
  Theorem coherence_separation :
      forall (F : @KnowledgePSh St Ev Stp σ₀)
             (X Y : @TraceOb St Ev Stp σ₀)
             (f : @TraceMor St Ev Stp σ₀ X Y),
      @kp_ob St Ev Stp σ₀ F Y ->
      @kp_ob St Ev Stp σ₀ F X.
  Proof.
    intros F X Y f p. exact (@kp_res St Ev Stp σ₀ F X Y f p).
  Qed.

  (** ** 主融贯性定理 *)
  Theorem main_coherence_theorem :
      (forall σ σₙ (τ : FT σ σₙ),
       @ft_replay St Ev Stp σ σₙ τ = σₙ) /\
      (forall σ₁ σ₂ σ₃ (τ₁ : FT σ₁ σ₂) (τ₂ : FT σ₂ σ₃),
       @ft_replay St Ev Stp σ₁ σ₃
                  (@ft_cat St Ev Stp σ₁ σ₂ τ₁ σ₃ τ₂) =
       @ft_replay St Ev Stp σ₂ σ₃ τ₂) /\
      (forall σ₁ σ₂ e (s : Stp σ₁ e σ₂),
       In (upd e) (levi_revision div' (belief σ₁) (upd e))) /\
      (forall (F : @KnowledgePSh St Ev Stp σ₀)
              (X Y : @TraceOb St Ev Stp σ₀)
              (f : @TraceMor St Ev Stp σ₀ X Y),
       @kp_ob St Ev Stp σ₀ F Y -> @kp_ob St Ev Stp σ₀ F X).
  Proof.
    exact (conj coherence_replay
          (conj coherence_concat
          (conj coherence_agm_R2
                coherence_separation))).
  Qed.

End CoherenceProofs.

(** ** 统一性定理 *)
Theorem zx_calculus_unification :
    forall (ZXF : ZXFramework),
    exists (S : SSRS (zxf_State ZXF) (zxf_Event ZXF) (zxf_Step ZXF)),
    forall (σ₀ σ₁ : zxf_State ZXF) (e : zxf_Event ZXF),
    zxf_Step ZXF σ₀ e σ₁ ->
    In (@ssrs_update _ _ _ S e)
       (levi_revision (@ssrs_div _ _ _ S)
                      (@ssrs_belief _ _ _ S σ₀)
                      (@ssrs_update _ _ _ S e)).
Proof.
  intro ZXF.
  exists (zxf_ssrs ZXF).
  intros σ₀ σ₁ e s.
  exact (@ssrs_agm_R2 _ _ _ (zxf_ssrs ZXF) σ₀ σ₁ e s).
Qed.

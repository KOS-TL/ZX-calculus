(** * TraceElim：轨迹消去子
    对应文献 §3.2（TraceElim 消去子与计算规则）
*)

Require Import ZXCalculus.Core.Syntax.
Require Import ZXCalculus.Core.Traces.

Set Universe Polymorphism.

Section TraceElim.

  Variable State : Type.
  Variable Event : Type.
  Variable Step  : State -> Event -> State -> Prop.

  Variable P : forall (σ₀ σₙ : State),
      @FinTrace State Event Step σ₀ σₙ -> Type.

  Variable P_nil : forall (σ : State),
      P σ σ (@ft_nil State Event Step σ).

  Variable P_step : forall (σ₀ σ₁ σ₂ : State) (e : Event)
      (s : Step σ₀ e σ₁) (τ : @FinTrace State Event Step σ₁ σ₂),
      P σ₁ σ₂ τ ->
      P σ₀ σ₂ (@ft_step State Event Step σ₀ σ₁ σ₂ e s τ).

  Fixpoint TraceElim {σ₀ σₙ}
      (τ : @FinTrace State Event Step σ₀ σₙ) : P σ₀ σₙ τ :=
    match τ in @FinTrace _ _ _ s e return P s e τ with
    | ft_nil σ   => P_nil σ
    | ft_step s τ' => P_step _ _ _ _ s τ' (TraceElim τ')
    end.

  Theorem beta_nil : forall (σ : State),
      TraceElim (@ft_nil State Event Step σ) = P_nil σ.
  Proof. reflexivity. Qed.

  Theorem beta_step :
      forall (σ₀ σ₁ σ₂ : State) (e : Event)
             (s : Step σ₀ e σ₁)
             (τ : @FinTrace State Event Step σ₁ σ₂),
      TraceElim (@ft_step State Event Step σ₀ σ₁ σ₂ e s τ) =
      P_step σ₀ σ₁ σ₂ e s τ (TraceElim τ).
  Proof. reflexivity. Qed.

End TraceElim.

Section TraceEta.

  Variable State : Type.
  Variable Event : Type.
  Variable Step  : State -> Event -> State -> Prop.

  Variable P : forall (σ₀ σₙ : State),
      @FinTrace State Event Step σ₀ σₙ -> Type.

  Variable f g : forall (σ₀ σₙ : State)
      (τ : @FinTrace State Event Step σ₀ σₙ), P σ₀ σₙ τ.

  Hypothesis Hnil : forall (σ : State),
      f σ σ (@ft_nil State Event Step σ) = g σ σ (@ft_nil State Event Step σ).

  Hypothesis Hstep : forall (σ₀ σ₁ σ₂ : State) (e : Event)
      (s : Step σ₀ e σ₁) (τ : @FinTrace State Event Step σ₁ σ₂),
      f σ₁ σ₂ τ = g σ₁ σ₂ τ ->
      f σ₀ σ₂ (@ft_step State Event Step σ₀ σ₁ σ₂ e s τ) =
      g σ₀ σ₂ (@ft_step State Event Step σ₀ σ₁ σ₂ e s τ).

  Theorem trace_eta : forall (σ₀ σₙ : State)
      (τ : @FinTrace State Event Step σ₀ σₙ),
      f σ₀ σₙ τ = g σ₀ σₙ τ.
  Proof.
    intros σ₀ σₙ τ.
    induction τ as [σ | σ₀' σ₁' σ₂' e' s' τ' IH].
    - apply Hnil.
    - apply Hstep. exact IH.
  Qed.

End TraceEta.

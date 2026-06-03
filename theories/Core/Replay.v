(** * Replay：确定性重演定理 *)

Require Import ZXCalculus.Core.Syntax.
Require Import ZXCalculus.Core.Traces.
Require Import ZXCalculus.Core.ConcatAlgebra.

Set Universe Polymorphism.

Section Replay.

  Variable State : Type.
  Variable Event : Type.
  Variable Step  : State -> Event -> State -> Prop.

  Notation FT := (@FinTrace State Event Step).
  Notation ft_cat := (@ft_cat State Event Step).

  Fixpoint ft_replay {σ₀ σₙ : State} (τ : FT σ₀ σₙ) : State :=
    match τ with
    | ft_nil σ    => σ
    | ft_step _ τ' => ft_replay τ'
    end.

  Theorem deterministic_replay :
      forall (σ₀ σₙ : State) (τ : FT σ₀ σₙ),
      ft_replay τ = σₙ.
  Proof.
    intros σ₀ σₙ τ.
    induction τ as [σ | σ₀' σ₁' σ₂' e' s' τ' IH].
    - reflexivity.
    - exact IH.
  Qed.

  Theorem replay_cat :
      forall (σ₀ σ₁ σ₂ : State) (τ₁ : FT σ₀ σ₁) (τ₂ : FT σ₁ σ₂),
      ft_replay (ft_cat τ₁ τ₂) = ft_replay τ₂.
  Proof.
    intros σ₀ σ₁ σ₂ τ₁.
    induction τ₁ as [σ | σ₀' σ₁' σ₂' e' s' τ' IH].
    - intro τ₂. reflexivity.
    - intro τ₂. simpl. apply IH.
  Qed.

End Replay.

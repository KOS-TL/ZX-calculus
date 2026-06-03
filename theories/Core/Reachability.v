(** * Reachability：轨迹可达性
    对应文献 §3.4（轨迹-可达性对应定理）
*)

Require Import ZXCalculus.Core.Syntax.
Require Import ZXCalculus.Core.Traces.
Require Import ZXCalculus.Core.ConcatAlgebra.

Set Universe Polymorphism.

Section Reachability.

  Variable State : Type.
  Variable Event : Type.
  Variable Step  : State -> Event -> State -> Prop.

  Notation FT := (@FinTrace State Event Step).

  (** ** 可达性关系
      Reachable σ₀ σₙ：存在一条从 σ₀ 到 σₙ 的有限轨迹 *)
  Definition Reachable (σ₀ σₙ : State) : Prop :=
    exists τ : FT σ₀ σₙ, True.

  (** ** 轨迹-可达性对应

      正向：有轨迹则可达 *)
  Theorem trace_implies_reachable :
      forall (σ₀ σₙ : State) (τ : FT σ₀ σₙ),
      Reachable σ₀ σₙ.
  Proof.
    intros σ₀ σₙ τ.
    exists τ. exact I.
  Qed.

  (** ** 可达性的自反性（零步） *)
  Theorem reachable_refl : forall (σ : State), Reachable σ σ.
  Proof.
    intro σ. exists (@ft_nil State Event Step σ). exact I.
  Qed.

  (** ** 可达性的传递性（轨迹拼接） *)
  Theorem reachable_trans :
      forall (σ₀ σ₁ σ₂ : State),
      Reachable σ₀ σ₁ -> Reachable σ₁ σ₂ -> Reachable σ₀ σ₂.
  Proof.
    intros σ₀ σ₁ σ₂ [τ₁ _] [τ₂ _].
    exists (@ft_cat State Event Step σ₀ σ₁ τ₁ σ₂ τ₂). exact I.
  Qed.

  (** ** 单步可达 *)
  Theorem reachable_step :
      forall (σ₀ σ₁ : State) (e : Event),
      Step σ₀ e σ₁ -> Reachable σ₀ σ₁.
  Proof.
    intros σ₀ σ₁ e s.
    exists (@ft_step State Event Step σ₀ σ₁ σ₁ e s
            (@ft_nil State Event Step σ₁)).
    exact I.
  Qed.

End Reachability.

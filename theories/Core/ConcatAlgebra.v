(** * ConcatAlgebra：轨迹拼接代数
    对应文献 §3.3（轨迹拼接与前缀关系）
*)

Require Import ZXCalculus.Core.Syntax.
Require Import ZXCalculus.Core.Traces.

Set Universe Polymorphism.

Section ConcatAlgebra.

  Variable State : Type.
  Variable Event : Type.
  Variable Step  : State -> Event -> State -> Prop.

  Notation FT := (@FinTrace State Event Step).

  (** ** 轨迹拼接 *)
  Fixpoint ft_cat {σ₀ σ_mid : State}
      (τ₁ : FT σ₀ σ_mid) {σₙ : State} (τ₂ : FT σ_mid σₙ) : FT σ₀ σₙ :=
    match τ₁ in @FinTrace _ _ _ s e return FT e σₙ -> FT s σₙ with
    | ft_nil _    => fun τ => τ
    | ft_step s τ' => fun τ => ft_step s (ft_cat τ' τ)
    end τ₂.

  (** ** 单步轨迹 *)
  Definition ft_single {σ₀ σ₁ : State} (e : Event) (s : Step σ₀ e σ₁) :
      FT σ₀ σ₁ :=
    ft_step s (ft_nil σ₁).

  (** ** 左单位律 *)
  Theorem ft_cat_nil_l : forall (σ₀ σₙ : State) (τ : FT σ₀ σₙ),
      ft_cat (ft_nil σ₀) τ = τ.
  Proof. reflexivity. Qed.

  (** ** 右单位律 *)
  Theorem ft_cat_nil_r : forall (σ₀ σₙ : State) (τ : FT σ₀ σₙ),
      ft_cat τ (ft_nil σₙ) = τ.
  Proof.
    intros σ₀ σₙ τ.
    induction τ as [σ | σ₀' σ₁' σ₂' e' s' τ' IH].
    - reflexivity.
    - simpl. rewrite IH. reflexivity.
  Qed.

  (** ** 结合律 *)
  Theorem ft_cat_assoc :
      forall (σ₀ σ₁ σ₂ σ₃ : State)
             (τ₁ : FT σ₀ σ₁) (τ₂ : FT σ₁ σ₂) (τ₃ : FT σ₂ σ₃),
      ft_cat (ft_cat τ₁ τ₂) τ₃ = ft_cat τ₁ (ft_cat τ₂ τ₃).
  Proof.
    intros σ₀ σ₁ σ₂ σ₃ τ₁.
    induction τ₁ as [σ | σ₀' σ₁' σ₂' e' s' τ' IH].
    - intros τ₂ τ₃. reflexivity.
    - intros τ₂ τ₃. simpl. rewrite IH. reflexivity.
  Qed.

  (** ** 长度加法引理 *)
  Theorem ft_len_cat :
      forall (σ₀ σ₁ σ₂ : State) (τ₁ : FT σ₀ σ₁) (τ₂ : FT σ₁ σ₂),
      ft_len (ft_cat τ₁ τ₂) = ft_len τ₁ + ft_len τ₂.
  Proof.
    intros σ₀ σ₁ σ₂ τ₁.
    induction τ₁ as [σ | σ₀' σ₁' σ₂' e' s' τ' IH].
    - intro τ₂. reflexivity.
    - intro τ₂. simpl. rewrite IH. reflexivity.
  Qed.

  (** ** 前缀关系
      τ₁ 是 τ₂ 的前缀：起点相同、终点可能不同，存在延伸轨迹 *)
  Definition TracePrefix {σ₀ σ₁} (τ₁ : FT σ₀ σ₁)
      {σ₂} (τ₂ : FT σ₀ σ₂) : Prop :=
    exists (τ' : FT σ₁ σ₂), ft_cat τ₁ τ' = τ₂.

  Theorem prefix_refl : forall (σ₀ σₙ : State) (τ : FT σ₀ σₙ),
      TracePrefix τ τ.
  Proof.
    intros σ₀ σₙ τ.
    exists (ft_nil σₙ). apply ft_cat_nil_r.
  Qed.

  Theorem prefix_trans :
      forall (σ₀ σ₁ σ₂ σ₃ : State)
             (τ₁ : FT σ₀ σ₁) (τ₂ : FT σ₀ σ₂) (τ₃ : FT σ₀ σ₃),
      TracePrefix τ₁ τ₂ ->
      TracePrefix τ₂ τ₃ ->
      TracePrefix τ₁ τ₃.
  Proof.
    intros σ₀ σ₁ σ₂ σ₃ τ₁ τ₂ τ₃.
    intros [mid₁ H₁] [mid₂ H₂].
    exists (ft_cat mid₁ mid₂).
    rewrite <- ft_cat_assoc. rewrite H₁. exact H₂.
  Qed.

End ConcatAlgebra.

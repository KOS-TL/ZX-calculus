(** * FinTrace：有限执行轨迹的归纳族
    对应文献 §3（轨迹类型与 TraceElim）

    FinTrace Step σ₀ σₙ 表示从状态 σ₀ 出发到达状态 σₙ 的有限执行轨迹。
    轨迹长度通过 ft_len 函数计算（非类型索引），避免异质等式问题。
*)

Require Import ZXCalculus.Core.Syntax.

Set Universe Polymorphism.
Unset Implicit Arguments.

Section FinTraces.

  Variable State : Type.
  Variable Event : Type.
  Variable Step  : State -> Event -> State -> Prop.

  (** ** FinTrace 归纳族

      构造子：
      - ft_nil  : 零步空轨迹，起止状态相同
      - ft_step : 在轨迹前追加一步转移
  *)
  Inductive FinTrace : State -> State -> Type :=
    | ft_nil  : forall (σ : State),
        FinTrace σ σ
    | ft_step : forall (σ₀ σ₁ σ₂ : State) (e : Event),
        Step σ₀ e σ₁ ->
        FinTrace σ₁ σ₂ ->
        FinTrace σ₀ σ₂.

  (** ** 轨迹长度（计算函数）*)
  Fixpoint ft_len {σ₀ σₙ} (τ : FinTrace σ₀ σₙ) : nat :=
    match τ with
    | ft_nil _ => 0
    | ft_step _ _ _ _ _ τ' => S (ft_len τ')
    end.

End FinTraces.

Arguments ft_nil  {State Event Step} σ.
Arguments ft_step {State Event Step σ₀ σ₁ σ₂ e} _ _.
Arguments ft_len  {State Event Step σ₀ σₙ} _.

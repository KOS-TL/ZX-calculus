(** * ZX演算（知行演算）核心语法
    基于 Martin-Löf 依值类型论的轨迹索引动态知识演算
*)

Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.

Section ZXSyntax.

  Variable State : Type.
  Variable Event : Type.
  Variable Agent : Type.

  (** 转移谓词：σ --[e]--> σ' *)
  Variable Step : State -> Event -> State -> Prop.

  Notation "σ '--[' e ']-->' σ'" := (Step σ e σ')
    (at level 70, no associativity).

  (** Σ-类型的投影 *)
  Definition sigma_proj1 {A : Type} {B : A -> Type}
      (p : {x : A & B x}) : A :=
    projT1 p.

  Definition sigma_proj2 {A : Type} {B : A -> Type}
      (p : {x : A & B x}) : B (projT1 p) :=
    projT2 p.

End ZXSyntax.

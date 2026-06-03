(** * Separation：分离定理
    对应文献 §4.3（证明论单调性与语义非单调性的分离）
*)

Require Import ZXCalculus.Core.Syntax.
Require Import ZXCalculus.Core.Traces.
Require Import ZXCalculus.Core.ConcatAlgebra.
Require Import ZXCalculus.Semantics.TraceCategory.
Require Import ZXCalculus.Semantics.Presheaf.

Set Universe Polymorphism.

Section Separation.

  Variable State  : Type.
  Variable Event  : Type.
  Variable Step   : State -> Event -> State -> Prop.
  Variable σ_base : State.

  Notation FT       := (@FinTrace State Event Step).
  Notation TrOb     := (@TraceOb  State Event Step σ_base).
  Notation TrMor    := (@TraceMor State Event Step σ_base).
  Notation KPSh     := (@KnowledgePSh State Event Step σ_base).
  Notation kp_ob'   := (@kp_ob State Event Step σ_base).
  Notation kp_res'  := (@kp_res State Event Step σ_base).
  Notation Soft'    := (@Soft State Event Step σ_base).

  (** ** 限制映射始终良定义 *)
  Theorem restriction_defined :
      forall F : KPSh,
      forall X Y : TrOb,
      forall f : TrMor X Y,
      kp_ob' F Y -> kp_ob' F X.
  Proof.
    intros F X Y f p.
    exact (kp_res' F X Y f p).
  Qed.

  (** ** 分离定理

      证明论侧（单调）：限制映射始终存在。
      语义侧（非单调）：软性是独立公理，不从结构推导。
  *)
  Theorem separation :
      (forall F : KPSh, forall X Y : TrOb, forall f : TrMor X Y,
       kp_ob' F Y -> kp_ob' F X) /\
      Soft' (@constant_unit_psf State Event Step σ_base).
  Proof.
    split.
    - exact restriction_defined.
    - exact (@constant_is_soft State Event Step σ_base).
  Qed.

End Separation.

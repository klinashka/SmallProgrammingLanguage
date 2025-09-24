Require Import Coq.Init.Datatypes.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Inductive aexpr : Type :=
| AInt : nat -> aexpr
| APlus : aexpr -> aexpr -> aexpr
| AMult : aexpr -> aexpr -> aexpr
| AIf : bexpr -> aexpr -> aexpr -> aexpr
| AVar : string -> aexpr

with bexpr : Type := 
| BBool : bool -> bexpr
| BLt : aexpr -> aexpr -> bexpr
| BEq : aexpr -> aexpr -> bexpr.

Hint Constructors aexpr : core.
Hint Constructors bexpr : core.

(* 
    If we are to include variables, both the evaluation function and the small-step semantics require an environment, mapping strings to actual values. For the purpose of this language, the most suitable definition for an environment seems to be a function from strings to natural numbers. This is because it is by far the simplest, and the lack of mutation and of functions in the language suggests there is no need to go into other ways of representing variables and environments than the most straightforward one. 
*)
Definition env := string -> nat.

(* Evaluation function. *)
Fixpoint aeval (Γ : env) (e : aexpr) : nat := 
    match e with 
    | AInt x => x
    | APlus a b => (aeval Γ a) + (aeval Γ b)
    | AMult a b => (aeval Γ a) * (aeval Γ b)
    | AIf cond e1 e2 => if (beval Γ cond) then (aeval Γ e1) else (aeval Γ e2)
    | AVar x => Γ x
    end

    with 

beval (Γ : env) (b : bexpr) : bool := 
    match b with 
    | BBool b => b
    | BLt e1 e2 => (aeval Γ e1) <? (aeval Γ e2)
    | BEq e1 e2 => (aeval Γ e1) =? (aeval Γ e2)
    end.

(* Small-step semantics *)

Reserved Notation " x '~' Γ '~>ₐ' y" (at level 90).
Reserved Notation " x '~' Γ '~>ₑ' y" (at level 90).

Inductive astep (Γ : env) : aexpr -> aexpr -> Prop := 
| APlusInt : forall x y, (APlus (AInt x) (AInt y)) ~ Γ ~>ₐ AInt (x + y)
| APlus1 : forall x y x', x ~ Γ ~>ₐ x' -> APlus x y ~ Γ ~>ₐ APlus x' y
| APlus2 : forall x y y', y ~ Γ ~>ₐ y' -> APlus (AInt x) y ~ Γ ~>ₐ APlus (AInt x) y'
| AVarInt : forall x, AVar x ~ Γ ~>ₐ AInt (Γ x) 
| AMultInt : forall x y, AMult (AInt x) (AInt y) ~ Γ ~>ₐ AInt (x * y)
| AMult1 : forall x y x', x ~ Γ ~>ₐ x' -> AMult x y ~ Γ ~>ₐ AMult x' y
| AMult2 : forall x y y', y ~ Γ ~>ₐ y' -> AMult (AInt x) y ~ Γ ~>ₐ AMult (AInt x) y'
| AIfCond : forall b c1 c2 b', b ~ Γ ~>ₑ b' -> AIf b c1 c2 ~ Γ ~>ₐ AIf b' c1 c2
| AIfTrue : forall c1 c2, AIf (BBool true) c1 c2 ~ Γ ~>ₐ c1
| AIfFalse : forall c1 c2, AIf (BBool false) c1 c2 ~ Γ ~>ₐ c2

where "x '~' Γ '~>ₐ' y" := (astep Γ x y)

with bstep (Γ : env) : bexpr -> bexpr -> Prop := 
| BLtInt : forall x y, BLt (AInt x) (AInt y) ~ Γ ~>ₑ BBool (x <? y)
| BLt1 : forall x y x', x ~ Γ ~>ₐ x' -> BLt x y ~ Γ ~>ₑ BLt x' y
| BLt2 : forall x y y', y ~ Γ ~>ₐ y' -> BLt (AInt x) y ~ Γ ~>ₑ BLt (AInt x) y' 
| BEqInt : forall x y, BEq (AInt x) (AInt y) ~ Γ ~>ₑ BBool (x =? y)
| BEq1 : forall x y x', x ~ Γ ~>ₐ x' -> BEq x y ~ Γ ~>ₑ BEq x' y
| BEq2 : forall x y y', y ~ Γ ~>ₐ y' -> BEq (AInt x) y ~ Γ ~>ₑ BEq (AInt x) y' 

where "x '~' Γ '~>ₑ' y" := (bstep Γ x y).

Hint Constructors astep : core.
Hint Constructors bstep : core. 

(* This instruction generates a stronger induction principle for aexpr, including an inductive hypothesis including bexpr. This is necessary since AIf takes a bexpr parameter.  *)
Scheme aexpr_mut := Induction for aexpr Sort Prop
with bexpr_mut := Induction for bexpr Sort Prop.

Reserved Notation "x '~' Γ '~>ₐ*' y" (at level 90).
Reserved Notation "x '~' Γ '~>ₑ*' y" (at level 90).

Inductive astep_seq (Γ : env) : aexpr -> aexpr -> Prop := 
| ASRefl : forall a, a ~ Γ ~>ₐ* a
| ASTrans : forall a b c, a ~ Γ ~>ₐ b -> b ~ Γ ~>ₐ* c -> a ~ Γ ~>ₐ* c
where "x '~' Γ '~>ₐ*' y" := (astep_seq Γ x y).

Inductive bstep_seq (Γ : env) : bexpr -> bexpr -> Prop := 
| BSRefl : forall a, a ~ Γ ~>ₑ* a
| BSTrans : forall a b c, a ~ Γ ~>ₑ b -> b ~ Γ ~>ₑ* c -> a ~ Γ ~>ₑ* c
where "x '~' Γ '~>ₑ*' y" := (bstep_seq Γ x y).

Hint Constructors astep_seq : core.
Hint Constructors bstep_seq : core.

Lemma astep_seq_trans (Γ : env) (a b c : aexpr) : 
    a ~ Γ ~>ₐ* b -> b ~ Γ ~>ₐ* c -> a ~ Γ ~>ₐ* c.
Proof.
    intros H1 H2; induction H1; eauto.
Qed.

Lemma bstep_seq_trans (Γ : env) (a b c : bexpr) : 
    a ~ Γ ~>ₑ* b -> b ~ Γ ~>ₑ* c -> a ~ Γ ~>ₑ* c.
Proof.
    intros H1 H2; induction H1; eauto.
Qed.

Lemma astep_aeval (Γ : env) (e : aexpr) : e ~ Γ ~>ₐ* AInt (aeval Γ e).
Proof.
    (* Apply the stronger induction principle. The induction tactic does not suffice here. *)
    apply aexpr_mut with (P := fun x => x ~ Γ ~>ₐ* (AInt (aeval Γ x))) (P0 := fun x => x ~ Γ ~>ₑ* (BBool (beval Γ x))); 
    (* Get rid of the trivial cases of the induction: Aint, BBool and AVar. *)
    simpl; eauto.
    (* APlus *)
    - intros a1 H1 a2 H2.
      eapply astep_seq_trans with (b := APlus (AInt (aeval Γ a1)) a2).
      + induction H1; eauto.
      + apply astep_seq_trans with (b := APlus (AInt (aeval Γ a1)) (AInt (aeval Γ a2))); eauto.
        induction H2; eauto.
    (* AMult *)
    - intros a1 H1 a2 H2.
      eapply astep_seq_trans with (b := AMult (AInt (aeval Γ a1)) a2).
      + induction H1; eauto.
      + apply astep_seq_trans with (b := AMult (AInt (aeval Γ a1)) (AInt (aeval Γ a2))); eauto.
        induction H2; eauto.
    (* AIf *)
    - intros b Hb a1 Ha1 a2 Ha2.
      apply astep_seq_trans with (b := AIf (BBool (beval Γ b)) a1 a2).
      + induction Hb; eauto.
      + induction (beval Γ b);
        eauto.
    (* BLt *)
    - intros a1 Ha1 a2 Ha2.
      eapply bstep_seq_trans with (b := BLt (AInt (aeval Γ a1)) a2).
      + induction Ha1; eauto.
      + apply bstep_seq_trans with (b := BLt (AInt (aeval Γ a1)) (AInt (aeval Γ a2))); eauto.
        induction Ha2; eauto.
    (* BEq *)
    - intros a1 Ha1 a2 Ha2.
      eapply bstep_seq_trans with (b := BEq (AInt (aeval Γ a1)) a2).
      + induction Ha1; eauto.
      + apply bstep_seq_trans with (b := BEq (AInt (aeval Γ a1)) (AInt (aeval Γ a2))); eauto.
        induction Ha2; eauto.
Qed.
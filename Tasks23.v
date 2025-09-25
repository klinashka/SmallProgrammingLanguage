Require Import Coq.Init.Datatypes.

(*
    Note: In the development here, I use natural numbers instead of integers. 
    This change does not affect the essence of the proofs, and opted for this 
    simply to keep the number of imported libraries to a minimum. 
*)

(* Task 2: Define a data structure for expressions, and an evaluation function *)

Inductive expr : Type := 
| EVal : nat -> expr
| EPlus : expr -> expr -> expr
| EMult : expr -> expr -> expr.

Fixpoint eval (e : expr) : nat := 
   match e with 
    | EVal y => y
    | EPlus e1 e2 => (eval e1) + (eval e2)
    | EMult e1 e2 => (eval e1) * (eval e2)
    end.

(* 
    Task 3: Define small-step semantics for the language and prove that it agrees with 
    the evaluation function. 
*)

Reserved Notation "x ~> y" (at level 90).

(* Small-step semantics for the language. *)

Inductive step : expr -> expr -> Prop := 
| EPlusVal : forall x y, (EPlus (EVal x) (EVal y)) ~> (EVal (x + y))
| EPlus1 : forall e1 e2 e1', e1 ~> e1' -> (EPlus e1 e2) ~> (EPlus e1' e2)
| EPlus2 : forall x e2 e2', e2 ~> e2' -> (EPlus (EVal x) e2) ~> (EPlus (EVal x) e2')
| EMultVal : forall x y, (EMult (EVal x) (EVal y)) ~> (EVal (x * y))
| EMult1 : forall e1 e2 e1', e1 ~> e1' -> (EMult e1 e2) ~> (EMult e1' e2)
| EMult2 : forall x e2 e2', e2 ~> e2' -> (EMult (EVal x) e2) ~> (EMult (EVal x) e2')
where "x ~> y" := (step x y).

Hint Constructors step : core.

Reserved Notation "x ~>* y" (at level 90).


(* Inductive type representing a sequence of evaluation steps *)
Inductive step_seq : expr -> expr -> Prop := 
| StepRefl : forall e, e ~>* e
| StepTrans : forall e1 e2 e3, e1 ~> e2 -> e2 ~>* e3 -> e1 ~>*e3
where "x ~>* y" := (step_seq x y). 

Hint Constructors step_seq : core.

(* Helper lemma proving transitivity. *)
Lemma step_seq_trans (e1 e2 e3 : expr) : e1 ~>* e2 -> e2 ~>* e3 -> e1 ~>* e3.
Proof.
    intros H1 H2; induction H1; eauto.
Qed. 

(* Lemma stating that the small-step semantics and the evaluation function agree. *)
Lemma step_eval (e : expr) : e ~>* (EVal (eval e)).
Proof.
    induction e; simpl; auto.
    - eapply step_seq_trans with (e2 := EPlus (EVal (eval e1)) e2).
      + induction IHe1; eauto.
      + apply step_seq_trans with (e2 := EPlus (EVal (eval e1)) (EVal (eval e2))); eauto.
        induction IHe2; eauto.
    - apply step_seq_trans with (e2 := EMult (EVal (eval e1)) e2).
      + induction IHe1; eauto.
      + apply step_seq_trans with (e2 := EMult (EVal (eval e1)) (EVal (eval e2))); eauto. induction IHe2; eauto.
Qed.
(*
Define a simple programming language, its semantics,
and its typing rules, and then prove that well-typed
programs cannot go wrong. Specifically: 
*)
Require Import Arith.
Require Import Notations.
Require Import Logic.

(* (a) Define var as a synonym for the natural numbers. *)
Definition var := nat.

(* (b) Define an inductive type exp of expressions,
   containing natural number constants, natural number
   addition, pairing of two other expressions,
   extraction of the first component of a pair,
   extraction of the second component of a pair,
   and variables (based on the var type you defined). *)
Inductive exp : Set :=
| Const : nat -> exp
| Sum   : exp -> exp -> exp
| Tuple : exp -> exp -> exp
| Extr1 : exp -> exp
| Extr2 : exp -> exp
| Var   : var -> exp
.

(* (c) Define an inductive type cmd of commands, containing
   expressions and variable assignments. A variable assignment
   node should contain the variable being assigned, the
   expression being assigned to it, and the command to run
   afterward. *)
Inductive cmd :=
| Exp    : exp -> cmd
| Assign : var -> exp -> cmd -> cmd
.

(* (d) Define an inductive type val of values, containing natural
   number constants and pairings of values. *)
Inductive val := 
| Val   : nat -> val
| VPair : val -> val -> val
.

(* (e) Define a type of variable assignments, which assign a value to
    each variable. *)
Definition assign := var -> val.

(* (f) Define a big-step evaluation relation eval, capturing what
   it means for an expression to evaluate to a value under a]
   particular variable assignment. “Big step” means that the
   evaluation of every expression should be proved with
   a single instance of the inductive predicate you will define.
   For instance, “1 + 1 evaluates to 2 under assignment va” should
   be derivable for any assignment va. *)



Fixpoint eval (e : exp) (a : assign) (v : val) : Prop :=
match e with
| Const n             => v = (Val n)
| Var n               => v = a n
| Extr1 e             => exists v2, eval e a (VPair v v2)
| Extr2 e             => exists v1, eval e a (VPair v1 v)
| Sum e1 e2           =>
      exists v1 v2, eval e1 a (Val v1) /\ eval e2 a (Val v2) /\ v = Val(v1+v2)
| Tuple e1 e2         =>
      exists v1 v2, eval e1 a v1 /\ eval e2 a v2 /\ v = VPair v1 v2
end.

(* (g) Define a big-step evaluation relation run, capturing
   what it means for a command to run to a value under a
   particular variable assignment. The value of a command
   is the result of evaluating its final expression. *)
Definition env_add (a : assign) (v : var) (l : val) (x : var) :=
    if eq_nat_dec x v then l else a x
.

Fixpoint run (c : cmd) (a : assign) (v : val) : Prop :=
match c with
| Exp e          => eval e a v
| Assign vr e c2 => exists ev, eval e a ev /\ run c2 (env_add a vr ev) v
end.

(* (h) Define a type of variable typings, which are like
   variable assignments, but map variables to types instead
   of values. You might use polymorphism to share some code
   with your variable assignments. *)
Inductive type := 
| NatT
| TupleT : type -> type -> type
.
Definition typing := var -> type.

(* (i) Define typing judgments for expressions, values,
   and commands. The expression and command cases will be
   in terms of a typing assignment. *)
Fixpoint typeE (e : exp) (t : typing) (tp : type) : Prop :=
match e with
| Const _     => tp = NatT
| Sum e1 e2   => typeE e1 t NatT /\ typeE e2 t NatT /\ tp = NatT
| Extr1 e     => exists t2, typeE e t (TupleT tp t2)
| Extr2 e     => exists t1, typeE e t (TupleT t1 tp)
| Tuple e1 e2 =>
       exists t1 t2, typeE e1 t t1 /\ typeE e2 t t2 /\ tp = TupleT t1 t2
| Var v       => t v = tp
end.

Fixpoint typeV (v : val) (tp : type) : Prop :=
match v with
| Val _ => tp = NatT
| VPair v1 v2 =>
       exists t1 t2, typeV v1 t1 /\ typeV v2 t2 /\ tp = TupleT t1 t2
end.

Definition type_add (t : typing) (v : var) (tp : type) : typing :=
    t (* fun x => if eq_nat_dec x v then tp else t x *)
.

Fixpoint typeC (c : cmd) (t : typing) (tp : type) : Prop :=
match c with
| Exp e          => typeE e t tp
| Assign v e c2 => exists tp2, typeE e t tp2 /\ typeC c2 (type_add t v tp2) tp
end.

(* (j) Define a predicate varsType to express when a variable
   assignment and a variable typing agree on the types of
   variables. *)
Definition varsType (a : assign) (t : typing) :=
forall (v : var), typeV (a v) (t v)
.

(* (k) Prove that any expression that has type t under variable
   typing vt evaluates under variable assignment va to some value
   that also has type t in vt, as long as va and vt agree. *)

Lemma tupleT : forall e1 e2 t tp, typeE (Tuple e1 e2) t tp
     -> exists t1 t2, tp = TupleT t1 t2.
intros.
simpl in H.
repeat destruct H.
destruct H0.
rewrite H1.
exists x; exists x0; trivial.
Qed.

Lemma ext1T : forall e t tp, typeE (Extr1 e) t tp -> exists t2,
     typeE e t (TupleT tp t2).
intros.
simpl in H.
repeat destruct H.
exists x; trivial.
Qed.

Lemma ext1E : forall e a vl, eval (Extr1 e) a vl ->
        exists v1 v2, eval e a (VPair v1 v2).
intros.
simpl in H.
repeat destruct H.
exists vl; exists x; trivial.
Qed.

Theorem well_typed: forall (vt : typing) (va : assign), (varsType va vt) ->
          forall (e : exp),
          forall tp vl,
          (typeE e vt tp) ->
           eval e va vl ->
                    typeV vl tp.
intro; intro; intro.
induction e.

+ simpl; intros.
  rewrite H0; rewrite H1.
  simpl; trivial.

+ simpl.
  intros.
  destruct H0.
  destruct H2.
  repeat destruct H1.
  destruct H4.
  rewrite H5.
  rewrite H3.
  simpl; trivial.

+ simpl.
  intros.
  repeat destruct H0.
  destruct H2.
  repeat destruct H1.
  destruct H4.
  rewrite H5.
  rewrite H3.
  simpl.
  exists x; exists x0; auto.

+ intros.
  simpl in H0; simpl in H1.
  destruct H0; destruct H1.
  assert (typeV (VPair vl x0) (TupleT tp x)).
  apply IHe; auto.
  simpl in H2.
  repeat destruct H2.
  destruct H3.
  injection H4; intros.
  rewrite H6.
  auto.

+ intros.
  simpl in H0; simpl in H1.
  destruct H0; destruct H1.
  assert (typeV (VPair x0 vl) (TupleT x tp)).
  apply IHe; auto.
  simpl in H2.
  repeat destruct H2.
  destruct H3.
  injection H4; intros.
  rewrite H5.
  auto.

+ intros.
  rewrite H1.
  rewrite <- H0.
  apply H.
Qed.


(* (l) Prove that any command that has type t under variable typing vt evaluates
   under variable assignment va to some value that also has type t in vt,
   as long as va and vt agree.  *)

Lemma add_safe : forall e t a tp vl, varsType a t ->
      eval e a vl -> typeV vl tp -> forall x,
      varsType (env_add a x vl) (type_add t x tp).
intros.
intro.
compare x v.
+ intros.
  rewrite e0; clear e0.
  admit.

+ intros.
  admit.
Qed.


Theorem cmd_types :  forall (tp : type) (vl : val) (c : cmd),
        forall (vt : typing) (va : assign), (varsType va vt) ->
        (typeC c vt tp) /\ (run c va vl) -> typeV vl tp.
intro; intro.
induction c.

+ intros.
  simpl in H0; destruct H0.
  apply well_typed with (vt := vt) (va := va) (e := e); auto.

+ intros.
  destruct H0.

  simpl in H0.
  repeat destruct H0.
  simpl in H1.
  repeat destruct H1.
  
  apply IHc with (vt := type_add vt v x) (va := env_add va v x0).
  apply add_safe with (e := e); auto.
  apply well_typed with (vt := vt) (va := va) (e := e); auto.
  auto.
Qed.

(*
(a) One easy way of defining variable assignments and typings
    is to define both as instances of a polymorphic map type.
    The map type at parameter T can be defined to be the type
    of arbitrary functions from variables to T. A helpful
    function for implementing insertion into such a functional
    map is eq_nat_dec, which you can make available with
    
    Require Import Arith.
    
    eq_nat_dec has a dependent type that tells you that it
    makes accurate decisions on whether two natural numbers
    are equal, but you can use it as if it returned a boolean, e.g.,
    if eq_nat_dec n m then E1 else E2.

(b) If you follow the last hint, you may find yourself writing a
    proof that involves an expression with eq_nat_dec that you
    would like to simplify. Running destruct on the particular
    call to eq_nat_dec should do the trick. You can automate
    this advice with a piece of Ltac:
    
    match goal with
    | [ ` context[eq_nat_dec ?X ?Y ] ] ⇒ destruct (eq_nat_dec X Y )
    end
*)








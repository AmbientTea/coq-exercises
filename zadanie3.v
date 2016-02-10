Require Import Permutation.
Require Import Quote.
Require Import List.
Require Import Morphisms.
Require Import Setoid.
Require Import Coq.Sorting.Mergesort.
Require Import Coq.Arith.Compare_dec.
Module Import NatSort := Sort NatOrder.
Set Implicit Arguments.

Infix "==" := (Permutation) (at level 70) : type_scope.

(***************************)
Inductive listexp :=
| Nil  : listexp
| List : nat -> listexp
| Rev  : listexp -> listexp
| App  : listexp -> listexp -> listexp
.

Fixpoint interp T (xs : list (list T)) (e : listexp)  :=
match e  with
| List ind  => nth ind xs nil
| Rev l     => rev (interp xs l)
| App l1 l2 => interp xs l1 ++ interp xs l2
| Nil       => nil
end.

Ltac insert l e :=
match l with
| nil     => constr:(e :: nil)
| e :: ?t  => l
| ?h :: ?t => let t' := insert t e in constr:(h :: t')
end.

Ltac createDict env T :=
match T with
| rev ?t     => createDict env t
| ?t1 ++ ?t2 => let env' := createDict env t1 in createDict env' t2
| ?h :: ?t   => let env' := createDict env t in insert env' (h::nil)
| _          => let env' := insert env T in env'
end.

Ltac find l e :=
match l with
| e :: _ => O
| _ :: ?t => let n := find t e in constr:(S n)
end.

Ltac reifyTerm env T :=
match T with
| nil        => Nil
| rev ?le    => let r := reifyTerm env le in constr:(Rev r)
| ?l1 ++ ?l2 => let r1 := reifyTerm env l1 in
                let r2 := reifyTerm env l2 in
                    constr:(App r1 r2)
| ?h :: ?t   => let hn := find env (h::nil) in
                let tr := reifyTerm env t in
                    constr:(App (List hn) tr)
| ?l         => let n := find env l in constr:(List n)
end.

Ltac reify :=
match goal with
| [ |- ?e1 == ?e2 ] => let t := type of e1 in
                       let emptyEnv := constr:(@nil t) in
                       let env  := createDict emptyEnv e1 in
                       let env' := createDict env e2 in
                       let r1   := reifyTerm env' e1 in
                       let r2   := reifyTerm env' e2 in
                       change (interp env' r1 == interp env' r2)
end.

Fixpoint flatten t :=
match t with
| Nil       => nil
| Rev t'    => flatten t'
| App t1 t2 => flatten t1 ++ flatten t2
| List n    => n :: nil
end.

Fixpoint inflate l :=
match l with
| h :: t => App (List h) (inflate t)
| nil => Nil
end.

Definition kanonik t := inflate (sort (flatten t)).

Section PermLemmas.
Variable A : Type.
Notation permutation := (@Permutation _) (only parsing).
Global Instance appPermutationProper :
    Proper (permutation ==> permutation ==> permutation) (@app A).
repeat red.
intros.
apply Permutation_app; auto.
Qed.

Lemma concat_flatten_ok : forall T (xs : list(list T)) l1 l2,
    interp xs (inflate (l1 ++ l2)) == interp xs (inflate l1) ++ interp xs (inflate l2).
intros.
induction l1.
+ auto.
+ simpl.
  rewrite <- app_assoc.
  apply Permutation_app_head.
  exact IHl1.
Qed.

Lemma inflate_flatten_ok : forall T (xs : list(list T)) l,
      interp xs (inflate (flatten l)) == interp xs l.
intros.
induction l.
+ trivial.
+ simpl.  
  rewrite app_nil_r.
  trivial.
+ simpl.
  rewrite IHl.
  apply Permutation_rev.
+ simpl.
  rewrite concat_flatten_ok.
  apply Permutation_app; trivial.
Qed.

Lemma Permutation_ok : forall T (xs : list (list T)) l1 l2,
    l1 == l2 -> interp xs (inflate l1) == interp xs (inflate l2).
intros.
induction H.
+ trivial.
+ simpl.
  apply Permutation_app_head.
  trivial.
+ simpl.
  repeat rewrite app_assoc.
  apply Permutation_app_tail.
  apply Permutation_app_comm.
+ rewrite <- IHPermutation2.
  rewrite <- IHPermutation1.
  trivial. 
Qed.

Lemma Sort_ok : forall T (xs : list (list T)) l,
    interp xs (inflate l) == interp xs (inflate (sort l)).
intros.
apply Permutation_ok.
apply Permuted_sort.
Qed.

Lemma kanonik_ok : forall (T: Type) (xs: list(list T)) (l: listexp),
      interp xs (kanonik l) == interp xs l.
intros.
change (interp xs (inflate (sort (flatten l))) == interp xs l).
rewrite <- Sort_ok.
apply inflate_flatten_ok.
Qed.

Lemma two_kanonik : forall (T: Type) (xs: list(list T)) (e1 e2: listexp),
  interp xs (kanonik e1) == interp xs (kanonik e2) ->
  interp xs e1 == interp xs e2.
intros; rewrite <- kanonik_ok.
rewrite H; apply kanonik_ok.
Qed.
End PermLemmas.

(* taktyka *)

Ltac solve_perm :=
  reify;
  apply two_kanonik;
  reflexivity.

(*  przyklady  *)
Theorem th1 : forall (a b c d e : list nat),
    rev (a ++ rev b ++ c ++ rev (d ++ e) ++ rev a) 
        ==
    rev (a ++ b) ++ c ++ rev (d ++ rev (rev e ++ rev a)).
intros.
solve_perm.
Qed.

Fixpoint insertIn l e :=
match l with
| nil    => e :: nil
| h :: t => match nat_compare e h with Lt => e :: h :: t | _ => h :: insertIn t e end
end.

Fixpoint insertionSort ls lt :=
match ls with
| nil    => lt
| h :: t => insertIn (insertionSort t lt) h
end.

Lemma insert_ok : forall l a, insertIn l a == a :: l.
intros.
induction l.
simpl; solve_perm.
simpl.
destruct (nat_compare a a0).
rewrite IHl; solve_perm.
solve_perm.
rewrite IHl; solve_perm.
Qed.


Theorem sortPerm : forall l, l == insertionSort l nil.
intros.
induction l.
simpl; solve_perm.
symmetry.
simpl.
rewrite insert_ok.
rewrite <- IHl.
solve_perm.
Qed.






















Load "DepList.v".
Require Import Coq.Bool.Bool.
(*
Write a dependently typed interpreter for a simple programming
language with ML-style pattern-matching. The object language is
defined informally by this grammar:
    t ::= bool | t + t
    p ::= x | b | inl p | inr p
    e ::= x | b | inl e | inr e | case e of [p ⇒ e]* [_ ⇒ e]
The non-terminal x stands for a variable, and b stands for a
boolean constant. The production for case expressions means
that a pattern-match includes zero or more pairs of patterns
and expressions, and a default case.

your definition of expressions should use dependent types and
de Bruijn indices to combine syntax and typing rules, such that
the type of an expression tells the types of variables that
are in scope. You should implement a simple recursive function
ranslating types t to Set, and your interpreter should produce
values in the image of this translation. 
*)

Inductive type :=
| BoolT
| EitherT : type -> type -> type
.

Fixpoint typeDenote (t: type) : Set :=
match t with
| BoolT         => bool
| EitherT t1 t2 => sum (typeDenote t1) (typeDenote t2)
end.

Compute typeDenote (EitherT BoolT (EitherT BoolT BoolT)).

Inductive pattern : list type -> type -> Set :=
| PConst : forall (b: bool), pattern nil BoolT
| PVal   : forall t, pattern (t::nil) t
| PInl   : forall ts t t', pattern ts t -> pattern ts (EitherT t t')
| PInr   : forall ts t t', pattern ts t -> pattern ts (EitherT t' t)
.

(* An exp ts t will stand for an expression that has type t
and whose free variables have types in the list ts. *)
Inductive exp : list type -> type -> Set :=
| EConst : forall ts, bool -> exp ts BoolT
| EVar   : forall ts t, member t ts -> exp ts t
| EInl   : forall ts t t', exp ts t -> exp ts (EitherT t t')
| EInr   : forall ts t t', exp ts t -> exp ts (EitherT t' t)
| ECase  : forall ts t ft, exp ts t ->
           list (sigT2 (fun tpl => pattern tpl t)
                       (fun tpl => exp (ts++tpl) ft))
           -> exp ts ft -> exp ts ft
.

Print exp.

Definition pairT ft ts t :=
sigT2 (fun tpl => pattern tpl t)
      (fun tpl => exp (ts++tpl) ft).


Fixpoint patternMatch t ptl (p: pattern ptl t) (v: typeDenote t)
      : option (hlist typeDenote ptl) := 
match p in pattern ptl' t'
return typeDenote t' -> option (hlist typeDenote ptl') with
| PConst ev  => fun v => if eqb v ev then Some HNil else None
| PVal _ => fun v => Some (v ::: HNil)
| PInl _ _ _ p => fun v => match v with
                | inl v => patternMatch p v
                | _ => None
                end
| PInr _ _ _ p => fun v => match v with
                | inr v => patternMatch p v
                | _ => None
                end
end v.

Fixpoint expDenote ts t (e : exp ts t) : hlist typeDenote ts -> typeDenote t :=
match e in exp ts' t' return hlist typeDenote ts' -> typeDenote t' with
| EConst _ b           => fun _ => b
| EVar _ _ mem         => fun s => hget s mem
| EInl _ _ _ e         => fun s => inl (expDenote e s)
| EInr _ _ _ e         => fun s => inr (expDenote e s)
| ECase _ _ _ e nil fe => fun s => expDenote fe s
| ECase cts ct cft e ptl fe => fun s => let v := expDenote e s in
         (fix patternChoose (v: typeDenote ct) ptl :=
              match ptl with
              | nil => expDenote fe s
              | (existT2 penv p pe)::tp => match patternMatch p v with
                      | None => patternChoose v tp
                      | Some env => expDenote pe (s +++ env)
                      end
              end
         ) v ptl
end.

Definition patternPair penv t ft ts (p : pattern penv t) (e : exp (ts++penv) ft) :
     (sigT2 (fun tpl => pattern tpl t) (fun tpl => exp (ts++tpl) ft)) :=
existT2 (fun tpl => pattern tpl t)
        (fun tpl => exp (ts++tpl) ft)
        (penv) (p) (e)
.

Compute (expDenote (EInl BoolT (EConst nil true))) HNil.

Compute (expDenote
    (EInl BoolT
        (ECase
            (EInr BoolT (EConst nil true))
            (*  existT2 : forall x:A, P x -> Q x -> sigT2 P Q. *)
            ((patternPair (nil)
                          (PVal (EitherT BoolT BoolT))
                          (EInl BoolT (EConst ((EitherT BoolT BoolT)::nil) (false)))
            )::(patternPair (nil)
                          (PVal (EitherT BoolT BoolT))
                          (EVar (HFirst)  )
            )::nil)
            (EInr BoolT (EConst nil false))
        )
     )
) HNil.

Compute (expDenote
    (ECase
         (EInr BoolT (EConst nil true))
         ((patternPair ( nil)
                      (PVal (EitherT BoolT BoolT))
                      (EVar HFirst))::nil)
         (EInr BoolT (EConst nil false)))
) HNil.


Compute (expDenote
    (ECase
         (EInr BoolT (EConst nil true))
         ((patternPair nil
                      (PInr BoolT (PVal BoolT))
                      (EVar HFirst))::nil)
         (EConst nil false))
) HNil.


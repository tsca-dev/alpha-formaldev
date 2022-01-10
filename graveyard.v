From mathcomp Require Import all_ssreflect.
From Michocoq Require Import semantics util macros.
Import syntax comparable error.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition parameter_ty := bytes.
Definition storage_ty := bytes.

Module graveyard(C : ContractContext).
Module semantics := Semantics C. Import semantics.
Require Import String.
Open Scope string_scope.

Definition graveyard: full_contract false parameter_ty None storage_ty :=
  DUP;;
  {
    CAR;
    UNPACK unit;
    IF_NONE {PUSH _ (Comparable_constant syntax_type.string "unpack param");
             FAILWITH}
            {DROP1}
  };;;
  {
    CDR;
    NIL operation;
    PAIR
  }.

Lemma graveyard_correct
      (env : @proto_env (Some (Comparable_type parameter_ty, None)))
      (fuel : Datatypes.nat)
      (param : data bytes)
      (storage : data bytes)
      (psi : stack (pair (list operation) storage_ty ::: [::]) -> Prop) :
fuel > 3 ->
precond (eval_seq env graveyard fuel ((param, storage), tt)) psi
<-> unpack env unit param <> None /\ psi ([::], storage, tt).
Proof.
  move=> F; have<-: 4 + (fuel - 4) = fuel by rewrite addnC subnK.
  split => H.
  + move: H.
    rewrite eval_seq_precond_correct /eval_seq_precond /=.
    by case => [] [] [] ->.
  + rewrite eval_seq_precond_correct /eval_seq_precond /=.
    case: H; case:(unpack env unit param) => // a _ ?.
    by exists a.
Qed.

Lemma graveyard_invocable
      (env : @proto_env (Some (Comparable_type parameter_ty, None)))
      (fuel : Datatypes.nat)
      (param : data bytes)
      (storage : data bytes)
      (psi : stack (pair (list operation) storage_ty ::: [::]) -> Prop) :
fuel > 3 ->
unpack env unit param <> None ->
precond (eval_seq env graveyard fuel ((param, storage), tt)) psi
<-> psi ([::], storage, tt).
Proof.
  move=> F up.
  split.
   by case/(graveyard_correct _ _ _ _ F).
  move=> pt.
  by apply/graveyard_correct.
Qed.
End graveyard.

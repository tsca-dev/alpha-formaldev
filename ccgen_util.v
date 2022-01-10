From mathcomp Require Import all_ssreflect.
From Michocoq Require Import semantics util macros.
Import syntax comparable error.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import String.
Open Scope string_scope.

Definition make_typed_validation_snippet genparam_ty
 (typed_validation_snippet :
    instruction_seq None false (genparam_ty ::: mutez ::: [::]) [::])
  : instruction_seq None false (pair bytes mutez ::: [::])
                    (pair bytes mutez ::: [::]) :=
  {
    DUP; DIP1 {UNPAIR; UNPACK genparam_ty};
    DIP1 {IF_NONE {PUSH _ (Comparable_constant syntax_type.string "genparam is of wrong type"); FAILWITH}
                  typed_validation_snippet}
  }.

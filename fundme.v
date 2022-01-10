From mathcomp Require Import all_ssreflect.
From Michocoq Require Import semantics util macros.
Import syntax comparable error.
Require Import ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import String.
Open Scope string_scope.
Import Notations.

Definition parameter_ty :=
or (or unit None unit None) None
  (or (Comparable_type address) None
     (or (Comparable_type nat) None (Comparable_type nat) None) None) None.
Definition storage_ty :=
pair (pair (option (Comparable_type mutez)) (Comparable_type address))
  (pair (Comparable_type mutez)
     (list (pair (Comparable_type address) (Comparable_type mutez)))).
Module fundme (C : ContractContext).
Module semantics := Semantics C. Import semantics.

Definition transfer error {A S}
  : instruction_seq A false
    (address ::: mutez ::: S)
    (operation ::: S) :=
  {
    CONTRACT None unit;
    IF_NONE {PUSH syntax_type.string error; FAILWITH}
            {SWAP; PUSH unit Unit; TRANSFER_TOKENS}
  }.

Definition refundall {A S}
  : instruction_seq A false
    (storage_ty ::: S)
    ((pair (list operation) storage_ty) ::: S) :=
  {
    UNPAIR;
    DIP1 {UNPAIR};
    DIP1 {SWAP}; SWAP;
    DIIIP {NIL (pair address mutez)};
    DIIP {PAIR};
    DIP1 {PAIR};
    @MAP _ (list (pair address mutez)) _ (map_list _ _) _
         (UNPAIR;; transfer "refund account invalid or of unsupported type"); PAIR
  }.
Open Scope michelson.

Definition isolate {A S}
  : instruction_seq A false
    (nat ::: list (pair address mutez) ::: S)
    ((pair (pair address mutez) (list (pair address mutez))) ::: S) :=
  {
    SWAP; DIP1 {PUSH _ (Pair (Nat_constant 0) (Pair None_ (Concrete_list [::])))};
    ITER
      {DIP1 {UNPAIR}; DUUUUP; DUUUP; SUB; EQ;
       IF_TRUE {SWAP; PUSH nat (Nat_constant 1); ADD; DIIP {UNPAIR}; DIIP {DROP1}; DIP1 {SOME; PAIR}; PAIR}
               {SWAP; PUSH nat (Nat_constant 1); ADD; DIIP {UNPAIR}; DIP1 {SWAP}; DIIP {CONS}; DIP1 {PAIR}; PAIR}
       : instruction A false (_ ::: iter_elt_type (list (pair address mutez)) (iter_list (pair address mutez)) ::: _) _};
    UNPAIR; DROP1; UNPAIR; DIIP {DROP1}; IF_NONE {PUSH syntax_type.string "index out of range"; FAILWITH} {PAIR}
  }.

Definition refund1 {A S}
  : instruction_seq A false
    (nat ::: storage_ty ::: S)
    ((pair (list operation) storage_ty) ::: S) :=
  {
    DIP1 {UNPAIR}; DIIP {UNPAIR}; DIIP {SWAP}; DIP1 {SWAP}
  } ;;; isolate ;;;
  {
    UNPAIR;
    DIP1 {SWAP}; DIIP {SWAP}; DIIP {PAIR}; DIP1 {PAIR}; UNPAIR
  } ;;; transfer "refund account invalid or of unsupported type";;;
  {
    DIP1 {NIL operation}; CONS; PAIR
  }.

Definition droprefund1 {A S}
  : instruction_seq A false
    (nat ::: storage_ty ::: S)
    ((pair (list operation) storage_ty) ::: S) :=
  {
    DIP1 {UNPAIR}; DIIP {UNPAIR}; DIIP {SWAP}; DIP1 {SWAP}
  };;; isolate;;;
  {
    UNPAIR;
    DIP1 {SWAP}; DIIP {SWAP}; DIIP {PAIR}; DIP1 {PAIR};
    DROP1; NIL operation; PAIR
  }.

Definition withdraw {A S}
  : instruction_seq A false
    (address ::: mutez ::: storage_ty ::: S)
    ((pair (list operation) storage_ty) ::: S) :=
  DIIP {UNPAIR;
        DIP1 {UNPAIR};
        DIP1 {SWAP}; SWAP;
        DIIIP {PUSH (list (pair address mutez)) (Concrete_list nil)};
        DIIP {PAIR};
        DIP1 {PAIR}};;
  transfer "withdraw account invalid or of unsupported type";;;
  {
    DIP1 {DROP1}; DIP1 {NIL operation};
    CONS; PAIR
  }.

Definition fund {A S}
  : instruction_seq A false
    (address ::: mutez ::: storage_ty ::: S)
    ((pair (list operation) storage_ty) ::: S) :=
  {
    DIIP {UNPAIR; UNPAIR; DUP}; DIIIP {PAIR; PAIR}; DIP1 {SWAP}; SWAP; DIP1 {SWAP}; DIIP {SWAP};
    IF_NONE {DIP1 {NIL operation}}
            {DIIP {DUP; UNPAIR; DROP1; UNPAIR; DIP1 {DROP1}}; DIP1 {DUP}; DIIP {@ADD _ _ _ (Mk_add _ _ _ Add_variant_tez_tez) _}; SWAP; DIP1 {DUP}; DIIP {COMPARE; LT}; DIP1 {SWAP}; SWAP;
             IF_ IF_bool
                 {DUP; DIP1 {SWAP}; DIP1 {@SUB _ _ _ (Mk_sub _ _ _ Sub_variant_tez_tez) _}; DIP1 {DUP}; @SUB _ _ _ (Mk_sub _ _ _ Sub_variant_tez_tez) _; DIP1 (SEQ DUUUP (transfer "handling error: cannot return exceeded fund")); DIIP {NIL operation}; DIP1 {CONS}}
                 {DIP1 {DROP1}; DIP1 {NIL operation}}}; DIIP {SWAP};
    DIP1 {SWAP}; SWAP; DIP1 {DUP}; PAIR; DIIIP {UNPAIR}; DIIIIP {UNPAIR}; DIIIP {SWAP}; DIIP {SWAP}; DIP1 {@ADD _ _ _ (Mk_add _ _ _ Add_variant_tez_tez) _} ; DIIIP {SWAP}; DIIP {SWAP}; DIP1 {SWAP}; CONS; SWAP; PAIR; SWAP; DIP1 {SWAP; PAIR}; PAIR
  }.

Definition canfund {A S} :
    instruction_seq A false
    (storage_ty ::: S)
    (bool ::: S) :=
  {
    UNPAIR; UNPAIR; DIP1 {DROP1};
    IF_NONE {DROP1; PUSH _ True_}
            {DIP1 {UNPAIR; DIP1 {DROP1}};
             Instruction_opcode (@COMPARE _ mutez _);
             GT}
  }.

Definition valfund {A S} :
    instruction_seq A false
    (storage_ty ::: S)
    ((pair (list operation) storage_ty) ::: S) :=
  DUP;; canfund;;;
  {
    IF_ IF_bool ({AMOUNT; SENDER};;; fund)
        {PUSH syntax_type.string "funding cap already reached"; FAILWITH}
  }.

Definition fundme : full_contract false parameter_ty None storage_ty :=
  {
    DUP; CAR; DIP1 {CDR};
    IF_LEFT
      {IF_LEFT (DROP1;; valfund)
               {DROP1; DUP; CAR; CDR; SENDER; COMPARE; EQ;
                IF_TRUE refundall {PUSH syntax_type.string "only contract owner can attempt a refund"; FAILWITH}}}
      {IF_LEFT
         {DIP1 {DUP; CAR; CDR; SENDER; COMPARE; EQ}; SWAP;
          IF_TRUE ({BALANCE; SWAP};;; withdraw)
                  {PUSH syntax_type.string "only contract owner can perform a withdraw"; FAILWITH}}
         {IF_LEFT
            {DIP1 {DUP; CAR; CDR; SENDER; COMPARE; EQ}; SWAP;
              IF_TRUE refund1 {PUSH syntax_type.string "only contract owner can attempt a refund"; FAILWITH}}
            {DIP1 {DUP; CAR; CDR; SENDER; COMPARE; EQ}; SWAP;
             IF_TRUE droprefund1 {PUSH syntax_type.string "only contract owner can attempt a refund"; FAILWITH}}}}
  }.
End fundme.

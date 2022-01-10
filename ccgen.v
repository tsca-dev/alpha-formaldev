From mathcomp Require Import all_ssreflect.
From Michocoq Require Import semantics util macros.
Import syntax comparable error.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module ccgen(C : ContractContext).
Module semantics := Semantics C. Import semantics.
Require Import String.
Open Scope string_scope.

Definition reconstr_op {self_type A B}
           (op: @opcode self_type A B) : @opcode None A B :=
  match op with
  | APPLY _ _ _ _ b => @APPLY _ _ _ _ _ b
  | DUP _ _ => DUP
  | SWAP _ _ _ => SWAP
  | UNIT _ => UNIT
  | EQ _ => EQ
  | NEQ _ => NEQ
  | LT _ => LT
  | GT _ => GT
  | LE _ => LE
  | GE _ => GE
  | OR _ s _ => @OR _ _ s _
  | AND _ _ s _ => @AND _ _ _ s _
  | XOR _ s _ => @XOR _ _ s _
  | NOT _ s _ => @NOT _ _ s _
  | NEG _ s _ => @NEG _ _ s _
  | ABS _ => ABS
  | ISNAT _ => ISNAT
  | INT _ => INT
  | ADD _ _ _ _ => ADD
  | SUB _ _ _ _ => SUB
  | MUL _ _ _ _ => MUL
  | EDIV _ _ _ _ => EDIV
  | LSL _ => LSL
  | LSR _ => LSR
  | COMPARE _ _ => COMPARE
  | CONCAT _ i _ => @CONCAT _ _ i _
  | CONCAT_list _ i _ => @CONCAT_list _ _ i _
  | SIZE _ i _ => @SIZE _ _ i _
  | SLICE _ i _ => @SLICE _ _ i _
  | PAIR _ _ _ => PAIR
  | CAR _ _ _ => CAR
  | CDR _ _ _ => CDR
  | EMPTY_SET elt _ => EMPTY_SET elt
  | MEM _ _ i _ => @MEM _ _ _ i _
  | UPDATE _ _ _ i _ => @UPDATE _ _ _ _ i _
  | EMPTY_MAP x y _ => EMPTY_MAP x y
  | EMPTY_BIG_MAP x y _ => EMPTY_BIG_MAP x y
  | GET _ i _ _ => @GET _ _ i _ _
  | SOME _ _ => SOME
  | NONE a _ => NONE a
  | LEFT _ b _ => LEFT b
  | RIGHT a _ _ => RIGHT a
  | CONS _ _ => CONS
  | NIL a _ => NIL a
  | TRANSFER_TOKENS _ _ => TRANSFER_TOKENS
  | SET_DELEGATE _ => SET_DELEGATE
  | BALANCE _ => BALANCE
  | ADDRESS _ _ => ADDRESS
  | CONTRACT _ annot_opt p => CONTRACT annot_opt p
  | SOURCE _ => SOURCE
  | SENDER _ => SENDER
  | AMOUNT _ => AMOUNT
  | IMPLICIT_ACCOUNT _ => IMPLICIT_ACCOUNT
  | NOW _ => NOW
  | PACK _ _ => PACK
  | UNPACK a _ => UNPACK a
  | HASH_KEY _ => HASH_KEY
  | BLAKE2B _ => BLAKE2B
  | SHA256 _ => SHA256
  | SHA512 _ => SHA512
  | CHECK_SIGNATURE _ => CHECK_SIGNATURE
  | DIG n _ _ _ Sn => DIG n Sn
  | DUG n _ _ _ Sn => DUG n Sn
  | DROP n _ _ An => DROP n An
  | CHAIN_ID _ => CHAIN_ID
  end.

Fixpoint reconstr {self_type a b tff} (ins: instruction_seq self_type tff a b) :
  Datatypes.option (instruction_seq None tff a b) :=
  match ins with
  | NOOP _ _ => Some NOOP
  | Tail_fail _ _ _ x => omap Tail_fail (reconstr1 x)
  | SEQ _ _ _ _ _ x y =>
    obind (fun a => omap a (reconstr y)) (omap SEQ (reconstr1 x))
  end
with reconstr1 {self_type a b tff} (ins: instruction self_type tff a b) :
  Datatypes.option (instruction None tff a b) :=
  match ins with
  | Instruction_seq _ _ _ _ x =>
    omap Instruction_seq (reconstr x)
  | FAILWITH _ _ _ _ => Some FAILWITH
  | IF_ _ _ _ _ _ _ _ _ i x y =>
    obind (fun a => omap a (reconstr y)) (omap (IF_ i) (reconstr x))
  | LOOP_ _ _ _ _ _ _ i x => omap (LOOP_ i) (reconstr x)
  | PUSH t x _ _ => Some (PUSH t x)
  | LAMBDA x y _ _ _ z => omap (LAMBDA x y) (reconstr z)
  | ITER _ _ _ _ _ x => omap ITER (reconstr x)
  | MAP _ _ _ _ _ x => omap MAP (reconstr x)
  | CREATE_CONTRACT _ _ _ g p an x => Some (CREATE_CONTRACT g p an x)
  | SELF _ _ _ annot_opt H => None
  | EXEC _ _ _ _ => Some EXEC
  | DIP n _ _ _ _ An x => omap (DIP n An) (reconstr x)
  | Instruction_opcode _ _ _ op => Some (Instruction_opcode (reconstr_op op))
  end.

Open Scope michelson_scope.

Definition genprog {parameter_ty storage_ty}
           (prog: full_contract false parameter_ty None storage_ty)
           (validation_snippet: instruction_seq None false
                                                (pair bytes mutez ::: [::])
                                                (pair bytes mutez ::: [::]))
  : Datatypes.option (instruction_seq None false (pair bytes mutez ::: [::])
    (list (pair (pair syntax_type.string (lambda (pair bytes bytes)
    (pair (list operation) bytes))) (pair bytes mutez)) ::: [::])) :=
  match reconstr prog with
  | Some prog0 =>
    Some (validation_snippet;;;
         {DIP1 {NIL _};
         LAMBDA _ _
                {
                  UNPAIR; UNPACK parameter_ty;
                  IF_NONE {PUSH _ (Comparable_constant syntax_type.string "unpack param"); FAILWITH}
                          {
                            SWAP; UNPACK storage_ty;
                            IF_NONE {PUSH _ (Comparable_constant syntax_type.string "unpack storage"); FAILWITH}
                                    (SWAP;; PAIR;; prog0;;;
                                     {UNPAIR; DIP1 {PACK}; PAIR})
                          }
                };
         PUSH _ (Comparable_constant syntax_type.string "main"); PAIR; PAIR; CONS})
  | None => None
  end.

Definition initprog :
  instruction_seq None false (pair bytes mutez ::: [::])
    (lambda (map syntax_type.string address)
       (list (pair syntax_type.string bytes)) ::: [::]) :=
  {DROP1; LAMBDA _ _ {DROP1; NIL (pair _ bytes)}}.
End ccgen.

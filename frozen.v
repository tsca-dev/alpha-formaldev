From mathcomp Require Import all_ssreflect.
From Michocoq Require Import semantics util macros.
Import syntax comparable error.
Require Import ccgen_util.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module frozen(C : ContractContext).
Module semantics := Semantics C. Import semantics.
Require Import String.
Open Scope string_scope.

Definition zero :=
  Comparable_constant syntax_type.mutez (extract (tez.of_Z BinNums.Z0) I).

Definition parameter_ty := pair (mutez (* amount *)) (address (* beneficiary *)).
Definition storage_ty :=
  pair (set address (* fund_owners *)) (timestamp (* unfrozen *)).

Definition validate_invocation {self_type S} :
  instruction_seq self_type false (pair parameter_ty storage_ty ::: S) S :=
  {
    AMOUNT; PUSH mutez zero; COMPARE; NEQ;
    IF_TRUE {FAILWITH} { };
    UNPAIR; DIP1 {UNPAIR}; SWAP; SOURCE; @MEM _ _ _ (mem_set _) _;
    IF_TRUE { } {FAILWITH};
    (* source of operation is not whitelisted for withdrawal operations *)
    SWAP; NOW; COMPARE; LT;
    IF_TRUE {FAILWITH} { };
    (* deposit still frozen *)
    UNPAIR; DUP;
    BALANCE; COMPARE; LT;
    IF_TRUE {FAILWITH} { };
    (* requested withdrawal amount exceeds the balance *)
    PUSH mutez zero; COMPARE; EQ;
    IF_TRUE {FAILWITH} { };
    (* frozen contract cannot accept positive amount transfer *)
    DROP1
  }.

Definition perform_withdraw {self_type S} :
  instruction_seq self_type false (parameter_ty ::: S) (operation ::: S) :=
  {
    UNPAIR; SWAP; CONTRACT (Some "") unit;
    IF_NONE {FAILWITH} {SWAP; PUSH unit Unit; TRANSFER_TOKENS}
  }.

Definition frozen : full_contract false parameter_ty None storage_ty :=
  DUP;; validate_invocation;;;
  UNPAIR;; perform_withdraw;;;
  {DIP1 {NIL operation}; CONS; PAIR}.

Local Lemma lem x :
  ~~ int64bv.sign x ->
  match int64bv.to_Z x with
  | BinNums.Z0 => true
  | BinNums.Zpos _ => true
  | BinNums.Zneg _ => false
  end.
Proof.
  move: x.
  rewrite /int64bv.sign /int64bv.to_Z /Bvector.Bsign
          /int64bv.int64 /Bvector.Bvector => x.
  apply: (@Vector.rectS _ (fun n x => forall x : Vector.t Datatypes.bool n.+1,
                           ~~ Vector.last x -> _) _ _ 63 x).
  + move=> _ x0 H.
    suff->: x0 = Vector.cons Datatypes.bool false 0 (Vector.nil Datatypes.bool)
      by [].
    apply: (@Vector.caseS' _ 0 x0
                           (fun x => ~~ Vector.last x -> x = Vector.cons
                                                           _ false
                                                           _ (Vector.nil _))
                           _ H).
    move=> h; apply: Vector.case0; by case: h.
  + move=> _ {x} n _ IH x.
    apply: (@Vector.caseS _ (fun n' (x0 : Vector.t Datatypes.bool n'.+1) =>
                               n' = n.+1 -> ~~ Vector.last x0 -> _) _ n.+1 x)
            => // {x} h n0 x C.
    move: C x => -> x.
    rewrite Zdigits.two_compl_value_Sn /= => /IH.
    case: (Zdigits.two_compl_value n x); by case: h.
Qed.

Lemma tez0 m :
  tez.compare (extract (tez.of_Z BinNums.Z0) I) m = Lt
\/ tez.compare (extract (tez.of_Z BinNums.Z0) I) m = Eq.
Proof.
  case: m => x.
  rewrite /tez.compare /int64bv.int64_compare /int64bv.compare /=.
  case H: (int64bv.sign x) => // _.
  move/negP/negP/lem: H.
  by case :(int64bv.to_Z x); auto.
Qed.

Lemma frozen_correct
      (env : @proto_env (Some (parameter_ty, None)))
      (fuel : Datatypes.nat)
      (m : tez.mutez)
      (addr : data address)
      (unfrozen : data timestamp)
      (fund_owners : data (set address))
      (psi : stack (pair (list operation) storage_ty ::: [::]) -> Prop) :
fuel > 5 ->
precond (eval_seq env frozen fuel ((m, addr), (fund_owners, unfrozen), tt)) psi
<-> match contract_ (Some "") unit addr with
  | Some c =>
    psi ([:: transfer_tokens env unit tt m c], (fund_owners, unfrozen), tt)
    /\ tez.compare (extract (tez.of_Z BinNums.Z0) I) (amount env) = Eq
    /\ set.mem address_constant address_compare (source env) fund_owners
    /\ (BinInt.Z.compare (now env) unfrozen = Gt
       \/ BinInt.Z.compare (now env) unfrozen = Eq)
    /\ (tez.compare (balance env) m = Gt
       \/ tez.compare (balance env) m = Eq)
    /\ tez.compare (extract (tez.of_Z BinNums.Z0) I) m = Lt
  | None => false
  end.
Proof.
  move=> F; have<-: 6 + (fuel - 6) = fuel by rewrite addnC subnK.
  split => H.
  + case C : (contract_ (Some "") unit addr).
    - move: H;
      rewrite eval_seq_precond_correct /eval_seq_precond /= C /=.
      case => + []+ []+ []+ []+ []+ [][->].
      set C1 := (tez.compare _ _); case: C1 => // _ ->.
       set C2 := (tez.compare _ _); case: C2 => //.
        set C4 := (tez.compare _ _); case H4: C4 => //.
         set C3 := (BinInt.Z.compare _ _); case: C3 => //= *;
          repeat split => //; auto.
        subst C4; move: H4 (tez0 m) => ->; by case.
        set C4 := (tez.compare _ _); case H4: C4 => //.
         set C3 := (BinInt.Z.compare _ _); case: C3 => //= *;
          repeat split => //; auto.
        subst C4; move: H4 (tez0 m) => ->; by case.
    - move: H; rewrite eval_seq_precond_correct /eval_seq_precond /= C /=.
      by repeat case => ?.
  + rewrite eval_seq_precond_correct /eval_seq_precond /=.
    move: H; case: (contract_ (Some "") unit addr) => // a.
    case => []H1 []-> []-> [][]-> [][]-> ->;
    repeat split; by exists a.
Qed.

Lemma frozen_preserve_storage
      (env : @proto_env (Some (parameter_ty, None)))
      (fuel : Datatypes.nat)
      (m : tez.mutez)
      (addr : data address)
      (unfrozen : data timestamp)
      (fund_owners : data (set address))
      returned_operations new_storage :
  fuel > 5 ->
  eval_seq env frozen fuel ((m, addr), (fund_owners, unfrozen), tt)
= Return (returned_operations, new_storage, tt) ->
  new_storage = (fund_owners, unfrozen).
Proof.
  move=> f5; rewrite return_precond frozen_correct //=.
  by case: (contract_ (Some "") unit addr) => // ? [][] + ->.
Qed.

Definition frozen_genprog_validation_snippet :=
  @make_typed_validation_snippet (pair (set address) timestamp) { DROP1; DROP1 }.
End frozen.

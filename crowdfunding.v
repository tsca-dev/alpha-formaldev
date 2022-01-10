From mathcomp Require Import all_ssreflect.
From Michocoq Require Import semantics util macros.
Import syntax comparable error.
Require Import ccgen_util.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module crowdfunding(C : ContractContext).
Module semantics := Semantics C. Import semantics.
Require Import String.
Open Scope string_scope.
Open Scope michelson_scope.

Definition parameter_ty :=
  or key_hash None
     (or address None address None) None.

Definition storage_ty :=
  (pair
     (pair (set (* %raisers *) address) (map (* %refund_table *) address mutez))
     (pair (pair (bool (* %withdrawn *)) (timestamp (* %funding_start *)))
           (pair (timestamp (* %funding_end *)) (timestamp (* %unconditional_refund_start *))))).

Definition funding_start {self_type S} :
  instruction_seq self_type false
                  (storage_ty ::: S)
                  (timestamp ::: storage_ty ::: S) :=
  {DUP; UNPAIR; DROP1; UNPAIR; UNPAIR; DROP1; DIP1 {DROP1}}.

Definition funding_end {self_type S} :
  instruction_seq self_type false
                  (storage_ty ::: S)
                  (timestamp ::: storage_ty ::: S) :=
  {DUP; UNPAIR; DROP1; UNPAIR; DROP1; UNPAIR; DIP1 {DROP1}}.

Definition refund_table {self_type S} :
  instruction_seq self_type false
                  (storage_ty ::: S)
                  (map address mutez::: storage_ty ::: S) :=
  {DUP; UNPAIR; DIP1 {DROP1}; UNPAIR; DROP1}.

Definition update_refund_table {self_type S} :
  instruction_seq self_type false
                  (map address mutez::: storage_ty ::: S)
                  (storage_ty ::: S) :=
  {SWAP; UNPAIR; UNPAIR; DIP1 {DROP1; SWAP}; PAIR; PAIR}.

Definition validate_contribute {self_type S} :
  instruction_seq self_type false
                  (storage_ty ::: S)
                  (storage_ty ::: S) :=
  funding_start;;; {NOW; COMPARE; GE;
  DIP1 funding_end; DIP1 {NOW; SWAP; COMPARE; GE}; AND; NOT;
  IF_TRUE {FAILWITH} { }}.

Definition unconditional_refund_start {self_type S} :
  instruction_seq self_type false
                  (storage_ty ::: S)
                  (timestamp ::: storage_ty ::: S) :=
  {DUP; UNPAIR; DROP1; UNPAIR; DROP1; UNPAIR; DROP1}.

Definition raisers {self_type S} :
  instruction_seq self_type false
                  (storage_ty ::: S)
                  (set address::: storage_ty ::: S) :=
  {DUP; UNPAIR; DIP1 {DROP1}; UNPAIR; DIP1 {DROP1}}.

Definition withdrawn {self_type S} :
  instruction_seq self_type false
                  (storage_ty ::: S)
                  (bool ::: storage_ty ::: S) :=
  {DUP; UNPAIR; DROP1; UNPAIR; DIP1 {DROP1}; UNPAIR; DIP1 {DROP1}}.

Definition set_withdrawn {self_type S} :
  instruction_seq self_type false
                  (storage_ty ::: S)
                  (storage_ty ::: S) :=
  {UNPAIR; DIP1 {UNPAIR; UNPAIR; DROP1; PUSH bool True; PAIR; PAIR}; PAIR}.

Definition validate_withdraw {self_type S} :
  instruction_seq self_type false
                  (storage_ty ::: S)
                  (storage_ty ::: S) :=
 funding_start;;; NOW;; SWAP;; COMPARE;; GE;;
 {DIP1 funding_end; DIP1 {NOW; COMPARE; GE}; AND; NOT};;;
 DIP1 {NOW; DIP1 unconditional_refund_start; SWAP; COMPARE; LE};;
 @OR _ _ bitwise_bool _;; IF_TRUE {FAILWITH} { };;
 withdrawn;;; IF_TRUE {FAILWITH} { };;
 raisers;;; {SOURCE; @MEM _ _ _ (mem_set address) _;
             NOT; IF_TRUE {FAILWITH} { }}.

Definition create_transfer {self_type S} :
  instruction_seq self_type false
                  (mutez ::: address ::: storage_ty ::: S)
                  (operation ::: storage_ty ::: S) :=
  {DIP1 {CONTRACT None unit}; SWAP;
   IF_NONE {FAILWITH}
           {SWAP; UNIT; TRANSFER_TOKENS}}.

Definition validate_refund {self_type S} :
  instruction_seq self_type false
                  (storage_ty ::: S)
                  (storage_ty ::: S) :=
{NOW; DIP1 unconditional_refund_start; SWAP; COMPARE; GT};;;
 IF_TRUE {FAILWITH} { };; withdrawn;;; {IF_TRUE {FAILWITH} { }}.

Definition crowdfunding : full_contract false parameter_ty None storage_ty :=
  {DUP; CAR; DIP1 {CDR};
  IF_LEFT
  (IMPLICIT_ACCOUNT;;
   ADDRESS;;
   DUP;;
   DIIP refund_table;;
   DIP1 {@GET _ _ _ (get_map address mutez) _};;
   DIP1 {IF_SOME {AMOUNT; @ADD _ _ _ add_tez_tez _} {AMOUNT}};;
   DIP1 {SOME};;
   DIIP refund_table;;
   @UPDATE _ _ _ _ (update_map address mutez) _;;
   DIP1 validate_contribute;; update_refund_table;;; {NIL operation; PAIR})
 {IF_LEFT
  (DIP1 validate_withdraw;;
  BALANCE;;
  create_transfer;;;
  {NIL operation; SWAP; CONS; DIP1 set_withdrawn; PAIR})
  {DIP1 refund_table; DUP; DIP1 {@GET _ _ _ (get_map address mutez) _}; SWAP;
   IF_NONE {FAILWITH}
     (SWAP;;
      DIP1 {SWAP};;
      NONE mutez;;
      DIIP refund_table;;
      SWAP;;
      DUP;;
      DIP1 {@UPDATE _ _ _ _ (update_map address mutez) _};;
      DIIP validate_refund;;
      DIP1 update_refund_table;;
      DIP1 {SWAP};;
      SWAP;;
      create_transfer;;;
      {NIL operation; SWAP; CONS; PAIR})}}}.

Local Definition geq a b :=
  match BinInt.Z.compare a b with
  | Gt | Eq => true
  | _ => false
  end.

Local Definition gt a b :=
  match BinInt.Z.compare a b with
  | Gt => true
  | _ => false
  end.

Import Notations.

Lemma crowdfunding_correct_contribute
      (env : @proto_env (Some (parameter_ty, None)))
      (fuel : Datatypes.nat)
      (refund_address : data key_hash)
      (raisers : data (set address))
      (refund_table : data (map address mutez))
      (funding_start : data timestamp)
      (funding_end : data timestamp)
      (unconditional_refund_start : data timestamp)
      (withdrawn : data bool)
      (psi : stack (pair (list operation) storage_ty ::: [::]) -> Prop) :
let refund_amount x := map.get _ _ _
                             (address_ _ (implicit_account x)) in
let insert := map.insert address_constant tez.mutez address_compare
                     (compare_eq_iff address) (gt_trans address)
                     (Implicit refund_address) in
fuel > 5 ->
precond (eval_seq env crowdfunding fuel
         (inl refund_address,
          ((raisers, refund_table),
           ((withdrawn, funding_start),
            (funding_end, unconditional_refund_start))), tt)) psi <->
let changed_refund_table :=
match refund_amount refund_address refund_table with
| Some x =>
  let! z := tez.of_Z (BinInt.Z.add (tez.to_Z (amount env)) (tez.to_Z x)) in
  Return (insert z refund_table)
| None =>
  Return (insert (amount env) refund_table)
end in
precond changed_refund_table (fun t =>
geq (now env) funding_start /\ geq funding_end (now env)
/\ psi ([::],
     ((raisers, t),
      ((withdrawn, funding_start),
       (funding_end, unconditional_refund_start))), tt)).
Proof.
  move=> ra ins F; have<-: 6 + (fuel - 6) = fuel by rewrite addnC subnK.
  rewrite /geq; subst ra ins; split.
  + rewrite eval_seq_precond_correct /eval_seq_precond /=.
    set H := map.get _ _ _ _ _.
    case: H => [a|].
    - set T := tez.of_Z _.
      case: T => //= T [] /negP/negP /andP[].
      case: (BinInt.Z.compare (now env) funding_start) => //;
      case: (BinInt.Z.compare funding_end (now env)) => //; auto.
    - case=> [] /negP/negP /andP[] /=.
      case: (BinInt.Z.compare (now env) funding_start) => //;
      case: (BinInt.Z.compare funding_end (now env)) => //; auto.
  + rewrite eval_seq_precond_correct /eval_seq_precond /=.
    set H := map.get _ _ _ _ _.
    case: H => [a|/=].
    - set T := tez.of_Z _.
      case: T => //= T [] + [].
      case: (BinInt.Z.compare (now env) funding_start) => //;
      case: (BinInt.Z.compare funding_end (now env)) => //; auto;
      (try by case);
      (try by move=> + []).
    - case => + [].
      case: (BinInt.Z.compare (now env) funding_start) => //;
      case: (BinInt.Z.compare funding_end (now env)) => //; auto;
      (try by case);
      (try by move=> + []).
Qed.

Lemma crowdfunding_fail_contribute
      (env : @proto_env (Some (parameter_ty, None)))
      (fuel : Datatypes.nat)
      (refund_address : data key_hash)
      (raisers : data (set address))
      (refund_table : data (big_map address mutez))
      (funding_start : data timestamp)
      (funding_end : data timestamp)
      (unconditional_refund_start : data timestamp)
      (withdrawn : data bool) :
fuel <= 5 ->
~~ success (eval_seq env crowdfunding fuel
         (inl refund_address,
          ((raisers, refund_table),
           ((withdrawn, funding_start),
            (funding_end, unconditional_refund_start))), tt)).
Proof.
  case: fuel => //.
  repeat case => //.
  rewrite /eval_seq /=.
  case: (map.get _ _ _ _ ) => // a.
  case: (tez.of_Z _) => //.
Qed.

Lemma crowdfunding_correct_withdraw
      (env : @proto_env (Some (parameter_ty, None)))
      (fuel : Datatypes.nat)
      (beneficiary : data address)
      (raisers : data (set address))
      (refund_table : data (big_map address mutez))
      (funding_start : data timestamp)
      (funding_end : data timestamp)
      (unconditional_refund_start : data timestamp)
      (withdrawn : data bool)
      (psi : stack (pair (list operation) storage_ty ::: [::]) -> Prop) :
fuel > 7 ->
precond (eval_seq env crowdfunding fuel
         (inr (inl beneficiary),
          ((raisers, refund_table),
           ((withdrawn, funding_start),
            (funding_end, unconditional_refund_start))), tt)) psi <->
geq funding_start (now env) /\ geq (now env) funding_end
/\ gt unconditional_refund_start (now env)
/\ withdrawn = false
/\ set.mem address_constant address_compare (source env) raisers
/\ exists y, contract_ None unit beneficiary = Some y
   /\ psi ([:: transfer_tokens env unit tt (balance env) y],
          (raisers, refund_table,
          (true, funding_start, (funding_end, unconditional_refund_start))), tt).
Proof.
  move=> F; have<-: 8 + (fuel - 8) = fuel by rewrite addnC subnK.
  rewrite eval_seq_precond_correct /eval_seq_precond /=.
  rewrite /gt /geq; split.
  + case => + [] + [].
    case: (BinInt.Z.compare funding_start (now env)) => //;
    case: (BinInt.Z.compare (now env) funding_end) => //;
    by (rewrite /= BinInt.Z.compare_antisym;
    case: (BinInt.Z.compare (now env) unconditional_refund_start) => // + + a *;
    repeat split => //; auto; by move/negP/negP: a).
  + case=> + [] + [] + [] + [].
    case: (BinInt.Z.compare funding_start (now env)) => // _;
    case: (BinInt.Z.compare (now env) funding_end) => // _;
    case: (BinInt.Z.compare unconditional_refund_start (now env)) => // _ *;
    repeat split => //; auto; by apply/negP/negP.
Qed.

Lemma crowdfunding_fail_withdraw
      (env : @proto_env (Some (parameter_ty, None)))
      (fuel : Datatypes.nat)
      (beneficiary : data address)
      (raisers : data (set address))
      (refund_table : data (big_map address mutez))
      (funding_start : data timestamp)
      (funding_end : data timestamp)
      (unconditional_refund_start : data timestamp)
      (withdrawn : data bool) :
fuel <= 7 ->
~~ success (eval_seq env crowdfunding fuel
         (inr (inl beneficiary),
          ((raisers, refund_table),
           ((withdrawn, funding_start),
            (funding_end, unconditional_refund_start))), tt)).
Proof.
  case: fuel => //.
  repeat case => //.
Qed.

Lemma crowdfunding_correct_refund
      (env : @proto_env (Some (parameter_ty, None)))
      (fuel : Datatypes.nat)
      (eligible_address : data address)
      (raisers : data (set address))
      (refund_table : data (big_map address mutez))
      (funding_start : data timestamp)
      (funding_end : data timestamp)
      (unconditional_refund_start : data timestamp)
      (withdrawn : data bool)
      (psi : stack (pair (list operation) storage_ty ::: [::]) -> Prop) :
let remove := map.remove address_constant tez.mutez address_compare
              (compare_eq_iff address) (lt_trans address) (gt_trans address) in
let get := map.get address_constant tez.mutez address_compare in
fuel > 7 ->
precond (eval_seq env crowdfunding fuel
         (inr (inr eligible_address),
          ((raisers, refund_table),
           ((withdrawn, funding_start),
            (funding_end, unconditional_refund_start))), tt)) psi <->
exists y, get eligible_address refund_table = Some y
/\ geq (now env) unconditional_refund_start
/\ withdrawn = false
/\ (exists y0, contract_ None unit eligible_address = Some y0
   /\ psi ([:: transfer_tokens env unit tt y y0],
           (raisers, remove eligible_address refund_table,
           (withdrawn, funding_start, (funding_end, unconditional_refund_start))), tt)).
Proof.
  move=> rm get F; have<-: 8 + (fuel - 8) = fuel by rewrite addnC subnK.
  rewrite eval_seq_precond_correct /eval_seq_precond /=.
  subst rm get; rewrite /gt /geq; split.
  + case=> y [] H1 [] H2 [] H3 H4; exists y.
    repeat split; auto.
    rewrite /= BinInt.Z.compare_antisym.
    by case: H2; case: (BinInt.Z.compare unconditional_refund_start (now env)); auto.
  + case=> y [] H1 [] H2 [] H3 H4; exists y.
    repeat split; auto.
    rewrite /= BinInt.Z.compare_antisym.
    by case: H2; case: (BinInt.Z.compare (now env) unconditional_refund_start); auto.
Qed.

Lemma crowdfunding_fail_refund
      (env : @proto_env (Some (parameter_ty, None)))
      (fuel : Datatypes.nat)
      (eligible_address : data address)
      (raisers : data (set address))
      (refund_table : data (big_map address mutez))
      (funding_start : data timestamp)
      (funding_end : data timestamp)
      (unconditional_refund_start : data timestamp)
      (withdrawn : data bool) :
fuel <= 7 ->
~~ success (eval_seq env crowdfunding fuel
         (inr (inr eligible_address),
          ((raisers, refund_table),
           ((withdrawn, funding_start),
            (funding_end, unconditional_refund_start))), tt)).
Proof.
  case: fuel => //.
  repeat case => //;
  rewrite /eval_seq /=;
  case: (map.get _ _ _ _ ) => //.
Qed.

(* 90 days = (60*60*24*90) seconds *)
Definition funding_start_latest :=
  Comparable_constant _ (BinInt.Z_of_nat [Num of 7776000]
                         : simple_comparable_data int).

(* 270 days = (60*60*24*270) seconds *)
Definition funding_period_longest :=
  Comparable_constant _ (BinInt.Z_of_nat [Num of 23328000]
                         : simple_comparable_data int).

(* 90 days = (60*60*24*90) seconds *)
Definition redeem_period_longest :=
  Comparable_constant _ (BinInt.Z_of_nat [Num of 7776000]
                         : simple_comparable_data int).

Local Notation SUB := (@SUB _ _ _ sub_timestamp_timestamp _).
Local Notation OR := (@OR _ _ bitwise_bool _).

Definition validation_snippet :
    instruction_seq None false (storage_ty ::: mutez ::: [::]) [::] :=
 DIP1 {DROP1};;
 raisers;;;
 @SIZE _ _ (size_set _) _;;
 PUSH _ (Comparable_constant _ (BinNums.N0 : simple_comparable_data nat));;
 COMPARE;;
 EQ;;
 IF_TRUE {PUSH _ (Comparable_constant syntax_type.string "there must be at least one registered raiser"); FAILWITH} { };;
 funding_start;;;
 DIP1 {NOW};;
 COMPARE;;
 LT;;
 DIP1 funding_end;;
 DIIP funding_start;;
 DIP1 {COMPARE; LT};;
 OR;;
 DIP1 unconditional_refund_start;;
 DIIP funding_end;;
 DIP1 {COMPARE; LT};;
 OR;;
 IF_TRUE {PUSH syntax_type.string (Comparable_constant syntax_type.string "timestamp parameters given in wrong order"); FAILWITH} { };;
 funding_start;;;
 NOW;;
 SWAP;;
 SUB;;
 PUSH int funding_start_latest;;
 SWAP;;
 COMPARE;;
 GT;;
 IF_TRUE {PUSH syntax_type.string (Comparable_constant syntax_type.string "funding_start too late"); FAILWITH} { };;
 funding_end;;;
 DIP1 funding_start;;
 SUB;;
 PUSH int funding_period_longest;;
 SWAP;;
 COMPARE;;
 GT;;
 IF_TRUE {PUSH syntax_type.string (Comparable_constant syntax_type.string "funding period too long"); FAILWITH} { };;
 unconditional_refund_start;;;
 {DIP1 funding_end; SUB; PUSH int redeem_period_longest; SWAP; COMPARE; GT;
  IF_TRUE {PUSH _ (Comparable_constant syntax_type.string "redeem period too long"); FAILWITH} { }; DROP1}.

Definition crowdfunding_genprog_validation_snippet :=
  make_typed_validation_snippet validation_snippet.

Hypothesis new_env :
  forall {N : self_info},
    @proto_env N -> data (list operation) -> @proto_env N.

Hypothesis now_geq :
  forall N env ops,
    geq (now (@new_env N env ops)) (now env).

Section Composition.
Definition comp {tffB T U}
           (N : self_info)
           (env : @proto_env N)
           (A : stack (pair (list operation) U ::: [::]))
           (paramB : data T)
           fuelB
           (B : instruction_seq N tffB (pair T U :: [::])
                                (pair (list operation) U :: [::])) :=
  let '(opsA, storage, tt) := A in
  match eval_seq env B fuelB (paramB, storage, tt) with
  | Return (opsB, storage, tt) =>
    (new_env env opsB, (cat opsA opsB, storage, tt))
  | Failed _ =>
    (env, (opsA, storage, tt))
  end.

Definition compN {tff T U N}
           (I : instruction_seq N tff (pair T U :: [::])
                                (pair (list operation) U :: [::]))
           xs env storage :=
  foldr (fun b a => comp a.1 a.2 b.1 b.2 I) (env, ([::], storage, tt)) xs.
End Composition.

Inductive operation' :=
| TransferTokens : forall
    (env : @proto_env (Some (parameter_ty, None)))
    (m : tez.mutez)
    (d : data (contract unit))
    (da : data address), operation'.

Definition eval_seq_another
      (env : @proto_env (Some (parameter_ty, None)))
      (fuel : Datatypes.nat)
      (A : stack (pair parameter_ty storage_ty ::: [::])) :=
  let refund_amount x := map.get _ _ _
                             (address_ _ (implicit_account x)) in
  let remove := map.remove address_constant tez.mutez address_compare
              (compare_eq_iff address) (lt_trans address) (gt_trans address) in
  let get := map.get address_constant tez.mutez address_compare in
  let '((raisers, refund_table),
           ((withdrawn, funding_start),
            (funding_end, unconditional_refund_start))) := A.1.2 in
  match A.1.1 with
  | inr (inr eligible_address) =>
    match get eligible_address refund_table with
    | Some y =>
      match contract_ None unit eligible_address with
      | Some y0 =>
        if (7 < fuel) && geq (now env) unconditional_refund_start && (withdrawn == false)
        then Return ([:: TransferTokens env y y0 eligible_address],
                (raisers, remove eligible_address refund_table,
                 (withdrawn, funding_start, (funding_end, unconditional_refund_start))), tt)
        else Failed _ Overflow
      | None => Failed _ Overflow
      end
    | None => Failed _ Overflow
    end
  | inr (inl beneficiary) =>
    match contract_ None unit beneficiary with
    | None => Failed _ Overflow
    | Some y =>
      if (7 < fuel) && geq funding_start (now env) && geq (now env) funding_end
         && gt unconditional_refund_start (now env)
         && (set.mem address_constant address_compare (source env) raisers)
         && (withdrawn == false)
      then Return ([:: TransferTokens env (balance env) y beneficiary],
          (raisers, refund_table,
          (true, funding_start, (funding_end, unconditional_refund_start))), tt)
      else Failed _ Overflow
    end
  | inl refund_address =>
    let insert := map.insert address_constant tez.mutez address_compare
                     (compare_eq_iff address) (gt_trans address)
                     (Implicit refund_address) in
    let! t :=
        match refund_amount refund_address refund_table with
        | Some x =>
          let! z := tez.of_Z (BinInt.Z.add (tez.to_Z (amount env)) (tez.to_Z x)) in
          Return (insert z refund_table)
        | None =>
          Return (insert (amount env) refund_table)
        end in
    if (5 < fuel) && geq (now env) funding_start && geq funding_end (now env)
    then Return ([::],
            ((raisers, t),
             ((withdrawn, funding_start),
              (funding_end, unconditional_refund_start))), tt)
    else Failed _ Overflow
  end.

Local Definition conv (o : operation') :=
  match o with
  | TransferTokens env m d _ =>
    transfer_tokens env unit tt m d
  end.

Local Definition destination (o : operation') :=
  match o with
  | TransferTokens env m d da => da
  end.

Lemma eval_seq_eq env fuel A :
  success (eval_seq env crowdfunding fuel A) ->
  eval_seq env crowdfunding fuel A =
  let! (ops, storage, tt) := eval_seq_another env fuel A in
  Return (seq.map conv ops, storage, tt).
Proof.
  case: A => [][] op st [].
  case: st => [][] raisers refund_table [][] withdrawn funding_start
              [] funding_end unconditional_refund_start.
  case: op => [refund_address|[beneficiary|eligible_address]] s.
  + have f5 : 5 < fuel.
     rewrite ltnNge.
     apply/negP => /(crowdfunding_fail_contribute
     env refund_address raisers refund_table funding_start funding_end unconditional_refund_start withdrawn).
     by rewrite s.
    have: is_true (success (eval_seq env crowdfunding fuel (inl refund_address, (raisers, refund_table, (withdrawn, funding_start, (funding_end, unconditional_refund_start))), tt)))
     by rewrite s.
    rewrite success_precond crowdfunding_correct_contribute //= /eval_seq_another /=.
    set B := match _ with | Some _ => _ | None => _ end .
    case Beq : B => //= [][] Ha [] Hb _.
    rewrite Ha Hb f5 return_precond crowdfunding_correct_contribute //.
    subst B; rewrite Beq /=.
    by auto.
  + have f7 : 7 < fuel.
     rewrite ltnNge.
     apply/negP => /(crowdfunding_fail_withdraw
     env beneficiary raisers refund_table funding_start funding_end unconditional_refund_start withdrawn).
     by rewrite s.
    have: is_true (success (eval_seq env crowdfunding fuel (inr (inl beneficiary), (raisers, refund_table, (withdrawn, funding_start, (funding_end, unconditional_refund_start))), tt)))
     by rewrite s.
    rewrite success_precond crowdfunding_correct_withdraw //= /eval_seq_another /=.
    case=> []a1 []a2 []a3 []a4 []a5 []y [] Hy _.
    rewrite a1 a2 a3 a4 a5 f7 Hy return_precond crowdfunding_correct_withdraw //.
    repeat split => //.
    by exists y; auto.
  + have f7 : 7 < fuel.
     rewrite ltnNge.
     apply/negP => /(crowdfunding_fail_refund
     env eligible_address raisers refund_table funding_start funding_end unconditional_refund_start withdrawn).
     by rewrite s.
    have: is_true (success (eval_seq env crowdfunding fuel (inr (inr eligible_address), (raisers, refund_table, (withdrawn, funding_start, (funding_end, unconditional_refund_start))), tt)))
     by rewrite s.
    rewrite success_precond crowdfunding_correct_refund //= /eval_seq_another /=.
    case=> []y []Hy []a1 []a2 []y0 []Hy0 _.
    rewrite Hy Hy0 a1 a2 f7 return_precond crowdfunding_correct_refund //.
    exists y; repeat split => //.
    exists y0; by auto.
Qed.

Lemma eval_seq_fail env fuel A :
  ~~ success (eval_seq env crowdfunding fuel A) <->
  ~~ success (eval_seq_another env fuel A).
Proof.
  case: A => [][] op st [].
  case: st => [][] raisers refund_table [][] withdrawn funding_start
              [] funding_end unconditional_refund_start.
  case: op => [refund_address|[beneficiary|eligible_address]];
  split; apply/contra => s.
  + apply/Bool.Is_true_eq_true.
    rewrite -/Is_true -/is_true success_precond.
    have f5: 5 < fuel.
     rewrite ltnNge.
     apply/negP => f5.
     move: s.
     rewrite /eval_seq_another /= ltnNge f5 /=.
     by case: (match _ with | Some _ => _ | None => _ end).
    rewrite crowdfunding_correct_contribute //=.
    move: s.
    rewrite /eval_seq_another /=.
    set B := (match _ with | Some _ => _ | None => _ end).
    case Beq : B => //.
    rewrite f5 /=.
    case: (geq (now env) funding_start) => //.
    by case: (geq funding_end (now env)).
  + apply/Bool.Is_true_eq_true.
    rewrite -/Is_true -/is_true success_precond.
    have f5: 5 < fuel.
     rewrite ltnNge.
     apply/negP => /(crowdfunding_fail_contribute
     env refund_address raisers refund_table funding_start funding_end unconditional_refund_start withdrawn).
     by rewrite s.
    rewrite /eval_seq_another /= f5 /=.
    move/Bool.Is_true_eq_left: s.
    rewrite -/Is_true -/is_true success_precond crowdfunding_correct_contribute //=.
    set B := (match _ with | Some _ => _ | None => _ end).
    case Beq : B => //=.
    case: (geq (now env) funding_start) => [|[]//].
    by case: (geq funding_end (now env)) => [|[] _ []].
  + apply/Bool.Is_true_eq_true.
    rewrite -/Is_true -/is_true success_precond.
    have f7: 7 < fuel.
     rewrite ltnNge.
     apply/negP => f7.
     move: s.
     rewrite /eval_seq_another /= ltnNge f7 /=.
     by case: (contract_ None unit beneficiary).
    rewrite crowdfunding_correct_withdraw //=.
    move: s.
    rewrite /eval_seq_another /=.
    case Ceq: (contract_ _ _ _) => [a|//].
    rewrite f7 /=.
    case: (geq funding_start (now env)) => //.
    case: (geq (now env) funding_end) => //.
    case: (gt unconditional_refund_start (now env)) => //.
    case: (set.mem address_constant address_compare (source env) raisers) => //.
    case: withdrawn => //= _.
    repeat split => //.
    by exists a.
  + apply/Bool.Is_true_eq_true.
    rewrite -/Is_true -/is_true success_precond.
    have f7: 7 < fuel.
     rewrite ltnNge.
     apply/negP => /(crowdfunding_fail_withdraw
     env beneficiary raisers refund_table funding_start funding_end unconditional_refund_start withdrawn).
     by rewrite s.
    rewrite /eval_seq_another /= f7 /=.
    move/Bool.Is_true_eq_left: s.
    rewrite -/Is_true -/is_true success_precond crowdfunding_correct_withdraw //=.
    by case=> []-> []-> []-> []-> []-> []y []-> _ /=.
  + apply/Bool.Is_true_eq_true.
    rewrite -/Is_true -/is_true success_precond.
    have f7: 7 < fuel.
     rewrite ltnNge.
     apply/negP => f7.
     move: s.
     rewrite /eval_seq_another /= ltnNge f7 /=.
     case: (map.get  _ _ _ _ _) => //.
     by case: (contract_ _ _ _).
    rewrite crowdfunding_correct_refund //=.
    move: s.
    rewrite /eval_seq_another /= f7 /=.
    case Teq: (map.get  _ _ _ _ _) => [t|//].
    case Ceq: (contract_ _ _ _) => [a|//].
    case: (geq (now env) unconditional_refund_start) => //.
    case: withdrawn => //= _.
    exists t; repeat split => //.
    by exists a.
  + apply/Bool.Is_true_eq_true.
    rewrite -/Is_true -/is_true success_precond.
    have f7: 7 < fuel.
     rewrite ltnNge.
     apply/negP => /(crowdfunding_fail_refund
     env eligible_address raisers refund_table funding_start funding_end unconditional_refund_start withdrawn).
     by rewrite s.
    rewrite /eval_seq_another /= f7 /=.
    move/Bool.Is_true_eq_left: s.
    rewrite -/Is_true -/is_true success_precond crowdfunding_correct_refund //=.
    by case=> []x []-> []-> []-> []x0 []-> _.
Qed.

Definition comp_another
           (env : @proto_env (Some (parameter_ty, None)))
           (A : seq operation' * data storage_ty * Datatypes.unit)
           (paramB : data parameter_ty)
           fuelB :=
  match eval_seq_another env fuelB (paramB, A.1.2, tt) with
  | Return (opsB, storage, tt) =>
    (new_env env (seq.map conv opsB), (cat A.1.1 opsB, storage, tt))
  | Failed _ =>
    (env, (A.1.1, A.1.2, tt))
  end.

Definition compN_another xs env storage :=
  foldr (fun b a => comp_another a.1 a.2 b.1 b.2) (env, ([::], storage, tt)) xs.

Lemma comp_eq env ops st paramB fuelB :
  comp env (seq.map conv ops, st, tt) paramB fuelB crowdfunding
= let '(env, (ops, st, tt)) := comp_another env (ops, st, tt) paramB fuelB in
  (env, (seq.map conv ops, st, tt)).
Proof.
  rewrite /comp /comp_another.
  set A := eval_seq_another _ _ _.
  case Aeq : A => [|a].
   have/eval_seq_fail: ~~ success A by rewrite Aeq.
   by case: (eval_seq env crowdfunding fuelB (paramB, st, tt)).
  set C := eval_seq env crowdfunding fuelB (paramB, st, tt).
  have/eval_seq_eq: success C.
   apply/negP => /negP /eval_seq_fail.
   by subst A; rewrite Aeq.
  subst C => ->.
  subst A; rewrite Aeq.
  case: a Aeq => [][] opsA st0 [] /= ?.
  by rewrite map_cat.
Qed.

Lemma compN_eq env xs storage :
  compN crowdfunding xs env storage
= let '(env, (ops, st, tt)) := compN_another xs env storage in
  (env, (seq.map conv ops, st, tt)).
Proof.
  elim: xs env storage => // x xs IH env storage.
  rewrite /= !IH //=.
  case: (compN_another xs env storage) => [] env0 [][] ops st [].
  case s: (success (eval_seq env0 crowdfunding x.2 (x.1, st, tt))).
  + rewrite /= eval_seq_eq // /comp_another.
    case: (eval_seq_another env0 x.2 (x.1, st, tt)) s => [//|] [][]? ? [].
    by rewrite map_cat.
  + have: ~~ success (eval_seq_another env0 x.2 (x.1, st, tt))
     by rewrite -eval_seq_fail s.
    move: s => /=; rewrite /comp_another.
    case: (eval_seq env0 crowdfunding x.2 (x.1, st, tt)) => //.
    by case: (eval_seq_another env0 x.2 (x.1, st, tt)).
Qed.

Definition address_constant_eq a b :=
  match a, b with
  | Implicit (Mk_key_hash x), Implicit (Mk_key_hash y) => eqb x y
  | Originated (Mk_smart_contract_address x),
    Originated (Mk_smart_contract_address y) => eqb x y
  | _, _ => false
  end.

Lemma comparable_data_eqP :
  Equality.axiom (address_constant_eq).
Proof.
  case=> [][]x [][]y; apply/(iffP idP) => //= [];
  (try by move/eqb_spec => ->);
  by case=> ->; apply/eqb_spec.
Qed.

Canonical comparable_data_eqMixin := EqMixin comparable_data_eqP.
Canonical comparable_data_eqType :=
  Eval hnf in EqType _ comparable_data_eqMixin.

Definition operation_constant_eq a b :=
  match a, b with
  | Mk_operation x, Mk_operation y => eqb x y
  end.

Lemma operation_constant_eqP :
  Equality.axiom operation_constant_eq.
Proof.
  case=> []x []y; apply/(iffP idP) => /= [/eqb_spec -> //|[]->].
  by apply/eqb_spec.
Qed.

Canonical operation_constant_eqMixin := EqMixin operation_constant_eqP.
Canonical operation_constant_eqType :=
  Eval hnf in EqType (data operation) operation_constant_eqMixin.

Lemma size_crowdfunding_operations env x y z a b:
  eval_seq_another env x (y, z, tt) = Return (a, b, tt) ->
  seq.size a <= 1.
Proof.
  rewrite /eval_seq_another.
  case: y => [refund_address|[beneficiary|eligible_address]] /=.
  + case: z => [] [] ? ? [] [] ? ? [] ? ?.
    case: (match _ with | Some _ => _ | None => _ end) => //= ?.
    by case: ifP => // ? [] <-.
  + case: z => [] [] ? ? [] [] ? ? [] ? ?.
    case: (contract_ None unit beneficiary) => // ?.
    by case: ifP => // ? [] <-.
  + case: z => [] [] ? ? [] [] ? ? [] ? ?.
    case: (map.get address_constant tez.mutez address_compare eligible_address _) => // ?.
    case: (contract_ None unit _) => // ?.
    by case: ifP => // ? [] <-.
Qed.

Lemma gt_geq_trans' a b c :
  gt a b -> geq b c -> gt a c.
Proof.
move=> ab bc.
rewrite /gt.
case eq: (BinInt.Z.compare a c) => //.
+ move: eq.
  rewrite BinInt.Z.compare_eq_iff => bceq.
  rewrite {}bceq in ab, bc.
  move: ab bc.
  rewrite /gt /geq BinInt.Z.compare_antisym.
  by case: (BinInt.Z.compare b c).
+ move: ab bc.
  rewrite /gt /geq BinInt.Z.compare_antisym.
  case eqab: (BinInt.Z.compare b a) => //.
  rewrite BinInt.Z.compare_antisym.
  case eqac: (BinInt.Z.compare c b) => //.
  - move: eqac.
    rewrite BinInt.Z.compare_eq_iff => eqcb.
    rewrite eqcb in eq.
    move: eq eqab.
    rewrite BinInt.Z.compare_antisym.
    by case: (BinInt.Z.compare b a).
  - move: eq eqab eqac.
    rewrite !BinInt.Z.compare_lt_iff => bc ab.
    move: (BinInt.Z.lt_trans _ _ _ ab bc).
    rewrite -!BinInt.Z.compare_lt_iff BinInt.Z.compare_antisym.
    by case: (BinInt.Z.compare c b).
Qed.

Lemma geq_refl a : geq a a.
Proof.
  rewrite /geq.
  by rewrite BinInt.Z.compare_refl.
Qed.

Lemma pres_unconditional_refund_start xs env storage :
  storage.2.2.2 = (compN_another xs env storage).2.1.2.2.2.2.
Proof.
  elim: xs env storage => // x xs IH env storage.
  rewrite /= /comp_another /=.
  case eq: (eval_seq_another _ _ _) => [/=|[][] ops st []]; first by apply/IH.
  have->: st.2.2.2 = (compN_another xs env storage).2.1.2.2.2.2.
   case: x eq => [][|[]] x f.
   + rewrite /eval_seq_another /=.
     case eq : (compN_another xs env storage).2.1.2 =>
     [[]raisers refund_table
        [][]withdrawn funding_start []
        funding_end unconditional_refund_start].
     case: (map.get address_constant tez.mutez address_compare _ _) => /= [z|].
      case: (tez.of_Z _) => [//|a]/=.
      by case: ifP => // ? [] ? <-.
     by case: ifP => // ? [] ? [] <-.
   + rewrite /eval_seq_another /=.
     case eq : (compN_another xs env storage).2.1.2 =>
     [[]raisers refund_table
        [][]withdrawn funding_start []
        funding_end unconditional_refund_start].
    case: (contract_ None unit _) => // ?.
    by case: ifP => // ? [] ? <-.
   + rewrite /eval_seq_another /=.
     case eq : (compN_another xs env storage).2.1.2 =>
     [[]raisers refund_table
        [][]withdrawn funding_start []
        funding_end unconditional_refund_start].
     case: (map.get _ _ _ _ _) => // ?.
     case: (contract_ _ _ _) => // ?.
     by case: ifP => // ? [] ? <-.
  by apply/IH.
Qed.

Lemma pres_funding_end xs env storage :
  storage.2.2.1 = (compN_another xs env storage).2.1.2.2.2.1.
Proof.
  elim: xs env storage => // x xs IH env storage.
  rewrite /= /comp_another /=.
  case eq: (eval_seq_another _ _ _) => [/=|[][] ops st []]; first by apply/IH.
  have->: st.2.2.1 = (compN_another xs env storage).2.1.2.2.2.1.
   case: x eq => [][|[]] x f.
   + rewrite /eval_seq_another /=.
     case eq : (compN_another xs env storage).2.1.2 =>
     [[]raisers refund_table
        [][]withdrawn funding_start []
        funding_end unconditional_refund_start].
     case: (map.get address_constant tez.mutez address_compare _ _) => /= [z|].
      case: (tez.of_Z _) => [//|a]/=.
      by case: ifP => // ? [] ? <-.
     by case: ifP => // ? [] ? [] <-.
   + rewrite /eval_seq_another /=.
     case eq : (compN_another xs env storage).2.1.2 =>
     [[]raisers refund_table
        [][]withdrawn funding_start []
        funding_end unconditional_refund_start].
    case: (contract_ None unit _) => // ?.
    by case: ifP => // ? [] ? <-.
   + rewrite /eval_seq_another /=.
     case eq : (compN_another xs env storage).2.1.2 =>
     [[]raisers refund_table
        [][]withdrawn funding_start []
        funding_end unconditional_refund_start].
     case: (map.get _ _ _ _ _) => // ?.
     case: (contract_ _ _ _) => // ?.
     by case: ifP => // ? [] ? <-.
  by apply/IH.
Qed.

Lemma geq_gt a b :
geq a b -> ~~ gt b a.
Proof.
  rewrite /geq /gt /= BinInt.Z.compare_antisym.
  by case: (BinInt.Z.compare b a).
Qed.

Lemma geq_trans' : transitive geq.
Proof.
  move=> a b c.
  rewrite /geq /= BinInt.Z.compare_antisym.
  case ab: (BinInt.Z.compare a b) => //.
   move: ab.
   by rewrite BinInt.Z.compare_eq_iff => ->.
  rewrite BinInt.Z.compare_antisym.
  case ac: (BinInt.Z.compare c a) => //.
   move: ac.
   rewrite BinInt.Z.compare_eq_iff => ->.
   by rewrite BinInt.Z.compare_antisym ab.
  move: ab ac.
  rewrite !BinInt.Z.compare_lt_iff => ab bc.
  move: (BinInt.Z.lt_trans _ _ _ bc ab).
  by rewrite BinInt.Z.compare_antisym -BinInt.Z.compare_lt_iff => ->.
Qed.

Lemma compN_unconditional_refund_start xs env storage :
  gt storage.2.2.2 (now (compN_another xs env storage).1) ->
  (compN_another xs env storage).2.1.2.2.1.1 = false ->
  (compN_another xs env storage).2.1.1 = [::].
Proof.
  elim: xs env storage => // x xs IH env storage.
  rewrite /= /comp_another /=.
  case: x => [][refund_address|[beneficiary|eligible_address]] fuel;
  rewrite /eval_seq_another /=.
  + case eq : (compN_another xs env storage).2.1.2 =>
    [[]raisers refund_table
     [][]withdrawn funding_start []
     funding_end unconditional_refund_start].
    case: (map.get address_constant tez.mutez address_compare _ _) => /= [z|].
     case: (tez.of_Z _) => [e H1 H2|a]/=.
      apply/IH => //.
      by rewrite eq.
      case: ifP => ? /= H1 H2; last
       by apply/IH => //; rewrite eq.
     rewrite IH ?eq //.
     by apply/(gt_geq_trans' H1)/now_geq.
    case: ifP => ? /= H1 H2; last
       by apply/IH => //; rewrite eq.
    rewrite /= cats0 IH ?eq //.
    by apply/(gt_geq_trans' H1)/now_geq.
  + case eq : (compN_another xs env storage).2.1.2 =>
    [[]raisers refund_table
     [][]withdrawn funding_start []
     funding_end unconditional_refund_start].
    case: (contract_ None unit beneficiary) => [a H1 H2|??]; last
     by apply/IH => //; rewrite eq.
    case: ifP => H0; last first.
     rewrite IH ?eq //.
      apply/(gt_geq_trans' H1).
      by rewrite H0 geq_refl.
     by rewrite H0 /= in H2.
    by rewrite H0 /= in H2.
  + case eq : (compN_another xs env storage).2.1.2 =>
    [[]raisers refund_table
     [][]withdrawn funding_start []
     funding_end unconditional_refund_start].
    case: (map.get _ _ _ _ _) => [|??]; last by apply/IH => //; rewrite eq.
    case: (contract_ None unit eligible_address) => [??|???];
     last by apply/IH => //; rewrite eq.
    case: ifP => [H0|???]; last by apply/IH => //; rewrite eq.
    have->: storage.2.2.2 = unconditional_refund_start
     by rewrite (pres_unconditional_refund_start xs env storage) eq.
    case/andP: H0 => [] /andP[] ? /geq_gt C1 ? C2.
    by rewrite (gt_geq_trans' C2 (now_geq _ _)) in C1.
Qed.

Lemma mem_insert a b c d e f x y z:
  Relations_1.Transitive (fun a0 b0 => c a0 b0 = Lt) ->
  map.mem a b c x (map.insert a b c d e y f z) <->
  c y x = Eq \/ map.mem a b c x z.
Proof.
  move=> h; split => H1.
  + have H1' : is_true (map.mem a b c x (map.insert a b c d e y f z))
     by rewrite H1.
    case: (map.map_memget _ _ _ _ _ H1') => ? H2.
    case cxy: (c y x); auto.
    - rewrite map.get_insert_other // in H2.
      * move: (map.map_getmem _ _ _ _ _ _ H2).
        by case: (map.mem _ _ _ _ _); auto.
      * by rewrite -d cxy.
    - rewrite map.get_insert_other // in H2.
      * move: (map.map_getmem _ _ _ _ _ _ H2).
        by case: (map.mem _ _ _ _ _); auto.
      * by rewrite -d cxy.
  + case eq: (c y x).
    - move: eq; rewrite d => ->.
      suff: is_true (map.mem a b c x (map.insert a b c d e x f z))
       by case: (map.mem _ _ _ _ _).
      apply/map.map_getmem.
      by rewrite map.get_insert.
    - case: H1 eq => [-> //|] H1 yx.
      suff: is_true (map.mem a b c x (map.insert a b c d e y f z))
       by case: (map.mem _ _ _ _ _).
      have H1': is_true (map.mem a b c x z)
        by case: (map.mem a b c x z) H1.
      case: (map.map_memget _ _ _ _ _ H1') => X H2.
      apply (map.map_getmem _ _ _ _ _ X).
      by rewrite map.get_insert_other // -d yx.
    - case: H1 eq => [-> //|] H1 yx.
      suff: is_true (map.mem a b c x (map.insert a b c d e y f z))
       by case: (map.mem _ _ _ _ _).
      have H1': is_true (map.mem a b c x z)
        by case: (map.mem a b c x z) H1.
      case: (map.map_memget _ _ _ _ _ H1') => X H2.
      apply (map.map_getmem _ _ _ _ _ X).
      by rewrite map.get_insert_other // -d yx.
Qed.

Ltac mytac :=
  match goal with
  | H : Some ?x = Some ?y |- _ => apply map.unsome in H
  | H : existT _ ?x ?Hx = existT _ ?y ?Hy |- _ =>
    apply error.existT_eq_3 in H; destruct H; subst; simpl
  | H : exist _ ?x ?Hx = exist _ ?y ?Hy |- _ =>
    apply error.exist_eq_3 in H; destruct H; subst; simpl
  | H : eq_rec _ _ _ _ eq_refl = _ |- _ => simpl in H
  end.

Lemma remove_above_untouched a b c d e f k m
      (compare_eq_iff : forall x y, c x y = Eq <-> x = y)
  : forall v x1 y1 x2 k' v' m' H,
      map.get_above a b c k v x1 m = y1 ->
      x1 <> x2 ->
      map.remove_above a b c d e f k v x2 m = Some (existT _ k' (existT _ v' (exist _ m' H))) ->
      map.get_above a b c k' v' x1 m' = y1.
Proof.
 have compare_refl : forall a, c a a = Eq.
  move=> x.
  by rewrite compare_eq_iff.
 induction m; intros v x1 y1 x2 k' v' m' H'; simpl.
  - case_eq (c x1 k); case_eq (c x2 k); try discriminate.
    + intros Hlt He Hy1 Hx1x2 HS.
      apply compare_eq_iff in He; subst.
      repeat mytac.
      rewrite /= in e0.
      case: e0 => -> <- /=.
      by rewrite compare_refl.
    + intros Hlt He Hy1 Hx1x2 HS.
      apply compare_eq_iff in He; subst.
      repeat mytac.
      case: e0 => -> <- /=.
      by rewrite compare_refl.
    + intros H1 H2 Hy1 Hx1x2 HS.
      repeat mytac.
      case: e0 => <- <- /=.
      by rewrite H2.
    + intros H1 H2 Hy1 Hx1x2 HS.
      repeat mytac.
      case: e0 => <- <- /=.
      by rewrite H2.
    + intros H1 H2 Hy1 Hx1x2 HS.
      repeat mytac.
      case: e0 => <- <- /=.
      by rewrite H2.
    + intros H1 H2 Hy1 Hx1x2 HS.
      repeat mytac.
      case: e0 => <- <- /=.
      by rewrite H2.
  - case_eq (c x1 k1).
    + intro He; apply compare_eq_iff in He; subst x1.
      intro Hv.
      case_eq (c x2 k1).
      * intros Hx2k1 Hk1x2 _.
        apply compare_eq_iff in Hx2k1.
        congruence.
      * intros Hx2k1 Hneq He.
        repeat mytac.
        case: e0 => <- <- /=.
        by rewrite compare_refl.
      * intros Hx2k1 Hneq.
        case_eq (map.remove_above a b c d e f k2 v2 x2 m).
        -- intros (k'', (v'', (m'', H''))) Hm.
           intro He.
           repeat mytac.
           case: e0 => <- <- /=.
           by rewrite compare_refl.
        -- intros Hn He.
           repeat mytac.
           case: e0 => <- <- /=.
           by rewrite compare_refl.
    + case_eq (c x2 k1).
      * intro He; apply compare_eq_iff in He; subst x2.
        intros.
        repeat mytac.
        case: e0 => <- <- /=.
        apply map.get_above_small.
        eapply e; eassumption.
      * intros.
        repeat mytac.
        case: e0 => <- <- /=.
        rewrite H1.
        reflexivity.
      * intros Hx2 Hx1 Hy1.
        case_eq (map.remove_above a b c d e f k2 v2 x2 m).
        -- intros (k'', (v'', (m'', H''))) He Hm Hn.
           repeat mytac.
           case: e0 => <- <- /=.
           by rewrite Hx1.
        -- intros Hn Hneq Hmem.
           repeat mytac.
           case: e0 => <- <- /=.
           by rewrite Hx1.
    + case_eq (c x2 k1).
      * intro He; apply compare_eq_iff in He; subst x2.
        intros.
        repeat mytac.
        by case: e0 => <- <- /=.
      * intros.
        repeat mytac.
        case: e0 => <- <- /=.
        by rewrite H1.
      * intros Hx2 Hx1 Hmem.
        case_eq (map.remove_above a b c d e f k2 v2 x2 m).
        -- intros (k'', (v'', (m'', H''))) He Hm Hn.
           specialize (IHm v2 x1 y1 x2 k'' v'' m'' H'' Hmem Hm He).
           repeat mytac.
           case: e0 => <- <- /=.
           by rewrite Hx1.
        -- intros Hn Hneq H''.
           repeat mytac.
           case: e0 => <- <- /=.
           rewrite Hx1.
           generalize (map.remove_above_none a b c d e f _ _ _ _ Hn).
           intro; subst m.
           simpl in Hn.
           case_eq (c x2 k2); intro Hx2k2; rewrite Hx2k2 in Hn;
             try discriminate; clear Hn.
           simpl.
           case_eq (c x1 k2); intro Hx1k2.
           ++ apply compare_eq_iff in Hx1k2.
              apply compare_eq_iff in Hx2k2.
              congruence.
           ++ reflexivity.
           ++ reflexivity.
Qed.

Lemma remove_absent_other a b c d e f x1 x2 m :
  map.get a b c x1 m = None ->
  x1 <> x2 ->
  map.get a b c x1 (map.remove a b c d e f x2 m) = None.
Proof.
  destruct m; simpl.
  - reflexivity.
  - case_eq (map.remove_above a b c d e f k v x2 s); simpl.
    + intros (k', (v', (m', H'))) Hsome Hmemt Hmemf.
      eapply remove_above_untouched; eassumption.
    + reflexivity.
Qed.


Lemma mem_remove' a b c d e f x y z v:
  x <> y ->
  map.get a b c x (map.remove a b c d e f y z) = Some v ->
  map.get a b c x z = Some v.
Proof.
  case eq: (map.get a b c x z) => [X|] xy H1.
   by rewrite -(map.remove_present_untouched _ _ _ _ _ _ _ _ _ _ eq xy).
  move: H1 => <-.
  case eq': (map.get a b c y z) => [Y|]; last by rewrite map.remove_absent.
  by rewrite remove_absent_other.
Qed.

Lemma mem_remove a b c d e f x y z:
  map.mem a b c x (map.remove a b c d e f y z) ->
  map.mem a b c x z.
Proof.
  have compare_refl : forall a, c a a = Eq
   by move=> X; rewrite d.
  move=> H.
  case eq: (c x y).
  + move: eq H.
    rewrite d => -> H.
    have H' : is_true (map.mem a b c y (map.remove a b c d e f y z))
     by case: (map.mem _ _ _ _ _) H.
    case: (map.map_memget _ _ _ _ _ H') => X.
    by rewrite map.remove_present_same.
  + have H' : is_true (map.mem a b c x (map.remove a b c d e f y z))
     by case: (map.mem _ _ _ _ _) H.
    case: (map.map_memget _ _ _ _ _ H') => v H1.
    suff: is_true (map.mem a b c x z) by case: (map.mem a b c x z).
    apply (map.map_getmem _ _ _ _ _ v).
    apply/(@mem_remove' _ _ _ _ _ _ x y) => //.
     move=> xy.
     by rewrite xy compare_refl in eq.
  + have H' : is_true (map.mem a b c x (map.remove a b c d e f y z))
     by case: (map.mem _ _ _ _ _) H.
    case: (map.map_memget _ _ _ _ _ H') => v H1.
    suff: is_true (map.mem a b c x z) by case: (map.mem a b c x z).
    apply (map.map_getmem _ _ _ _ _ v).
    apply/(@mem_remove' _ _ _ _ _ _ x y) => //.
     move=> xy.
     by rewrite xy compare_refl in eq.
Qed.

Lemma uniq_eligible_address xs env storage eligible_address :
  gt storage.2.2.2 storage.2.2.1 ->
  (compN_another xs env storage).2.1.2.2.1.1 = false ->
  eligible_address \in [seq destination i | i <- (compN_another xs env storage).2.1.1] ->
  ~~ map.mem address_constant tez.mutez address_compare eligible_address (compN_another xs env storage).2.1.2.1.2.
Proof.
  elim: xs env storage eligible_address => // x xs IH env storage eligible_address.
  rewrite /= /comp_another /=.
  case: x => [][refund_address|[beneficiary|eligible_address']] fuel;
  rewrite /eval_seq_another /=.
  + case eq : (compN_another xs env storage).2.1.2 =>
    [[]raisers refund_table
     [][]withdrawn funding_start []
     funding_end unconditional_refund_start].
    case: (map.get address_constant tez.mutez address_compare _ _) => [z|].
     case: (tez.of_Z _) => [e H1 H2|a /=].
      by move: (IH env storage); rewrite /= eq /=; apply.
     case: ifP => i /=; last
      by move: (IH env storage); rewrite /= eq /=; apply.
     rewrite cats0.
     move=> H1 H2 H3.
     apply/negP; rewrite mem_insert //; last by apply (lt_trans address).
     have H2' : (compN_another xs env storage).2.1.2.2.1.1 = false
      by rewrite eq.
     case C: (map.mem address_constant tez.mutez address_compare eligible_address refund_table).
      move=> _.
      apply/negP: (IH _ _ _ H1 H2' H3).
      by rewrite negbK eq.
     case=>// C0; move: C0 H3 C.
     rewrite (compare_eq_iff address) => <-.
     rewrite compN_unconditional_refund_start //.
     apply/(gt_geq_trans' H1).
     rewrite (pres_funding_end xs env) eq.
     by case/andP: i.
    move=> H1 /=.
    case: ifP => i /=; last
      by move: (IH env storage); rewrite /= eq /=; apply.
    rewrite cats0.
    move=> H2 H3.
    apply/negP; rewrite mem_insert //; last by apply (lt_trans address).
    have H2' : (compN_another xs env storage).2.1.2.2.1.1 = false
     by rewrite eq.
    case C: (map.mem address_constant tez.mutez address_compare eligible_address refund_table).
     move=> _.
     apply/negP: (IH _ _ _ H1 H2' H3).
     by rewrite negbK eq.
    case=>// C0; move: C0 H3 C.
    rewrite (compare_eq_iff address) => <-.
    rewrite compN_unconditional_refund_start //.
    apply/(gt_geq_trans' H1).
    rewrite (pres_funding_end xs env) eq.
    by case/andP: i.
  + case eq : (compN_another xs env storage).2.1.2 =>
    [[]raisers refund_table
     [][]withdrawn funding_start []
     funding_end unconditional_refund_start].
    case: (contract_ None unit beneficiary); last
      by move: (IH env storage); rewrite /= eq /=; apply.
    move=> a /=.
    case: ifP => H //=.
    by move: (IH env storage); rewrite /= eq /=; apply.
  + case eq : (compN_another xs env storage).2.1.2 =>
    [[]raisers refund_table
     [][]withdrawn funding_start []
     funding_end unconditional_refund_start] => /=.
    case: (map.get _ _ _ _ _); last
     by move: (IH env storage); rewrite /= eq /=; apply.
    move=> a /=.
    case: (contract_ None unit _); last
     by move: (IH env storage); rewrite /= eq /=; apply.
    move=> a0.
    case: ifP => c; last
     by move: (IH env storage); rewrite /= eq /=; apply.
    rewrite map_cat /= mem_cat in_cons orbF.
    case C: (eligible_address == eligible_address'); last first.
     rewrite orbF => H1 H2 H3.
     apply/negP => C0.
     move: (mem_remove C0).
     apply/negP.
     move: (IH env storage eligible_address H1).
     rewrite !eq /=.
     by apply.
    move=> H1 H2 _.
    rewrite (eqP C).
    apply/negP => C0.
    have H0: is_true (map.mem address_constant tez.mutez address_compare eligible_address' (map.remove address_constant tez.mutez address_compare (compare_eq_iff address) (lt_trans address) (gt_trans address) eligible_address' refund_table))
     by case: (map.mem _ _ _ _ _) C0.
    case: (map.map_memget _ _ _ _ _ H0) => v.
    by rewrite map.remove_present_same.
Qed.

Lemma refund_refund
      (xs : seq (data parameter_ty * Datatypes.nat))
      env storage :
gt storage.2.2.2 storage.2.2.1 ->
let '(env, (ops, storage, tt)) := compN_another xs env storage in
@uniq [eqType of data address] (seq.map destination ops).
Proof.
  suff: gt storage.2.2.2 storage.2.2.1 ->
    @uniq [eqType of data address] (seq.map destination (compN_another xs env storage).2.1.1)
   by case: (compN_another xs env storage) => [] env0 [][] ?? [].
  elim: xs env storage => //= x xs IH env storage.
  case compN_eq': (compN_another xs env storage) => [env0 [][] ops st []].
  rewrite /comp_another /=.
  case eq: (eval_seq_another env0 x.2 (x.1, st, tt)) => [/=|[] a []].
   have<-: (compN_another xs env storage).2.1.1 = ops by rewrite compN_eq'.
   by apply/IH.
  case: a eq => [] opsB st0 /= H.
  rewrite map_cat uniq_catC cat_uniq => H1.
  have<-: (compN_another xs env storage).2.1.1 = ops by rewrite compN_eq'.
  rewrite IH // andbT.
  case: x H => [][refund_address|[beneficiary|eligible_address]] fuel;
  rewrite /eval_seq_another /=.
  + case: st compN_eq' => [][] raisers refund_table [][] withdrawn funding_start
              [] funding_end unconditional_refund_start compN_eq'.
    case: (map.get address_constant tez.mutez address_compare (Implicit refund_address) refund_table) => [?|/=].
     case: (tez.of_Z _) => //= ?.
     case: ifP => // ? [] <- ? /=.
     by elim: [seq destination i | i <- _].
    case: ifP => // ? [] <- ? /=.
    by elim: [seq destination i | i <- _].
  + case: st compN_eq' => [][] raisers refund_table [][] withdrawn funding_start
              [] funding_end unconditional_refund_start compN_eq'.
    case: (contract_ None unit beneficiary) => // ?.
    case: ifP => // C [] <- st0_eq /=.
    case: hasP => // [][] x /=.
    rewrite in_cons orbF => + /eqP xe.
    rewrite {}xe => {x}.
    have ?: (compN_another xs env storage).2.1.2.2.1.1 = false.
     rewrite compN_eq' /=; case: C.
     by case/andP => ? /eqP.
    rewrite compN_unconditional_refund_start //
             (pres_unconditional_refund_start xs env storage) compN_eq' /=.
    by case/andP: C => []/andP[]/andP[].
  + case: st compN_eq' => [][] raisers refund_table [][] withdrawn funding_start
              [] funding_end unconditional_refund_start compN_eq'.
    case H: (map.get _ _ _ _ _) => [a|//].
    case: (contract_ None unit _) => // b.
    case: ifP => // c [] <- _.
    case: hasP => // [][] x /=.
    rewrite in_cons orbF => + /eqP xe.
    rewrite {}xe => {x IH} C.
    have H2: (compN_another xs env storage).2.1.2.2.1.1 = false
     by rewrite compN_eq' /=; case/andP: c => ? /eqP.
    have H3: geq (now (compN_another xs env storage).1) storage.2.2.2.
     rewrite (pres_unconditional_refund_start xs env) compN_eq'.
     by case/andP: c => [] /andP[].
    have H4: map.mem address_constant tez.mutez address_compare eligible_address (compN_another xs env storage).2.1.2.1.2.
     rewrite compN_eq' /=.
     apply/negP => /negP /negPf.
     rewrite map.get_mem_false => C1.
     by rewrite C1 in H.
    by move: H4 (uniq_eligible_address H1 H2 C) => ->.
Qed.
End crowdfunding.

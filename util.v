From Michocoq Require Import semantics util macros
     untyper micheline2michelson michelson2micheline micheline_pp.
Import syntax error.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import String.
Open Scope string_scope.
Import Notations.

Definition pp b parameter_ty storage_ty
           (contract : full_contract b parameter_ty None storage_ty) := "{
parameter (" ++ micheline_pp (michelson2micheline_type parameter_ty) 2 true true
            ++ ");
storage (" ++ micheline_pp (michelson2micheline_type storage_ty) 2 true true
            ++ ");
code " ++ micheline_pp
            (michelson2micheline_instruction
               (untype_instruction untype_Readable (Instruction_seq contract))) 2 true true
            ++ ";}".

Definition ppc self_type tff a b (ins: instruction_seq self_type tff a b) :=
micheline_pp
  (michelson2micheline_instruction
     (untype_instruction untype_Readable (Instruction_seq ins))) 2 true true.

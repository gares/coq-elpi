(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

DECLARE PLUGIN "elpi_plugin"

open Stdarg
open Ltac_plugin

open Pcoq
open Pcoq.Constr
open Pcoq.Prim

module EV = Coq_elpi_vernacular
module U = Coq_elpi_utils

(* Arguments ************************************************************* *)
let pr_elpi_string _ _ _ (_,s : Ploc.t * string) = Pp.str s
ARGUMENT EXTEND elpi_string PRINTED BY pr_elpi_string
[ "xxxxxxxx" ] -> [ (Ploc.dummy, "") ]   (* XXX To be removed when maxime's patches gets merged *)
END
GEXTEND Gram GLOBAL: elpi_string;
elpi_string : [[ s = string -> loc, s ]];
END

let pr_fp _ _ _ (_,x) = EV.pr_qualified_name x
ARGUMENT EXTEND qualified_name PRINTED BY pr_fp
[ "xxxxxxxx" ] -> [ Ploc.dummy, [] ]   (* XXX To be removed when maxime's patches gets merged *)
END
GEXTEND Gram GLOBAL: qualified_name;
qualified_name : [[ i = IDENT; s = LIST0 FIELD -> loc, i :: s ]];
END

(* Anti-quotation ******************************************************** *)
let pr_elpi_code _ _ _ (s : string) = Pp.str s

ARGUMENT EXTEND elpi_code
    PRINTED BY pr_elpi_code
 [ "xxxxxxx" ] -> [ "" ] (* XXX To be removed when maxime's patches get merged 
*)
END
let () = Coq_elpi_glob_quotation.is_elpi_code :=
           (fun x -> Genarg.(has_type x (glbwit wit_elpi_code)))
let () = Coq_elpi_glob_quotation.get_elpi_code :=
           (fun x -> Genarg.(out_gen (glbwit wit_elpi_code) x))
GEXTEND Gram
  GLOBAL: operconstr;

  operconstr: LEVEL "0"
    [ [ "lp"; ":"; id = IDENT ->
          let arg = Genarg.in_gen (Genarg.rawwit wit_elpi_code) id in
          CAst.make ~loc:!@loc
             (Constrexpr.CHole (None, Misctypes.IntroAnonymous, Some arg)) ] 
    | [ "lp"; ":"; "_" ->
          let arg = Genarg.in_gen (Genarg.rawwit wit_elpi_code) "_" in
          CAst.make ~loc:!@loc
             (Constrexpr.CHole (None, Misctypes.IntroAnonymous, Some arg)) ] 
    | [ "lp"; ":"; s = STRING -> 
          let arg = Genarg.in_gen (Genarg.rawwit wit_elpi_code) s in
          CAst.make ~loc:!@loc
            (Constrexpr.CHole (None, Misctypes.IntroAnonymous, Some arg)) ] 
          ]
  ;
END

(* Syntax **************************************************************** *)
let pr_glob_constr_and_expr = function
  | (_, Some c) -> Ppconstr.pr_constr_expr c
  | (c, None) -> Printer.pr_glob_constr_env (Global.env ()) c

let pp_elpi_arg _ _ _ = EV.pr_arg (fun (_,x) -> pr_glob_constr_and_expr x)
let pp_glob_elpi_arg _ _ _ = EV.pr_arg pr_glob_constr_and_expr
let pp_raw_elpi_arg _ _ _ = EV.pr_arg Ppconstr.pr_constr_expr

let glob_elpi_arg = EV.glob_arg
let interp_elpi_arg = EV.interp_arg
let subst_elpi_arg mod_subst = function
  | EV.Qualid _ as x -> x
  | EV.DashQualid _ as x -> x
  | EV.Int _ as x -> x
  | EV.String _ as x -> x
  | EV.Term t ->
      EV.Term (Tacsubst.subst_glob_constr_and_expr mod_subst t)

ARGUMENT EXTEND elpi_arg
PRINTED BY pp_elpi_arg
INTERPRETED BY interp_elpi_arg
GLOBALIZED BY glob_elpi_arg
SUBSTITUTED BY subst_elpi_arg
RAW_PRINTED BY pp_raw_elpi_arg
GLOB_PRINTED BY pp_glob_elpi_arg
| [ qualified_name(s) ] -> [ EV.Qualid (snd s) ]
| [ "-" qualified_name(s) ] -> [ EV.DashQualid (snd s) ]
| [ string(s) ] -> [ EV.String s ]
| [ integer(n) ] -> [ EV.Int n ]
| [ constr(t) ] -> [ EV.Term t ]
END

VERNAC COMMAND EXTEND Elpi CLASSIFIED AS SIDEFF
| [ "Elpi" "Accumulate" "File" string_list(s) ] -> [ EV.load_files s ]
| [ "Elpi" "Accumulate" "Files" string_list(s) ] -> [ EV.load_files s ]
| [ "Elpi" "Accumulate" elpi_string(s) ] -> [ EV.load_string s ]
| [ "Elpi" "Accumulate" qualified_name(p) "File" string_list(s) ] ->
  [ EV.set_current_program (snd p);EV.load_files s ]
| [ "Elpi" "Accumulate" qualified_name(p) "Files" string_list(s) ] ->
  [ EV.set_current_program (snd p);EV.load_files s ]
| [ "Elpi" "Accumulate" qualified_name(p) elpi_string(s) ] ->
  [ EV.set_current_program (snd p);EV.load_string s ]
| [ "Elpi" "Accumulate" "Db" qualified_name(d) ] -> [ EV.load_db (snd d) ]
| [ "Elpi" "Accumulate" qualified_name(p) "Db" qualified_name(d) ] ->
  [ EV.set_current_program (snd p);EV.load_db (snd d) ]

| [ "Elpi" "Debug" string_list(s) ] -> [ EV.debug s ]
| [ "Elpi" "Trace" string_opt(s) ] -> [ EV.trace s ]
| [ "Elpi" "Trace" int(start) int(stop) ] -> [ EV.trace_at start stop ]
| [ "Elpi" "Trace" "Off" ] -> [ EV.trace (Some "") ]
| [ "Elpi" "Bound" "Steps" int(steps) ] -> [ EV.bound_steps steps ]

| [ "Elpi" "Print" qualified_name(p) string_list(s) ] -> [ EV.print p s ]

| [ "Elpi" "Command" qualified_name(p) elpi_string_opt(s) ] ->
    [ EV.set_current_program ~kind:EV.Command (snd p);
      Option.iter EV.load_string s ]
| [ "Elpi" "Tactic" qualified_name(p) elpi_string_opt(s) ] ->
    [ EV.set_current_program ~kind:EV.Tactic (snd p);
      Option.iter EV.load_string s ]
| [ "Elpi" "Db" qualified_name(d) elpi_string(s) ] ->
    [ EV.declare_db (snd d) s ]

| [ "Elpi" "Query" elpi_string(s) ] ->
    [ EV.run_in_program s ]
| [ "Elpi" "Query"  qualified_name(program) elpi_string(s) ] ->
    [ EV.run_in_program ~program s ]
| [ "Elpi" qualified_name(program) elpi_arg_list(args) ] ->
    [ EV.run_program program args ]

| [ "Elpi" "Typecheck" ] -> [ EV.typecheck () ]
| [ "Elpi" "Typecheck" qualified_name(program) ] -> [ EV.typecheck ~program () ]

| [ "Elpi" "HOAS" ne_string_list(s) ] -> [ EV.load_hoas_def s ]
| [ "Elpi" "Checker" string(s) ] -> [ EV.load_checker s ]
| [ "Elpi" "Printer" string(s) ] -> [ EV.load_printer s ]
| [ "Elpi" "CommandTemplate" string(s) ] -> [ EV.load_command s ]
| [ "Elpi" "TacticTemplate" string(s) ] -> [ EV.load_tactic s ]
END

TACTIC EXTEND elpi_tac
| [ "elpi" qualified_name(program) elpi_arg_list(args) ] ->
  [ EV.run_tactic program ist args ]
| [ "elpi" "query" elpi_string(s) elpi_arg_list(args) ] ->
  [ EV.run_in_tactic s ist args ]
| [ "elpi" "query"  qualified_name(program) elpi_string(s) elpi_arg_list(args) ] ->
  [ EV.run_in_tactic s ~program ist args ]
  
END

(* vim:set ft=ocaml: *)

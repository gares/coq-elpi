(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

val init : paths:string list -> unit
val exec : string -> unit
val load_files : string list -> unit
val load_string : string -> unit
val trace : string option -> unit

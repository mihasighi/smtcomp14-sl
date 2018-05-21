open Lib
open Symheap

(* goal: also allow checking consistency of a predicate given by the user  *)
(* let cl_predicate = ref ""                                               *)
let defs_path = ref "examples/sl.defs"

module Parser = Sl_parser
module Lexer = Sl_lexer
module F = Slsat_frontend


let defs_of_channel c =
	let lexbuf = Lexing.from_channel c in
	try
		let defs = Parser.ind_def_set Lexer.token lexbuf in
		begin
			(** WARNING: Added to obtain translation to SMTLIB v2 *)
			Symheap.Defs.to_smtlib defs;
			defs
		end
	with
	| Lexer.Error msg -> print_endline msg ; assert false
	| Parser.Error -> Printf.fprintf stderr "At offset %d: syntax error.\n%!" (Lexing.lexeme_start lexbuf) ; assert false

let () = F.usage := !F.usage ^ " [-D <file>] -r <def>" 

let () = F.speclist := !F.speclist @ [
       ("-D", Arg.Set_string defs_path,
           ": read inductive definitions from <file>, default is " ^ !defs_path
       );
	(** WARNING: Added to obtain translation to SMTLIB v2 *)
       ("-r", Arg.Set_string Symheap.defs_root,
	   ": set root inductive definition, default is " ^ !defs_root
       );
	(* ("-C", Arg.Set_string cl_predicate,*)
	(*  ": prove consistency of the SL predicate provided in <string>"); *)
	]


let () =
	Arg.parse !F.speclist (fun _ -> raise (Arg.Bad "Stray argument found.")) !F.usage ;
	let res = F.check_consistency (defs_of_channel (open_in !defs_path)) in
  let () = print_endline ("Exit code: " ^ (string_of_int res)) in 
	exit res



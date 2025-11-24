(* S-Expression Export for Megalodon *)
open Syntax

let rec sexpr_escape s =
  let b = Buffer.create (String.length s + 5) in
  Buffer.add_char b '"';
  String.iter (fun c ->
    if c = '"' || c = '\\' then Buffer.add_char b '\\';
    Buffer.add_char b c
  ) s;
  Buffer.add_char b '"';
  Buffer.contents b

(* Helper to print lists *) 
let sexpr_list f l = "(" ^ String.concat " " (List.map f l) ^ ")"

let rec ltree_to_sexpr (l:ltree) : string =
  match l with
  | NaL s -> sexpr_escape s
  | NuL(b,s1,_,_) -> Printf.sprintf "(Num %s %s)" (if b then "real" else "int") (sexpr_escape s1)
  | StringL s -> Printf.sprintf "(String %s)" (sexpr_escape s)
  | QStringL s -> Printf.sprintf "(QString %s)" (sexpr_escape s)
  | InfoL(op,l,r) -> 
      let op_str = match op with
        | InfixOp s -> s
        | InfixImp -> "->"
        | InfixIff -> "<->"
        | InfixAnd -> "/\"
        | InfixOr -> "\\/"
        | InfixEq -> "="
        | InfixIn -> ":e"
        | InfixSubq -> "c="
        | _ -> "?op?"
      in
      Printf.sprintf "(%s %s %s)" (sexpr_escape op_str) (ltree_to_sexpr l) (ltree_to_sexpr r)
  | PreoL(s,l) -> Printf.sprintf "(%s %s)" (sexpr_escape s) (ltree_to_sexpr l)
  | PostoL(s,l) -> Printf.sprintf "(%s %s)" (sexpr_escape s) (ltree_to_sexpr l)
  | BiL(b, _, vl, r) -> 
      (* Binder: b is binder name, vl is var list *)
      let vars = String.concat " " (List.map (fun (ns, _) -> sexpr_list sexpr_escape ns) vl) in
      Printf.sprintf "(%s (%s) %s)" (sexpr_escape b) vars (ltree_to_sexpr r)
  | MTupleL(l, ls) -> 
      let args = String.concat " " (List.map ltree_to_sexpr (l::ls)) in
      Printf.sprintf "(%s)" args (* Application or Tuple *)
  | IfThenElseL(c,t,e) -> Printf.sprintf "(if %s %s %s)" (ltree_to_sexpr c) (ltree_to_sexpr t) (ltree_to_sexpr e)
  | LeL(x,_,v,b) -> Printf.sprintf "(let %s %s %s)" (sexpr_escape x) (ltree_to_sexpr v) (ltree_to_sexpr b)
  | ParenL(l,_) -> ltree_to_sexpr l (* Ignore extra parens *)
  | _ -> "\"(Unknown ltree)\""

let docitem_to_sexpr (d:docitem) : string =
  match d with
  | DefDecl(n, Some ty, tm) -> Printf.sprintf "(Definition %s %s %s)" (sexpr_escape n) (ltree_to_sexpr ty) (ltree_to_sexpr tm)
  | DefDecl(n, None, tm) -> Printf.sprintf "(Definition %s _ %s)" (sexpr_escape n) (ltree_to_sexpr tm)
  | ThmDecl(n, _, tm) -> Printf.sprintf "(Theorem %s %s)" (sexpr_escape n) (ltree_to_sexpr tm)
  | AxDecl(n, tm) -> Printf.sprintf "(Axiom %s %s)" (sexpr_escape n) (ltree_to_sexpr tm)
  | ParamDecl(n, tm) -> Printf.sprintf "(Parameter %s %s)" (sexpr_escape n) (ltree_to_sexpr tm)
  | VarDecl(ns, _, tm) -> 
      let names = String.concat " " (List.map sexpr_escape ns) in
      Printf.sprintf "(Variable (%s) %s)" names (ltree_to_sexpr tm)
  | Section n -> Printf.sprintf "(Section %s)" (sexpr_escape n)
  | End n -> Printf.sprintf "(End %s)" (sexpr_escape n)
  | PostInfixDecl(op, tm, prec, assoc) -> 
      let asc = match assoc with InfixLeft -> "left" | InfixRight -> "right" | _ -> "none" in
      Printf.sprintf "(Infix %s %s %d %s)" (sexpr_escape op) (ltree_to_sexpr tm) prec asc
  | _ -> ""

let print_docitem d =
  let s = docitem_to_sexpr d in
  if s <> "" then (print_endline s; flush stdout)
open Why3
open Ptree
open Mod_subst
module T = Uterm

type odecl =
  | Odecl of Loc.position * decl
  | Omodule of Loc.position * ident * odecl list

let mk_odecl loc d = Odecl (loc, d)
let mk_omodule loc id mod_expr = Omodule (loc, id, mod_expr)

type path = string list

type info_refinement = {
  info_ref_name : qualid option;
  info_ref_decl : odecl list;
  info_subst : subst;
  info_path : path;
}

let mk_info_refinement info_ref_name info_ref_decl info_subst info_path =
  { info_ref_name; info_ref_decl; info_subst; info_path }

type info = {
  (* to be completed as needed *)
  info_arith_construct : (string, int) Hashtbl.t;
  info_refinement : (string, info_refinement) Hashtbl.t;
  info_iter_argument : (string, int) Hashtbl.t;
  (* expression nesting level *)
  info_nesting : term list;
}

let empty_info () =
  {
    info_arith_construct = Hashtbl.create 32;
    info_refinement = Hashtbl.create 32;
    info_iter_argument = Hashtbl.create 32;
    info_nesting = [];
  }

let add_info info id arith = Hashtbl.add info.info_arith_construct id arith
let add_nesting info t = { info with info_nesting = t @ info.info_nesting }
let add_iter_argument info (s, i) = Hashtbl.add info.info_iter_argument s i

let add_info_refinement info id info_refinement =
  Hashtbl.add info.info_refinement id info_refinement

let mk_dtype loc td_list = mk_odecl loc (Dtype td_list)
let mk_coercion loc f = mk_odecl loc (Dmeta (T.mk_id "coercion", [ Mfs f ]))

let mk_dlogic loc coerc f =
  let coerc = match coerc with None -> [] | Some c -> [ mk_coercion loc c ] in
  mk_odecl loc (Dlogic f) :: coerc

let mk_dprop loc prop_kind id t = mk_odecl loc (Dprop (prop_kind, id, t))

let mk_ind loc in_ident in_params in_def =
  let ind_decl = { in_loc = loc; in_ident; in_params; in_def } in
  mk_odecl loc (Dind (Decl.Ind, [ ind_decl ]))

let mk_dlet loc id ghost rs_kind expr =
  mk_odecl loc (Dlet (id, ghost, rs_kind, expr))

let mk_drec loc fd_list = mk_odecl loc (Drec fd_list)
let mk_dexn loc id pty mask = mk_odecl loc (Dexn (id, pty, mask))

let mk_duseimport loc ?(import = true) q_list =
  mk_odecl loc (Duseimport (loc, import, q_list))

let mk_functor loc id arg body = mk_omodule loc id arg :: body

let mk_cloneexport ?odecl_loc id clone_subst =
  let loc = match odecl_loc with Some l -> l | None -> Loc.dummy_position in
  mk_odecl loc (Dcloneexport (loc, id, clone_subst))

module Iteration = struct
  open Gospel.Utils
  open Gospel

  let args = Hstr.create 16

  let populate_map l =
    List.iter
      (fun (x, y) -> match x with Some x -> Hstr.add args x y | None -> ())
      l

  let get_term a =
    let x =
      try Hstr.find args a
      with Not_found ->
        let err = Printf.sprintf "Missing %s argument" a in
        failwith err
    in
    match (x : Uast.iter_arg_type) with
    | Term x -> x
    | Pty _ -> failwith "Not a term"

  let get_pty a =
    let x =
      try Hstr.find args a
      with Not_found ->
        let err = Printf.sprintf "Missing %s argument" a in
        failwith err
    in
    match (x : Uast.iter_arg_type) with
    | Pty y -> y
    | Term _ -> failwith "Not a Pty"

  let get_term_opt a = Hstr.find_opt args a
end

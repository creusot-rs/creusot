(* vc_spans_stub.ml — OCaml stub for the vc-spans Rust crate. *)

open Why3

(* ------------------------------------------------------------------ *)
(* Helpers                                                             *)
(* ------------------------------------------------------------------ *)

let is_source_file f =
  not (String.length f >= 5 &&
       String.sub f (String.length f - 5) 5 = ".coma")

let all_source_locs (root : Term.term) : Loc.position list =
  let seen = Hashtbl.create 8 in
  let result = ref [] in
  let rec walk t =
    List.iter (fun loc ->
      let file, l1, c1, _, _ = Loc.get loc in
      if is_source_file file then begin
        let key = (file, l1, c1) in
        if not (Hashtbl.mem seen key) then begin
          Hashtbl.add seen key ();
          result := loc :: !result
        end
      end
    ) t.Term.t_locs;
    Term.t_iter walk t
  in
  walk root;
  List.rev !result

let first_source_loc (root : Term.term) : Loc.position option =
  match all_source_locs root with loc :: _ -> Some loc | [] -> None

let second_source_loc (root : Term.term) : Loc.position option =
  match all_source_locs root with _ :: loc :: _ -> Some loc | _ -> None

(** For precondition VCs, find the call-site location by walking the task's
    hypothesis chain (task_prev) and returning the first source location that
    differs from the goal's own location. *)
let call_site_loc (task : Task.task) (goal_file : string) (goal_l1 : int) : Loc.position option =
  let result = ref None in
  let rec walk_task t =
    match t with
    | None -> ()
    | Some { Task.task_decl = td; Task.task_prev = prev; _ } ->
      (* Walk the term in this declaration looking for a source location
         that is different from the goal's own location. *)
      (match td.Theory.td_node with
       | Theory.Decl { Decl.d_node = Decl.Dprop ((Decl.Paxiom | Decl.Plemma), _, t); _ } ->
         let rec walk_term tm =
           List.iter (fun loc ->
             let file, l1, _, _, _ = Loc.get loc in
             if is_source_file file && not (file = goal_file && l1 = goal_l1) then
               (match !result with None -> result := Some loc | Some _ -> ())
           ) tm.Term.t_locs;
           Term.t_iter walk_term tm
         in
         walk_term t
       | _ -> ());
      if !result = None then walk_task prev
  in
  walk_task task;
  !result

(** Walk a term looking for a sub-term whose attributes include a string
    matching [pred], and return the first source location on that sub-term. *)
let find_attr_source_loc (pred : string -> bool) (root : Term.term) : Loc.position option =
  let result = ref None in
  let rec walk t =
    if !result <> None then ()
    else begin
      let has_match =
        Ident.Sattr.exists (fun a -> pred a.Ident.attr_string) t.Term.t_attrs
      in
      if has_match then
        (match List.find_opt (fun loc ->
           let file, _, _, _, _ = Loc.get loc in is_source_file file
         ) t.Term.t_locs with
         | Some loc -> result := Some loc
         | None -> ());
      Term.t_iter walk t
    end
  in
  walk root;
  !result

let first_coma_loc (root : Term.term) : Loc.position option =
  let result = ref None in
  let rec walk t =
    List.iter (fun loc ->
      let file, _, _, _, _ = Loc.get loc in
      if not (is_source_file file) then
        (match !result with None -> result := Some loc | Some _ -> ())
    ) t.Term.t_locs;
    Term.t_iter walk t
  in
  walk root;
  !result

let loc_fields opt_loc =
  match opt_loc with
  | None -> ("", 0, 0, 0, 0)
  | Some loc ->
    let file, l1, c1, l2, c2 = Loc.get loc in
    (file, l1, c1, l2, c2)

(* ------------------------------------------------------------------ *)
(* Goal kind classification                                            *)
(* ------------------------------------------------------------------ *)

let contains s sub =
  let ls = String.length s and lsub = String.length sub in
  if lsub = 0 then true
  else if ls < lsub then false
  else begin
    let found = ref false in
    for i = 0 to ls - lsub do
      if not !found && String.sub s i lsub = sub then found := true
    done;
    !found
  end

let classify_expl (expl : string) : string =
  let e = String.lowercase_ascii expl in
  if e = "assertion" then "assertion"
  else if contains e "ensures" then "postcondition"
  else if contains e "requires" then "precondition"
  else if contains e "integer overflow"
       || contains e "index out of bounds"
       || contains e "attempt to divide"
       || contains e "attempt to subtract"
       || contains e "attempt to add"
       || contains e "attempt to multiply"
       || contains e "attempt to shift"
       || contains e "attempt to negate"
  then "overflow"
  else if contains e "unreachable" || contains e "panic" then "panic"
  else if contains e "refines" then "law"
  else if contains e "loop invariant" then "loop_invariant"
  else if contains e "loop variant" then "loop_variant"
  else if contains e "type invariant" then "type_invariant"
  else "other"

(* ------------------------------------------------------------------ *)
(* Global why3 environment                                             *)
(* ------------------------------------------------------------------ *)

(* Name of the splitting transformation to use. Determined once at init. *)
let split_trans_name : string ref = ref "split_vc"

let global_env : Env.env option ref = ref None

let init_env (conf_file : string) (extra_loadpath : string) : unit =
  let conf_arg =
    if conf_file = "" || not (Sys.file_exists conf_file) then None
    else Some conf_file
  in
  Loc.set_warning_hook (fun ?loc:_ _ -> ());
  let config =
    Whyconf.(
      let base = read_config conf_arg in
      let main = get_main base in
      let lp   = loadpath main in
      let main =
        if List.mem Config.datadir lp then main
        else set_loadpath main (Config.datadir :: lp)
      in
      set_main base main
    )
  in
  let main   = Whyconf.get_main config in
  let main   = Whyconf.set_libdir main Config.libdir in
  let _config = Whyconf.set_main config main in
  Whyconf.load_plugins main;
  let base_lp = Whyconf.loadpath main in
  let home = try Sys.getenv "HOME" with Not_found -> "" in
  let creusot_auto =
    List.filter (fun dir -> Sys.file_exists dir && Sys.is_directory dir) [
      Filename.concat Config.libdir "packages/creusot";
      Filename.concat home ".local/share/creusot/share/why3find/packages/creusot";
      Filename.concat
        (Filename.dirname (Filename.dirname
          (Filename.dirname (Filename.dirname Config.libdir))))
        "share/why3find/packages/creusot";
    ]
  in
  let extra_dirs =
    if extra_loadpath = "" then []
    else List.filter (fun s -> s <> "") (String.split_on_char ':' extra_loadpath)
  in
  let seen = Hashtbl.create 16 in
  let full_lp =
    List.filter_map (fun dir ->
      if Hashtbl.mem seen dir then None
      else begin Hashtbl.add seen dir (); Some dir end
    ) (base_lp @ creusot_auto @ extra_dirs)
  in
  let env = Env.create_env full_lp in
  (* Determine which splitting transformation is available. *)
  let tname =
    if (try ignore (Trans.lookup_transform_l "split_vc" env); true
        with Not_found | Trans.UnknownTrans _ -> false)
    then "split_vc"
    else if (try ignore (Trans.lookup_transform_l "split_goal_wp" env); true
             with Not_found | Trans.UnknownTrans _ -> false)
    then "split_goal_wp"
    else ""
  in
  split_trans_name := tname;
  global_env := Some env

let get_env () =
  match !global_env with
  | Some e -> e
  | None -> failwith "vc_spans: why3 environment not initialised; call init_env first"

(* ------------------------------------------------------------------ *)
(* VC span extraction                                                  *)
(* ------------------------------------------------------------------ *)

let goal_term task =
  match task with
  | Some { Task.task_decl = {
        Theory.td_node = Theory.Decl {
            Decl.d_node = Decl.Dprop (Decl.Pgoal, _, t) ; _ } ; _ } ; _ } ->
    Some t
  | _ -> None

(** Apply [split_vc] recursively, replicating the session's naming scheme.
    The session names each sub-goal as [parent_name ^ "." ^ string_of_int index].
    We stop recursing when split_vc produces zero sub-goals or the task is
    identical to itself (no progress).  Single-child splits are followed
    because the session records them as a transformation node too. *)

let rec collect_leaf_spans (env : Env.env) (parent_name : string)
    (task : Task.task)
    (orig_goal : Term.term option)
    (fallback_expl : string)
    (acc : (string * string * string
                               * string * int * int * int * int
                               * string * int * int * int * int
                               * string * int * int * int * int) list)
    : (string * string * string
       * string * int * int * int * int
       * string * int * int * int * int
       * string * int * int * int * int) list =
  let tname = !split_trans_name in
  let orig_term = goal_term task in
  let sub_tasks =
    if tname = "" then []
    else
      match Trans.apply_transform tname env task with
      | []       -> []
      | [single] ->
        (* Stop if the goal term is unchanged (split made no progress). *)
        let new_term = goal_term single in
        let same = match orig_term, new_term with
          | Some a, Some b -> Term.t_equal a b
          | None,   None   -> true
          | _              -> false
        in
        if same then [] else [single]
      | tasks    -> tasks
      | exception _ -> []
  in
  match sub_tasks with
  | [] ->
    let _id, expl0, _t2 = Termcode.goal_expl_task ~root:false task in
    (* When compute_specified strips the [@expl:...] attribute from the goal term,
       root:false returns "".  Fall back to the top-level expl captured before
       compute_specified ran. *)
    let expl =
      if expl0 <> "" then expl0
      else fallback_expl
    in
    let kind0 = classify_expl expl in
    let kind =
      if kind0 = "other" then
        let base = match String.index_opt parent_name '.' with
          | None   -> parent_name
          | Some i -> String.sub parent_name 0 i
        in
        if base = "refines" then "refinement" else kind0
      else kind0
    in
    let term = goal_term task in
    (* For type_invariant VCs, prefer the pre-rewrite location (the return type
       span) over the post-rewrite location (the invariant definition span),
       because compute_specified rewrites inv_T away and loses the call-site span.
       Search the original (pre-compute_specified) goal term for the sub-term
       whose expl attribute exactly matches this leaf's expl string. *)
    let primary_loc =
      if kind = "type_invariant" then
        let pre_loc =
          match orig_goal with
          | None -> None
          | Some t ->
            find_attr_source_loc
              (fun s -> String.lowercase_ascii s = "expl:" ^ String.lowercase_ascii expl)
              t
        in
        (match pre_loc with
         | Some _ -> pre_loc
         | None   -> Option.bind term first_source_loc)
      else
        Option.bind term first_source_loc
    in
    let (file, l1, c1, l2, c2)   = loc_fields primary_loc in
    let (file2, l1b, c1b, l2b, c2b) =
      if kind = "precondition" || kind = "refinement" then
        loc_fields (call_site_loc task file l1)
      else if kind = "type_invariant" then
        (* Secondary location: the invariant definition (first_source_loc of the
           post-rewrite goal, which is the invariant_T predicate declaration). *)
        loc_fields (Option.bind term first_source_loc)
      else
        loc_fields (Option.bind term second_source_loc)
    in
    let (coma_ref, cl1, cc1, cl2, cc2) = loc_fields (Option.bind term first_coma_loc) in
    (parent_name, expl, kind,
     file, l1, c1, l2, c2,
     file2, l1b, c1b, l2b, c2b,
     coma_ref, cl1, cc1, cl2, cc2) :: acc
  | children ->
    (* Internal node: recurse into each child with the session naming scheme. *)
    List.fold_left (fun acc (index, child) ->
      let child_name = parent_name ^ "." ^ string_of_int index in
      collect_leaf_spans env child_name child orig_goal fallback_expl acc
    ) acc (List.mapi (fun i t -> (i, t)) children)

let extract_spans (coma_file : string)
    : (string * string * string
       * string * int * int * int * int
       * string * int * int * int * int
       * string * int * int * int * int) list =
  let env = get_env () in
  let tmap, _format = Env.(read_file ~format:"coma" base_language env coma_file) in
  let theories = Wstdlib.Mstr.bindings tmap |> List.map snd in
  List.concat_map (fun theory ->
    let top_tasks = Task.split_theory theory None None in
    List.concat_map (fun top_task ->
      let top_name, _expl, _t = Termcode.goal_expl_task ~root:true top_task in
      let base_name = top_name.Ident.id_string in
      (* Capture the original (pre-compute_specified) goal term and expl so that
         leaf goals can look up their return-type span and kind even after
         compute_specified strips [@expl:...] attributes from the goal term. *)
      let orig_goal = goal_term top_task in
      let _, top_expl, _ = Termcode.goal_expl_task ~root:false top_task in
      let after_compute =
        match Trans.apply_transform "compute_specified" env top_task with
        | [child] -> [(base_name ^ ".0", child)]
        | children ->
          List.mapi (fun i t -> (base_name ^ "." ^ string_of_int i, t)) children
        | exception _ -> [(base_name, top_task)]
      in
      List.concat_map (fun (name, task) ->
        List.rev (collect_leaf_spans env name task orig_goal top_expl [])
      ) after_compute
    ) top_tasks
  ) theories

(* ------------------------------------------------------------------ *)
(* Exception printing                                                  *)
(* ------------------------------------------------------------------ *)

let string_of_exn exn =
  let buf = Buffer.create 64 in
  let fmt = Format.formatter_of_buffer buf in
  Exn_printer.exn_printer fmt exn;
  Format.pp_print_flush fmt ();
  let s = Buffer.contents buf in
  if String.length s > 9 && String.sub s 0 9 = "anomaly: "
  then String.sub s 9 (String.length s - 9)
  else s

(* ------------------------------------------------------------------ *)
(* Rust-safe wrappers                                                  *)
(* ------------------------------------------------------------------ *)

let safe_init_env (args : string) : string =
  try
    let conf_file, extra_loadpath =
      match String.index_opt args ':' with
      | None   -> (args, "")
      | Some i ->
        (String.sub args 0 i,
         String.sub args (i+1) (String.length args - i - 1))
    in
    init_env conf_file extra_loadpath;
    "ok"
  with exn -> "error: " ^ string_of_exn exn

let safe_extract_spans (coma_file : string) : string =
  try
    let spans = extract_spans coma_file in
    let buf   = Buffer.create 1024 in
    let first = ref true in
    List.iter (fun (name, expl, kind,
                    file,  l1,  c1,  l2,  c2,
                    file2, l1b, c1b, l2b, c2b,
                    coma_ref, cl1, cc1, cl2, cc2) ->
      if !first then first := false else Buffer.add_string buf "\n---\n";
      let add s = Buffer.add_string buf s; Buffer.add_char buf '\n' in
      add name; add expl; add kind;
      add file;  add (string_of_int l1);  add (string_of_int c1);
                 add (string_of_int l2);  add (string_of_int c2);
      add file2; add (string_of_int l1b); add (string_of_int c1b);
                 add (string_of_int l2b); add (string_of_int c2b);
      add coma_ref;
      add (string_of_int cl1); add (string_of_int cc1);
      add (string_of_int cl2); Buffer.add_string buf (string_of_int cc2)
    ) spans;
    Buffer.contents buf
  with exn -> "error: " ^ string_of_exn exn

let () =
  Callback.register "vc_spans_init_env" safe_init_env;
  Callback.register "vc_spans_extract"  safe_extract_spans

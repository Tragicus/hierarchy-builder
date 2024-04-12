module ConstSet = Set.Make(Names.Constant)
(* module ConstMap = Map.Make(Names.Constant) *)

let mixin_set = ref ConstSet.empty

(* let factory_set = ref ConstSet.empty *)

let factory_deps env sigma m =
   let rec accumulate_mixins t r =
      let _, arg, body = EConstr.destProd sigma t
      in try let c, _ = EConstr.destConst sigma arg
         in if ConstSet.mem c !mixin_set
         then accumulate_mixins body (ConstSet.add c r)
         else raise Constr.DestKO
      with Constr.DestKO -> accumulate_mixins body r
   in
   accumulate_mixins (Retyping.get_type_of env sigma (EConstr.mkConstU (m, EConstr.EInstance.empty))) ConstSet.empty

let mixin_deps = factory_deps

let synterp_declare_factory_of_record states r =
   let open Vernacentries.Preprocessed_Mind_decl in
   (* We extract the record from the output of the parser. *)
   let { flags; primitive_proj; kind; records } : record = r in
   let open Record.Ast in
   let { name; is_coercion; binders: Constrexpr.local_binder_expr list; cfs; idbuild; sort; default_inhabitant_id : Names.Id.t option } =
      match records with
      | [x] -> x
      | _ -> assert false (* mutually recursive records *)
   in 
   let name = name.CAst.v in
   let states, _ = Utils.Synterp.start_module states name in
   let states = Utils.Synterp.start_section states name in
   let states = Utils.Synterp.end_section states in
   let states, _ = Utils.Synterp.end_module states in
   List.rev states

let declare_factory_of_record states r =
   let open Vernacentries.Preprocessed_Mind_decl in
   (* We extract the record from the output of the parser. *)
   let { flags; primitive_proj; kind; records } : record = r in
   let open Record.Ast in
   let record =
      match records with
      | [x] -> x
      | _ -> assert false (* mutually recursive records *)
   in 
   let name = record.name.CAst.v in
   let states, _ = Utils.Interp.start_module states name in
   let states = Utils.Interp.start_section states name in
   let env = Global.env () in
   let sigma = Evd.from_env env in
   let () = Feedback.msg_info Pp.(str "binders: " ++ Ppconstr.pr_binders env sigma record.binders) in
   let declare_binders = function
     | [] -> ()
     | [key] -> 
     | param :: binders -> 
   let states = Utils.Interp.end_section states in
   let _ = Utils.Interp.end_module states in
   ()
   

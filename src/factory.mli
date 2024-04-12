val factory_deps : Environ.env -> Evd.evar_map -> Names.Constant.t -> Set.Make(Names.Constant).t

val mixin_deps : Environ.env -> Evd.evar_map -> Names.Constant.t -> Set.Make(Names.Constant).t

val synterp_declare_factory_of_record : Vernacstate.Synterp.t list -> Vernacentries.Preprocessed_Mind_decl.record -> Vernacstate.Synterp.t list

val declare_factory_of_record : Vernacstate.Synterp.t list -> Vernacentries.Preprocessed_Mind_decl.record -> unit

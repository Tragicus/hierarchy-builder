module Synterp : sig
   val start_module : Vernacstate.Synterp.t list -> Names.Id.t -> Vernacstate.Synterp.t list * (Names.ModPath.t * Declaremods.module_params_expr * Declaremods.module_expr Declaremods.module_signature)
   val end_module : Vernacstate.Synterp.t list -> Vernacstate.Synterp.t list * Names.ModPath.t
   val start_section : Vernacstate.Synterp.t list -> Names.Id.t -> Vernacstate.Synterp.t list
   val end_section : Vernacstate.Synterp.t list -> Vernacstate.Synterp.t list
end

module Interp : sig
   val unfreeze : Vernacstate.Synterp.t list -> Vernacstate.Synterp.t list
   val start_module : Vernacstate.Synterp.t list -> Names.Id.t -> Vernacstate.Synterp.t list * Names.ModPath.t
   val end_module : Vernacstate.Synterp.t list -> Vernacstate.Synterp.t list * Names.ModPath.t
   val start_section : Vernacstate.Synterp.t list -> Names.Id.t -> Vernacstate.Synterp.t list
   val end_section : Vernacstate.Synterp.t list -> Vernacstate.Synterp.t list
end

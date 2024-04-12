module Synterp = struct

  let start_module states name =
     let r = Declaremods.Synterp.start_module None name [] (Declaremods.Check []) in
     Vernacstate.Synterp.freeze () :: states, r

  let end_module states = 
     let r = Declaremods.Synterp.end_module () in
     Vernacstate.Synterp.freeze () :: states, r

  let start_section states name =
     Lib.Synterp.open_section name;
     Vernacstate.Synterp.freeze () :: states

  let end_section states =
     Lib.Synterp.close_section ();
     Vernacstate.Synterp.freeze () :: states



end

module Interp = struct

  let unfreeze = function
    | [] -> CErrors.user_err Pp.(str "More actions in the synterp phase than in the interp phase, did you forget to declare some actions?")
    | state :: states -> Vernacstate.Synterp.unfreeze state; states

  let start_module states name =
     let states = unfreeze states in
     let r = Declaremods.Interp.start_module None name [] (Declaremods.Check []) in
     states, r

  let end_module states = 
     let states = unfreeze states in
     let r = Declaremods.Interp.end_module () in
     states, r

  let start_section states name =
     let states = unfreeze states in
     Lib.Interp.open_section name;
     states
     
let end_section states =
     let states = unfreeze states in
     Lib.Interp.close_section ();
     states

end

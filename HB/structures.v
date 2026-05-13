(* Support constants, to be kept in sync with shim/structures.v *)
From Corelib Require Import ssreflect ssrfun.

Add Search Blacklist "Builders_".
Add Search Blacklist "__canonical__".
Add Search Blacklist "__to__".
Add Search Blacklist "_between_".
Add Search Blacklist "_mixin".

Variant error_msg := NoMsg | IsNotCanonicallyA (x : Type).
Definition unify T1 T2 (t1 : T1) (t2 : T2) (s : error_msg) :=
  phantom T1 t1 -> phantom T2 t2.
Definition id_phant {T} {t : T} (x : phantom T t) := x.
Definition id_phant_disabled {T T'} {t : T} {t' : T'} (x : phantom T t) := Phantom T' t'.
Definition nomsg : error_msg := NoMsg.
Definition is_not_canonically_a x := IsNotCanonicallyA x.
Definition new {T} (x : T) := x.
Definition eta {T} (x : T) := x.
Definition ignore {T} (x: T) := x.
Definition ignore_disabled {T T'} (x : T) (x' : T') := x'.


(* ********************* structures ****************************** *)
Set Primitive Projections.
From elpi Require Import elpi coercion tc cs.

From elpi.apps.tc.elpi Extra Dependency "tc_aux.elpi" as tc_aux.

TC.AddAllClasses.
TC.AddAllInstances.

Elpi Query TC.Solver lp:{{
  global C = {{ unify }},
  coq.TC.declare-class C.
}}.
Elpi Accumulate TC.Solver lp:{{
tc-HB.structures.tc-unify T T X1 X2 _ R :-
  coq.unify-eq X1 X2 ok,
  R = {{ @id_phant lp:T lp:X1 (@Phant lp:T lp:X1) }}.
}}.

Ltac done_tc := elpi TC.Solver.

Register unify as hb.unify.
Register id_phant as hb.id.
Register id_phant_disabled as hb.id_disabled.
Register ignore as hb.ignore.
Register ignore_disabled as hb.ignore_disabled.
Register Corelib.Init.Datatypes.None as hb.none.
Register nomsg as hb.nomsg.
Register is_not_canonically_a as hb.not_a_msg.
Register Corelib.Init.Datatypes.Some as hb.some.
Register Corelib.Init.Datatypes.pair as hb.pair.
Register Corelib.Init.Datatypes.prod as hb.prod.
Register Corelib.Init.Specif.sigT as hb.sigT.
Register Corelib.ssr.ssreflect.phant as hb.phant.
Register Corelib.ssr.ssreflect.Phant as hb.Phant.
Register Corelib.ssr.ssreflect.phantom as hb.phantom.
Register Corelib.ssr.ssreflect.Phantom as hb.Phantom.
Register Corelib.Init.Logic.eq as hb.eq.
Register Corelib.Init.Logic.eq_refl as hb.erefl.
Register new as hb.new.
Register eta as hb.eta.

#[deprecated(since="HB 1.0.1", note="use #[key=...] instead")]
Notation indexed T := T (only parsing).

Declare Scope HB_scope.
Notation "{  A  'of'  P  &  ..  &  Q  }" :=
  (sigT (fun A => (prod P .. (prod Q True) ..)%type))
  (at level 0, A at level 99) : HB_scope.
Notation "{  A  'of'  P  &  ..  &  Q  &  }" :=
  (sigT (fun A => (prod P .. (prod Q False) ..)%type))
  (at level 0, A at level 99) : HB_scope.
Global Open Scope HB_scope.

(* Hacking the tc solver's instance compilation clause. *)
Elpi Accumulate tc.db lp:{{
% copy of the cs predicate in tc.db used to transfer clauses during export.
:index (0 6 6)
pred cs i:goal-ctx, i:term, i:term, o:term.

func w-holes.aux int, (list term -> prop -> prop), list term -> prop.
w-holes.aux 0 P L R :- !, P L R, !.
w-holes.aux N P L (pi x\ R x) :- pi x\ w-holes.aux {calc (N - 1)} P [x|L] (R x).

func w-holes int, (list term -> prop -> prop) -> prop.
w-holes N P R :- w-holes.aux N P [] R.

% [get-structure-coercion S1 S2 F] finds the coecion F from the structure S1 to S2
func get-structure-coercion structure, structure -> term.
get-structure-coercion S T (global F) :-
  coq.coercion.db-for (grefclass S) (grefclass T) L,
  if (L = [pr F _]) true (coq.error "No one step coercion from" S "to" T).

func get-projections inductive -> list (option term).
get-projections S Proj :-
  coq.env.projections S ProjC,
  std.map ProjC (c\ p\ sigma c' p' n\
    if (c = some c')
      (if (coq.env.primitive-projection? p' c' n) (p = some (primitive (proj p' n))) (p = some (global (const c'))))
    (p = none)) Proj.

func get-structure-sort-projection structure -> term.
get-structure-sort-projection (indt S) Proj :- !,
  get-projections S L,
  if (L = [some Proj, _]) true (coq.error "No canonical sort projection for" S).
get-structure-sort-projection S _ :- coq.error "get-structure-sort-projection: not a structure" S.

func get-structure-class-projection structure -> term.
get-structure-class-projection (indt S) T :- !,
  get-projections S L,
  if (L = [_, some T]) true (coq.error "No canonical class projection for" S).
get-structure-class-projection S _ :- coq.error "get-structure-class-projection: not a structure" S.

namespace hb {
  %FIXME: may be incorrect, two goals may be on the same evar but have their nablas in different orders. Is there a way to get the evar (unapplied) from the goal?
  func eq-sealed-goal sealed-goal, sealed-goal ->.
  eq-sealed-goal (nabla G) (nabla G2) :- !, pi x\ eq-sealed-goal (G x) (G2 x).
  eq-sealed-goal (nabla G) G2 :- !, pi x\ eq-sealed-goal (G x) G2.
  eq-sealed-goal G (nabla G2) :- !, pi x\ eq-sealed-goal G (G2 x).
  eq-sealed-goal (seal (goal _ _ _ E _)) (seal (goal _ _ _ E2 _)) :- E == E2.

  func mem-sealed-goal list sealed-goal, sealed-goal ->.
  mem-sealed-goal [X|_] Y :- eq-sealed-goal X Y, !.
  mem-sealed-goal [_|L] Y :- mem-sealed-goal L Y.

  func goal->concl sealed-goal -> term.
  goal->concl (nabla G) C :- pi x\ goal->concl (G x) C.
  goal->concl (seal (goal _ _ G _ _)) G.

  func goal-is-class sealed-goal ->.
  goal-is-class (nabla G) :- pi x\ goal-is-class (G x).
  goal-is-class (seal (goal _ _ G _ _)) :-
    not (var G),
    coq.safe-dest-app G GC _,
    not (var GC),
    GC = global C,
    not (var C),
    coq.TC.class? C, !.

  pred has-compiled.
  pred reducing.
  pred subgoal.

  func compile.mk-clause gref, term, list term, list term, list term, list term, term, prop, list term -> prop.
  compile.mk-clause Class ProofHd RHHyps RTHyps RevArgs HRArgs HA PA HLArgs Clause :-
    std.map [RHHyps, RTHyps, RevArgs] std.rev [HHyps, THyps, Args],
    coq.mk-app ProofHd HHyps Proof,
    coq.typecheck Proof _ ok, %This instantiates the parameters, if applicable
    tc.gref->pred-name Class PredName,
    if (var HA) (HArgs = HRArgs, RArgs = Args)
      (std.append HLArgs [HA|HRArgs] HArgs, std.split-at {std.length HLArgs} Args LArgs [_|RArgs]),
    coq.elpi.predicate PredName {std.append HArgs [Proof]} C,
    if (HHyps = []) (Conds0 = []) (Conds0 = [std.forall2 HHyps THyps (x\ t\ coq.typecheck x t ok)]), !,
    (pi ginit gfinal\
      if (HArgs = []) (Conds1 ginit = [ginit = []|Conds0]) (
        Conds1 ginit = [
          sigma g gs\
            coq.ltac.collect-goals (app HArgs) g gs,
            std.append g gs ginit|Conds0]), !,
      if (HLArgs = []) (Conds2 ginit = Conds1 ginit) (
        Conds2 ginit = [std.forall2 LArgs HLArgs (h\ x\ coq.unify-eq h x ok)|Conds1 ginit]), !,
      if (var HA) (Conds3 ginit = Conds2 ginit)
        (Conds3 ginit = [PA|Conds2 ginit]), !,
      if (HRArgs = []) (Conds4 ginit = Conds3 ginit)
        (Conds4 ginit = [std.forall2 RArgs HRArgs (h\ x\ coq.unify-eq h x ok)|Conds3 ginit]), !,
      if (HArgs = []) (Conds5 ginit gfinal = Conds4 ginit) (
        std.append HArgs Args H0,
        std.append HHyps H0 H1,
        Conds5 ginit gfinal = [
          ((sigma g gs\
            coq.ltac.collect-goals (app H1) g gs,
            std.append g gs gfinal),
            [(reducing :- !, fail), subgoal] => std.forall gfinal (g\
            mem-sealed-goal ginit g;
            not (goal-is-class g);
            coq.ltac.open (coq.ltac.call-ltac1 "done_tc") g []
            ))|Conds4 ginit]), !,
      std.rev (Conds5 ginit gfinal : list prop) (Conds6 ginit gfinal)),
    Clause = (pi ginit gfinal\ C :- Conds6 ginit gfinal).

% [compile.largs Args PredName ProofHd HHyps THyps As HRArgs HA HLArgs Clause] abstracts over the arguments of the class
  % we are providing an instance for, from what to left, stopping at the last argument which contains a pattern (e.g. not a local variable).
  func compile.largs list term, gref, term, list term, list term, list term, list term, term, prop, list term -> prop.
  compile.largs [A|Args] Class ProofHd HHyps THyps As HRArgs HA PA HLArgs (pi p\ Clause p) :-
    coq.typecheck A T ok,
    (@pi-decl _ T p\ compile.largs Args Class ProofHd HHyps THyps As HRArgs HA PA [p|HLArgs] (Clause p)).
    
  compile.largs [] Class ProofHd HHyps THyps RArgs HRArgs HA PA HLArgs Clause :-
    compile.mk-clause Class ProofHd HHyps THyps RArgs HRArgs HA PA HLArgs Clause.

  % [compile.subject T T'] extracts the pattern [T'] out of [T]. It replaces every subterm of [T] which is not
  % part of the pattern by a fresh hole. The holes are abstracted using pis and the output term [X] is hidden as
  % a prop using [T' = compile.subject.hide X P], with [P] the clause that need to be inserted in the final output
  % when unifying the subject.

  func compile.subject term, list term, gref, term, list term, list term, list term, list term -> prop.
  compile.subject (prod N T X) Args Class ProofHd HHyps THyps As HRArgs (pi t x\ Clause t x) :- !,
    pi t x\ compile.largs Args Class ProofHd HHyps THyps As HRArgs (prod N t x) (coq.unify-eq T t ok, @pi-decl N T y\ coq.unify-eq (X y) (x y) ok) [] (Clause t x).
  %TODO: This is not precise enough, but I do not know how to abstract under a binder.
  compile.subject (fun N T X) Args Class ProofHd HHyps THyps As HRArgs (pi t x\ Clause t x) :- !,
    pi t x\ compile.largs Args Class ProofHd HHyps THyps As HRArgs (fun N t x) (coq.unify-eq T t ok, @pi-decl N T t\ coq.unify-eq (X t) (x t) ok) [] (Clause t x).
  compile.subject (sort U) Args Class ProofHd HHyps THyps As HRArgs Clause :- !,
    compile.largs Args Class ProofHd HHyps THyps As HRArgs (sort U) true [] Clause.
  compile.subject S Args Class ProofHd HHyps THyps As HRArgs Clause :-
    coq.safe-dest-app S K SArgs,
    (K = global _; K = pglobal _ _; K = primitive _), !,
    if (SArgs = []) (compile.largs Args Class ProofHd HHyps THyps As HRArgs K true [] Clause) (
      Clause = (pi x\ C x),
      pi x\ compile.largs Args Class ProofHd HHyps THyps As HRArgs (app [K|x]) (std.forall2 SArgs x (x\y\ coq.unify-eq x y ok)) [] (C x)).
  
  % [compile.rargs Args PredName ProofHd HHyps THyps As HArgs Clause] abstracts over the arguments of the class
  % we are providing an instance for, from right to left, stopping at the rightmost argument which contains a pattern (e.g. not a local variable).
  pred compile.rargs i:list term, i:gref, i:term, i:list term, i:list term, i:list term, i:list term, o:prop.
  compile.rargs [A|Args] Class ProofHd HHyps THyps As HRArgs Clause :-
    (@redflags! coq.redflags.betaiotazeta => coq.reduction.lazy.whd A A0),
    compile.subject A0 Args Class ProofHd HHyps THyps As HRArgs Clause.

  compile.rargs [A|Args] Class ProofHd HHyps THyps As HArgs (pi p\ Clause p) :-
    coq.typecheck A T ok,
    (@pi-decl _ T p\ compile.rargs Args Class ProofHd HHyps THyps As [p|HArgs] (Clause p)).
    
  compile.rargs [] Class ProofHd HHyps THyps RArgs HArgs Clause :-
    compile.mk-clause Class ProofHd HHyps THyps RArgs HArgs _ _ [] Clause.

  func reduce term -> term.
  reduce T R :-
    not (var T),
		coq.reduction.whd-betaiota-deltazeta-for-iota-state T U,
    if (T = U)
      (coq.safe-dest-app U Hd Args,
        not (var Hd),
        if (Hd = global (const HdG)) (coq.env.const-body HdG (some Hd'))
          (Hd = primitive (proj P N),
          coq.primitive.projection-unfolded P PU,
          Hd' = primitive (proj PU N)),
        coq.mk-app Hd' Args V,
        coq.reduction.whd-betaiota-deltazeta-for-iota-state V R,
        not (R = T))
      (R = U).

  % Reduction loop, we reduce arguments of the typeclass from right to left.
  % We do not allow reduction in recursive calls, as they would not know which argument to reduce next or how to refold reduced arguments.
  func reduce-loop string, list term, term, term, list term ->.
  reduce-loop PredName LArgs Ainit A RArgs :-
    not reducing,
    if (reduce A A0)
      (if (coq.elpi.predicate PredName {std.append LArgs [A0|RArgs]} G, reducing => G) true
        (reduce-loop PredName LArgs Ainit A0 RArgs))
      (std.rev LArgs [A1|RLArgs],
        std.rev RLArgs LArgs0,
        reduce-loop PredName LArgs0 A1 A1 [Ainit|RArgs]).
    

  func compile.try-join gref, list term, list term -> prop, prop, prop.
  compile.try-join (indt TC) [S|RParams] [X|RParams] (pi x y\ UClause x y) (pi x y\ JClause x y) (pi x y\ Clause x y) :-
    %Check that the current clause being built is the identity clause (T.axioms_ (T.sort _)).
    std.rev RParams Params,
    coq.safe-dest-app S TSPC SArgs,
    if (TSPC = primitive (proj P _))
      (coq.projection->gref P (const PC),
        SArgs = [X],
        coq.typecheck X XTy ok,
        coq.safe-dest-app XTy _ Params)
      (TSPC = global (const PC),
        std.rev SArgs [X|RParams]),
    coq.env.projection-record? PC TStruct,
    class-def (class (indt TC) (indt TStruct) _), !,

    tc.gref->pred-name (indt TC) PredName,
    get-structure-class-projection (indt TStruct) TCPC,
    if (TCPC = primitive _) (TCP = TCPC)
      (coq.mk-app TCPC Params TCP),

    (pi x y\ sigma args c\
			std.append Params [app [TSPC|x], y] args,
			coq.elpi.predicate PredName args c,
      if (TSPC = primitive _)
        (Clause x y = (pi params s sty tc\ c :-
          % If we are in a subgoal, we HAVE TO succeed since no one will catch a failure. This may cause the below mentioned loop to trigger once, but on its next run we will not be in a subgoal.
          % If we are not in a subgoal and are reducing, we MUST NOT succeed, otherwise typechecking will unify the
          % `S.axioms_ t` with `S.axioms_ (S.sort s)` with `S.axioms_ t` the initial goal and
          % `S.axioms_ (S.sort s)` the current goal, leading to an infinite loop.
          (subgoal; not reducing),
          x = [s],
          coq.typecheck s sty ok,
          coq.safe-dest-app sty tc params,
          std.forall2 params Params (h\ x\ coq.unify-eq h x ok),
          y = app [TCPC|x]))
        (Clause x y = (pi rparams params s\ c :-
          (subgoal; not reducing),
          std.rev x [s|rparams],
          std.rev rparams params,
          std.forall2 params Params (h\ x\ coq.unify-eq h x ok),
          y = app [TCPC|x]))), !,
    % Build unfolding and join clauses
    pi x y\ sigma args c\
			std.append Params [x, y] args,
			coq.elpi.predicate PredName args c,
      UClause x y = (c :- !, reduce-loop PredName Params x x [y]),
      JClause x y =
        (pi kargs k p pc pn s m sc jc subject revkparams kparams coe revkparams kparams\ c :-
          (subgoal; not reducing),
          %Check that the subject is a projection...
          coq.safe-dest-app x k kargs,
          not (var k),
          if (k = primitive (proj p pn)) (coq.projection->gref p (const pc)) (k = global (const pc)),
          %... of class sc ...
          coq.env.projection-record? pc s,
          class-def (class (indt sc) (indt s) m),

          %Extract the subject of the projection
          std.rev kargs [subject|revkparams],

          %Computing join
          join (indt TC) (indt sc) (indt jc),

          %If we are projecting
          if (jc = sc)
            %We get the projection
            (get-structure-coercion (indt s) (indt TStruct) coe,
            %We compute the parameters
            sigma paramsS paramsSx x\
              if (k = primitive (proj p pn))
                (sigma ty v\
                  coq.typecheck subject ty ok,
                  coq.safe-dest-app ty v paramsS)
                (std.rev revkparams paramsS),
              %We coerce the subject
              std.append paramsS [subject] paramsSx,
              coq.mk-app coe paramsSx x,
              %And we extract the class
              coq.mk-app TCP [x] y)
            %If we have a real join, we introduce a fresh term x0
            (sigma js x0 n n' v0 v1 v2 v3 v4 h hx x' jm coet\
              %We prepare the arguments of the coercions
              coq.env.indt jc v0 n v1 v2 v3 v4,
              calc (n - 1) n',
              coq.mk-n-holes n' h,
              std.append h [x0] hx,
              %We check that the subject is a coercion of x0
              class-def (class (indt jc) js jm),
              get-structure-coercion js (indt s) coet,
              coq.mk-app coet hx subject,
              %We coerce x0
              if (jc = TC) (x' = x0)
                (get-structure-coercion js (indt TStruct) coe,
                coq.mk-app coe hx x'),
              %And we extract the class
              coq.mk-app TCP [x'] y)).


  % [compile.telescope Ty ProofHd HHyps THyps Clause UClause JClause] creates fresh variables for every hypothesis of [ProofHd] (as given in
  % its type [Ty]) and abstracts over them in the output clause [Clause] (and [UClause] and [JClause] if they are also produced).
  func compile.telescope term, term, list term, list term -> prop, prop, prop.
  compile.telescope (prod N T B) ProofHd HHyps THyps (pi x\ Clause x) UClause JClause :-
    (@pi-decl N T x\ compile.telescope (B x) ProofHd [x|HHyps] [T|THyps] (Clause x) (UClause' x) (JClause' x)),
    if (pi x\ var (UClause' x)) true ((UClause = pi x\ UClause' x), (JClause = pi x\ JClause' x)).

  compile.telescope (app [(global Class)|Args]) ProofHd HHyps THyps Clause UClause JClause :- !,
    coq.TC.class? Class,
    std.rev Args RArgs,
    (compile.try-join Class RArgs HHyps UClause JClause Clause;
      compile.rargs RArgs Class ProofHd HHyps THyps RArgs [] Clause), !.

% TOTHINK: Can I return only one clause?
%  func compile.is-id-instance.telescope term, list term ->.
%  compile.is-id-instance.telescope (prod N T B) Tele :-
%    @pi-decl N T x\ compile.is-id-instance.telescope (B x) [x|Tele].
%
%  compile.is-id-instance.telescope T [X|Tele] :-
%    coq.safe-dest-app T TC TArgs,
%    std.rev TArgs [S|Tele],
%    coq.safe-dest-app S K SArgs,
%    if (K = primitive (proj P _))
%      (coq.projection->gref P (const PC),
%        SArgs = [X],
%        coq.typecheck X XTy ok,
%        coq.safe-dest-app XTy _ XParams,
%        std.rev XParams Tele)
%      (K = global (const PC),
%        std.rev SArgs [X|Tele]),
%    coq.env.projection-record? PC TStruct,
%    class-def (class (indt TC) (indt TStruct) _).
%    
%  func compile.is-id-instance term ->.
%  compile.is-id-instance Ty :-
%    compile.is-id-instance.telescope Ty [].
  

  % [compile Ty ProofHd Clause UClause JClause] compiles the instance [ProofHd] of type [Ty], producing the clause [Clause].
  % If [ProofHd] is the instance of a class on the associated structure's sort projection, it also produces the
  % unfolding clause [UClause] and the join clause [JClause].
  func compile term, term -> prop, prop, prop.
  compile Ty ProofHd Clause UClause JClause :- !,
    %if (compile.is-id-instance Ty) (
    %  
    %) true,
    compile.telescope Ty ProofHd [] [] Clause UClause JClause.

  func compile.instance-gr gref -> prop, prop, prop.
  % If the instance is polymorphic, we wrap its gref into the pglobal constructor
  compile.instance-gr InstGR (pi x\ Clause x) UClause JClause :- coq.env.univpoly? InstGR _, !,
    coq.env.typeof InstGR Ty,
    (pi x\ compile Ty (pglobal InstGR x) (Clause x) (UClause' x) (JClause' x)),
    if (pi x\ var (UClause' x)) true ((UClause = pi x\ UClause' x), (JClause = pi x\ JClause' x)).
  compile.instance-gr InstGR Clause UClause JClause :- !,
    coq.env.typeof InstGR Ty,
    compile Ty (global InstGR) Clause UClause JClause.
}

func tc.gref->pred-name gref -> string.
namespace tc {
  func lettify.main term -> term.
  func add-tc-db id, grafting, prop ->.
  func get-full-path gref -> string.
  namespace compile {
    func instance term, term -> prop.
    instance Ty ProofHd Clause :-
      hb.compile Ty ProofHd Clause _ _, !.
  }

  func add-inst.aux gref, gref, list prop, grafting ->.
  add-inst.aux Inst TC Locality Grafting :-
    coq.env.current-section-path SectionPath,
    hb.compile.instance-gr Inst Clause UClause JClause, 
    tc.get-full-path Inst _ClauseName, !,
    (Locality => (
      if (var UClause) true (
        tc.add-tc-db _ (after {calc (int_to_string 100)}) UClause,
        tc.add-tc-db _ (after {calc (int_to_string 100)}) JClause),
      tc.add-tc-db _ Grafting Clause, 
      tc.add-tc-db _ Grafting (tc.instance SectionPath Inst TC Locality))).
  add-inst.aux Inst _ _ _ :- !,!,
    (@global! => tc.add-tc-db _ _ (tc.banned Inst)),
    coq.error "Not-added" "TC_solver" "[TC] Not yet able to compile" Inst "...".

}

% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% This data represents the hierarchy and some other piece of state to
%    implement the commands of this file

typeabbrev mixinname   gref.
typeabbrev classname   gref.
typeabbrev factoryname gref.
typeabbrev structure   gref.

typeabbrev (w-args A) (triple A (list term) term).

kind w-params type -> type.
type w-params.cons id -> term -> (term -> w-params A) -> w-params A.
type w-params.nil id -> term -> (term -> A) -> w-params A.

typeabbrev (list-w-params A) (w-params (list (w-args A))).
typeabbrev (one-w-params A) (w-params (w-args A)).
typeabbrev mixins (list-w-params mixinname).
typeabbrev factories (list-w-params mixinname).
typeabbrev (w-mixins A) (pair mixins (w-params A)).

%%%%% Classes %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% (class C S ML) represents a class C packed in S containing mixins ML.
% Example:
%
%  HB.mixin Record IsZmodule V := { ... }
%  HB.mixin Record Zmodule_IsLmodule (R : ringType) V of Zmodule V := { ... }
%  HB.structure Definition Lmodule R := {M of Zmodule M & Zmodule_IsLmodule R M}
%
% The class description for Lmodule would be:
%
%  class (indt «Lmodule.axioms»)                   /* The record with all mixins     */
%        (indt «Lmodule.type»)                     /* The record with sort and class */
%        (w-params.cons "R" {{ Ring.type }} P \    /* The first parameter, named "R" */
%          w-params.nil "M" {{ Type }} T \         /* The key of the structure       */
%           [...,                                  /* deps of IsZmodule.mixin        */
%            triple (indt «IsZmodule.mixin») [] T, /* a mixins with its params       */
%            triple (indt «Zmodule_IsLmodule.mixin») [P] T ]) /* another mixins      */
%
% If some mixin parameters depend on other mixins (through a canonical instance that
% can be inferred from them). Since our structure does not account for dependencies
% between mixins (the list in the end is flat), we compensate by replacing canonical
% instances by calls to `S.Pack T {{lib:elpi.hole}}`, and extending the reconstruction
% mecanism of mixins to also reinfer these holes.

kind hbclass type.
type class classname -> structure -> mixins -> hbclass.

% class-def contains all the classes ever declared
:index (10)
pred class-def o:hbclass.

%%%%% Builders %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% [from FN MN F] invariant:
% "F : forall p1 .. pn T LMN, FN p1 .. pn T LMN1 -> MN c1 .. cm T LMN2" where
%  - LMN1 and LMN2 are sub lists of LMN
%  - c1 .. cm are terms built using p1 .. pn and T
% - [factory-requires FN LMN]
% [from _ M _] tests whether M is a declared mixin.
pred from o:factoryname, o:mixinname, o:term.

%%%%% Abbreviations %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% [phant-abbrev Cst AbbrevCst Abbrev]
% Stores phantom abbreviation Abbrev associated with Cst
% AbbrevCst is the constant that serves as support
% e.g. Definition AbbrevCst := fun t1 t2 (phant_id t1 t2) => Cst t2.
%      Notation   Abbrev t1 := (AbbrevCst t1 _ idfun).
pred phant-abbrev o:gref, o:gref, o:abbreviation.

% [factory-alias->gref X GR] when X is already a factory X = GR
% however, when X is a phantom abbreviated gref, we find the underlying
% factory gref GR associated to it.
func factory-alias->gref gref -> gref, diagnostic.
factory-alias->gref PhGR GR ok :- phant-abbrev GR PhGR _, !.
factory-alias->gref GR GR ok :- phant-abbrev GR _ _, !.
factory-alias->gref GR _ (error Msg) :- !,
  Msg is {coq.term->string (global GR)} ^
         " is not a factory or its library (" ^
        { std.string.concat "." {std.drop-last 1 {coq.gref->path GR} } } ^
        ") was not correctly imported".

%%%%% Cache of known facts %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% [factory->constructor F K] means K is a constructor for
% the factory F.
:index(2)
func factory->constructor factoryname -> gref.

% [factory->nparams F N] says that F has N parameters
:index(2)
func factory->nparams factoryname -> int.

% [is-structure GR] tests if GR is a known structure
pred is-structure o:gref.

% [is-factory GR] tests if GR is a known factory
pred is-factory o:gref.

% [sub-class C1 C2 Coercion12 NparamsCoercion] C1 is a sub-class of C2,
% see also sub-class? which computes it on the fly
:index (2 2 1)
pred sub-class o:classname, o:classname, o:constant, o:int.

% Sparser relation equivalent to [sub-class]
:index (2 2)
pred sub-class-edge o:classname, o:classname.


% [gref->deps GR MLwP] is a (pre computed) list of dependencies of a know global
% constant. The list is topologically sorted
:index(2)
func gref->deps gref -> mixins.

% [join C1 C2 C3] means that C3 is the join of C1 and C2 in the hierarchy lattice
:index (2 2 2)
pred join o:classname, o:classname, o:classname.

% Section local memory of names for mixins, so that we can reuse them
% and build terms with simpler conversion problems (less unfolding
% in order to discover two mixins are the same)
% @gares : is it really a func. Ideally I think so, bu we load mixin-mem via
% `Clauses =>` in infer-class. Should perform a dynamic check?
func mixin-mem term -> gref.

% [has-canonical-structure-on Pat Struct] means that we declared an instance
% of structure Struct on pattern Pat.
pred has-canonical-structure-on o:cs-pattern, o:structure.


% [has-canonical-structure-on Pat Struct] means that we declared an instance
% of structure Struct on pattern Pat.
pred has-canonical-structure-on o:cs-pattern, o:structure.


%%%%%% Memory of exported mixins (HB.structure) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Operations (named mixin fields) need to be exported exactly once,
% but the same mixin can be used in many structure, hence this memory
% to keep the invariant.
% Also we remember which is the first class/structure that includes
% a given mixin, assuming the invariant that this first class is also
% the minimal class that includes this mixin.
% [mixin->first-class M C] states that C is the first/minimal class
% that contains the mixin M
:index(2)
func mixin->first-class mixinname -> classname.

% memory of exported operations (TODO: document fiels)
pred exported-op o:mixinname, o:constant, o:constant.

% memory of factory sort coercion
pred factory-sort o:coercion.

% memory of canonical projections for a structure (X.sort, X.class, X.type)
pred structure-key o:constant, o:constant, o:structure.

%%%%%% Membership of mixins to a  class %%%%%%%%%%%%%%%%
% [mixin-class M C] means M belongs to C
:index (2 2)
pred mixin-class o:mixinname, o:classname.

%% database for HB.context %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% [mixin-src T M X] states that X can be used to reconstruct
% an instance of the mixin [M T …], directly or through a builder.
% Since HB.builders sections can declare canonical instances of
% mixins that do not yet form a structure, we cannot resort to
% Coq's CS database (which is just for structures).
pred mixin-src o:term, o:mixinname, o:term.

% [has-mixin-instance K M G] states that G is a reference to an instance
% of mixin M for subject K'
:index (2 2 3)
pred has-mixin-instance o:cs-pattern, o:mixinname, o:gref.

%% database for HB.builders %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% [builder N TheFactory TheMixin S] is used to
% remember that the user run [HB.instance S] hence [HB.end] has to
% synthesize builders from TheFactory to TheMixin mixins generated by S.
% N is a timestamp.
kind builder type.
type builder int -> factoryname -> mixinname -> gref -> builder.
pred builder-decl o:builder.

%% database for builder-local canonical instances %%%%%%%%%%%%%%%%%%%%%%%
pred local-canonical o:constant.

% To tell HB.end what we are doing
kind declaration type.
% TheType, TheFactory and it's name and the name of the module encloding all that
type builder-from term -> term -> factoryname -> id -> declaration.
type no-builder declaration.
pred current-mode o:declaration.

%% database for HB.export / HB.reexport %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% library, nice-name, object
pred module-to-export   o:string, o:id, o:modpath.
pred instance-to-export o:string, o:id, o:constant.
pred mixin-to-export o:string, o:id, o:constant.
pred abbrev-to-export   o:string, o:id, o:gref.
pred clause-to-export   o:string, o:string, o:prop.

%% database for HB.locate and HB.about %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pred decl-location o:gref, o:loc.

% [docstring Loc Doc] links a location in the source text and some doc
pred docstring o:loc, o:string.

}}.

(* This database is used by the parsing phase only *)
#[synterp] Elpi Db export.db lp:{{
  pred module-to-export   o:string, o:modpath.

}}.


(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** This is like Locate but tells you the file and line at which the constant
    or inductive was generated.
*)

#[arguments(raw)] Elpi Command HB.locate.
Elpi Accumulate Db tc.db.
(* Since it can become rather large, accumulating the DB is often by far the
   most expensive accumulation. It is then worth sharing its cache between
   the commands. To this end, we accumulate the DB first in each command to
   ensure the same dependencies and maximize cache hits. For instance, this
   can save a few (2 or 3) percents of total compilation time on MathComp. *)
Elpi Accumulate lp:{{

:name "start"
main [str S] :- !,
  if (decl-location {coq.locate S} Loc)
     (coq.say "HB: synthesized in file" Loc)
     (coq.say "HB" S "not synthesized by HB").

main _ :- coq.error "Usage: HB.locate <name>.".
}}.
Elpi Typecheck.
Elpi Export HB.locate.


(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** This is like About but understands HB generated stuff, namely
    - structures, eg Foo.type
    - classes, eg Foo
    - factories, eg Bar
    - factory constructors, eg Bar.Build
    - canonical projections, eg Foo.sort
    - canonical value, eg Z, prod, ...
*)

#[arguments(raw)] Elpi Command HB.about.
Elpi Accumulate Db tc.db.
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/compat_acc_clauses_all.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate File "HB/common/compat_add_secvar_all.elpi".
Elpi Accumulate File "HB/about.elpi".
Elpi Accumulate lp:{{

:name "start"
main [str S] :- !, with-attributes (with-logging (about.main S)).

main _ :- coq.error "Usage: HB.about <name>.".
}}.
Elpi Typecheck.
Elpi Export HB.about.


(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** [HB.howto (T) Foo.type d] prints possible sequences of factories
    to equip a type [T] with a structure [Foo.type], taking into account
    structures already instantiated on [T]. The search depth [d]
    is the maximum length of the sequences, 3 by default.
    The first argument [T] is optional, when ommited [Foo.type] is built
    from scratch.
    Finally, the first argument can be another structure [Bar.type],
    in which case [Foo.type] is built starting from [Bar.type].
*)

#[arguments(raw)] Elpi Command HB.howto.
Elpi Accumulate Db tc.db.
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/compat_acc_clauses_all.elpi".
Elpi Accumulate File "HB/common/compat_add_secvar_all.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate File "HB/about.elpi".
Elpi Accumulate File "HB/howto.elpi".
Elpi Accumulate lp:{{

:name "start"
main [trm T, str STgt] :- !,
  with-attributes (with-logging (howto.main-trm T STgt none)).
main [trm T, str STgt, int Depth] :- !,
  with-attributes (with-logging (howto.main-trm T STgt (some Depth))).
main [str T, str STgt] :- !,
  with-attributes (with-logging (howto.main-str T STgt none)).
main [str T, str STgt, int Depth] :- !,
  with-attributes (with-logging (howto.main-str T STgt (some Depth))).
main [str STgt] :- !,
  with-attributes (with-logging (howto.main-from [] STgt none)).
main [str STgt, int Depth] :- !,
  with-attributes (with-logging (howto.main-from [] STgt (some Depth))).

main _ :-
  coq.error
    "Usage: HB.howto [(<type>)|<structure>] <structure> [<search depth>].".
}}.
Elpi Typecheck.
Elpi Export HB.howto.


(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** This command prints the status of the hierarchy (Debug)

*)

#[arguments(raw)] Elpi Command HB.status.
Elpi Accumulate Db tc.db.
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/compat_acc_clauses_all.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate File "HB/common/compat_add_secvar_all.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/status.elpi".
Elpi Accumulate lp:{{

:name "start"
main [] :- !, status.print-hierarchy.

main _ :- coq.error "Usage: HB.status.".
}}.
Elpi Typecheck.
Elpi Export HB.status.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** This command prints the hierarchy to a dot file. You can use
[[
tred file.dot | xdot -
]]
    to visualize file.dot
*)

#[arguments(raw)] Elpi Command HB.graph.
Elpi Accumulate Db tc.db.
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/compat_acc_clauses_all.elpi".
Elpi Accumulate File "HB/common/compat_add_secvar_all.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate File "HB/graph.elpi".
Elpi Accumulate lp:{{

:name "start"
main [str File] :- with-attributes (with-logging (graph.to-file File)).
main _ :- coq.error "Usage: HB.graph <filename>.".

}}.
Elpi Typecheck.
Elpi Export HB.graph.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** [HB.mixin] declares a mixin

  Syntax to create a mixin [MixinName]
  with requirements [Factory1] .. [FactoryN]:

[[
HB.mixin Record MixinName T & Factory1 T & … & FactoryN T := {
   op : T -> …
   …
   property : forall x : T, op …
   …
}
]]

  Synthesizes:
  - [MixinName T] abbreviation for the type of the (degenerate) factory
  - [MixinName.Build T] abbreviation for the constructor of the factory

  Note: [T & f1 T & … & fN T] is syntactic sugar for [T (_ : f1 T) … (_ : fN T)]

  Supported attributes:
  - [#[primitive]] experimental attribute to make the mixin/factory primitive,
  - [#[verbose]] for a verbose output.

*)

#[arguments(raw)] Elpi Command HB.mixin.
Elpi Accumulate Db tc.db.
Elpi Accumulate File tc_aux.
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/compat_acc_clauses_all.elpi".
Elpi Accumulate File "HB/common/compat_add_secvar_all.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate File "HB/common/synthesis.elpi".
Elpi Accumulate File "HB/common/phant-abbreviation.elpi".
Elpi Accumulate File "HB/instance.elpi".
Elpi Accumulate File "HB/context.elpi".
Elpi Accumulate File "HB/export.elpi".
Elpi Accumulate File "HB/factory.elpi".
Elpi Accumulate lp:{{

:name "start"
main [A] :- with-attributes (with-logging (factory.declare-mixin A)).

}}.
#[synterp] Elpi Accumulate File "HB/common/utils-synterp.elpi".
#[synterp] Elpi Accumulate Db export.db.
#[synterp] Elpi Accumulate lp:{{

shorten coq.env.{ begin-module, end-module, begin-section, end-section, export-module }.

pred actions i:id.
actions N :-
  begin-module N none,
    begin-section N,
    end-section,
    begin-module "Exports" none,
    end-module E,
  end-module _,
  export-module E,
  coq.env.current-library File,
  coq.elpi.accumulate current "export.db" (clause _ _ (module-to-export File E)).

main [indt-decl D] :- record-decl->id D N, with-attributes (actions N).

main _ :-
  coq.error "Usage: HB.mixin Record <MixinName> T & F A & … := { … }.".
}}.
Elpi Typecheck.
Elpi Export HB.mixin.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** [HB.pack] and [HB.pack_for] are tactic-in-term synthesizing a structure
    instance.

    In the middle of a term, in a context expecting a [Structure.type],
    you can write [HB.pack T F] to use factory [F] to equip type [T] with
    [Structure]. If [T] is already a rich type, eg [T : OtherStructure.type]
    or if [T] is a global constant with canonical structure instances attached
    to it, then this piece of info is used to infer a [Structure].

    If the context does not impose a [Structure.type] typing constraint, then
    you can use [HB.pack_for Structure.type T F].

    You can pass zero or more factories like [F] but they must all typecheck
    in the current context (the type is not enriched progressively).
    Structure instances are projected to their class in order to obtain a
    factory.

    Examples:

[[
    pose Fa : IsSomething T := IsSomething.Build T ...
    pose A : A.type := HB.pack T Fa.
    pose Fb : IsMore A := IsMore.Build ...
    pose B := HB.pack_for B.type T A Fb.
]]

    If [Structure.type] as parameters [P1..Pn] then you should use
    [HB.pack T F1..Fn] or
    [HB.pack_for (Structure.type P1..Pn) T F1..Fn]

*)

Elpi Tactic HB.pack_for.
Elpi Accumulate Db tc.db.
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/compat_acc_clauses_all.elpi".
Elpi Accumulate File "HB/common/compat_add_secvar_all.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate File "HB/common/synthesis.elpi".
Elpi Accumulate File "HB/pack.elpi".
Elpi Accumulate lp:{{

:name "start"
solve (goal _ _ S _ [trm Ty | Args] as G) GLS :- with-attributes (with-logging (std.do! [
  pack.main Ty Args InstanceSkel,
  std.assert-ok! (coq.elaborate-skeleton InstanceSkel S Instance) "HB.pack_for: the instance does not solve the goal",
  log.refine.no_check Instance G GLS,
])).

}}.
Elpi Typecheck.
Elpi Export HB.pack_for.

Elpi Tactic HB.pack.
Elpi Accumulate Db tc.db.
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/compat_acc_clauses_all.elpi".
Elpi Accumulate File "HB/common/compat_add_secvar_all.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate File "HB/common/synthesis.elpi".
Elpi Accumulate File "HB/pack.elpi".
Elpi Accumulate lp:{{

:name "start"
solve (goal _ _ Ty _ Args as G) GLS :- with-attributes (with-logging (std.do! [
  pack.main Ty Args InstanceSkel,
  std.assert-ok! (coq.elaborate-skeleton InstanceSkel Ty Instance) "HB.pack: the instance does not solve the goal",
  log.refine.no_check Instance G GLS,
])).

}}.
Elpi Typecheck.
Elpi Export HB.pack.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** [HB.structure] declares a packed structure.

  Syntax to declare a structure combing the axioms from [Factory1] … [FactoryN].
  The second syntax has a trailing [&] to pull in factory requirements silently.

[[
HB.structure Definition StructureName params :=
  { A of Factory1 … A & … & FactoryN … A }.
HB.structure Definition StructureName params :=
  { A of Factory1 … A & … & FactoryN … A & }.
]]

  Synthesizes:
  - [StructureName A] the type of the class that regroups all the factories
    [Factory1 … A] … [FactoryN … A].
  - [StructureName.type params] the structure type that packs together [A] and its class.
  - [StructureName.sort params] the first projection of the previous structure,
  - [StructureName.clone params T cT] a legacy repackaging function that eta expands
    the canonical [StructureName.type] of [T], using [cT] if provided.
  - [StructureName.class sT : StructureName sT] projects out the class of [sT : StructureName.type params],
  - [StructureName.copy T T' : StructureName T] returns the class of the canonical
    [StructureName.type] of [T], and gives it the type [Structure T]. It is thus
    ready to use in combination with HB.instance, as in
[[
  (* Cloning a structure from another one, given by the user *)
  HB.instance Definition _ := StructureName.copy T cT.
]]
  - [StructureName.on T : StructureName T] infers the class of the canonical
    [StructureName.type] of [T]. This is a shortcut for [StructureName.Copy T T],
    and it will succeeds if a reduction of [T] is canonically a [StructureName.type].

  Disclaimer: any function other that the ones described above, including pattern matching
    (using Gallina [match], [let] or tactics ([case], [elim], etc)) is an internal and must
    not be relied upon. Also hand-crafted [Canonical] declarations of such structures will
    break the hierarchy. Use [HB.instance] instead.

  Supported attributes:
  - [#[mathcomp]] attempts to generate a backward compatibility layer with mathcomp:
    trying to infer the right [StructureName.pack],
  - [#[arg_sort]] defines an alias [StructureName.arg_sort] for [StructureName.sort],
    and declares it as the main coercion. [StructureName.sort] is still declared as a coercion
    but the only reason is to make sure Coq does not print it.
    Cf #<a href="https://github.com/math-comp/math-comp/blob/17dd3091e7f809c1385b0c0be43d1f8de4fa6be0/mathcomp/fingroup/fingroup.v##L225-L243">#[fingroup.v]#</a>#.
  - [#[short(type="shortName")]] produces the abbreviation [shortName] for [Structure.type]
  - [#[short(pack="shortName")]] produces the abbreviation [shortName] for [HB.pack_for Structure.type]
  - [#[primitive]] experimental attribute to make the structure a primitive record,
  - [#[verbose]] for a verbose output.
*)

#[arguments(raw)] Elpi Command HB.structure.
Elpi Accumulate Db coercion.db.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db cs.db.
Elpi Accumulate File tc_aux.
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/compat_acc_clauses_all.elpi".
Elpi Accumulate File "HB/common/compat_add_secvar_all.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate File "HB/common/synthesis.elpi".
Elpi Accumulate File "HB/common/phant-abbreviation.elpi".
Elpi Accumulate File "HB/export.elpi".
Elpi Accumulate File "HB/instance.elpi".
Elpi Accumulate File "HB/context.elpi".
Elpi Accumulate File "HB/factory.elpi".
Elpi Accumulate File "HB/structure.elpi".
Elpi Accumulate lp:{{

:name "start"
main [const-decl N (some B) Arity] :- std.do! [
  % compute the universe for the structure (default )
  prod-last {coq.arity->term Arity} Ty,
  if (ground_term Ty) (Sort = Ty) (Sort = {{Type}}), sort Univ = Sort,
  with-attributes (with-logging (structure.declare N B Univ)),
].

}}.
#[synterp] Elpi Accumulate File "HB/common/utils-synterp.elpi".
#[synterp] Elpi Accumulate Db export.db.
#[synterp] Elpi Accumulate lp:{{

shorten coq.env.{ begin-module, end-module, begin-section, end-section, import-module, export-module }.

pred actions i:id.
actions N :-
  begin-module N none,
    begin-module "Exports" none,
    end-module E,
    import-module E,
  end-module _,
  export-module E,
  begin-module {calc (N ^ "ElpiOperations")} none,
  end-module O,
  export-module O,
  coq.env.current-library File,
  coq.elpi.accumulate current "export.db" (clause _ _ (module-to-export File E)),
  coq.elpi.accumulate current "export.db" (clause _ _ (module-to-export File O)),
  if (get-option "mathcomp" tt ; get-option "mathcomp.axiom" _) (actions-compat N) true.

pred actions-compat i:id.
actions-compat ModuleName :-
  CompatModuleName is "MathCompCompat" ^ ModuleName,
  begin-module CompatModuleName none,
    begin-module ModuleName none,
    end-module _,
  end-module O,
  export-module O,
  % is this a bug?
  % coq.env.current-library File,
  % coq.elpi.accumulate current "export.db" (clause _ _ (module-to-export File O)).
  true.

main [const-decl N _ _] :- !, with-attributes (actions N).

main _ :- coq.error "Usage: HB.structure Definition <ModuleName> := { A of <Factory1> A & … & <FactoryN> A }".
}}.
Elpi Typecheck.
Elpi Export HB.structure.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(* [HB.saturate [key]] saturates all instances (of all known keys, if key is not
   given) w.r.t. the current hierarchy.

   When two (unrelated) files are imported it might be that the instances
   declared in one file are sufficient to instantiate structures declared
   in the other file.

   This command reconsiders all types with a canonical structure instance
   and see if the they are also equipped with new ones.
*)

#[arguments(raw)] Elpi Command HB.saturate.
Elpi Accumulate Db tc.db.
Elpi Accumulate File tc_aux.
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/compat_acc_clauses_all.elpi".
Elpi Accumulate File "HB/common/compat_add_secvar_all.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate File "HB/common/synthesis.elpi".
Elpi Accumulate File "HB/common/phant-abbreviation.elpi".
Elpi Accumulate File "HB/export.elpi".
Elpi Accumulate File "HB/instance.elpi".
Elpi Accumulate File "HB/context.elpi".
Elpi Accumulate File "HB/factory.elpi".
Elpi Accumulate lp:{{
main [] :- !, with-attributes (with-logging (instance.saturate-instances _)).
main [str "Type"] :- !, with-attributes (with-logging (instance.saturate-instances (cs-sort _))).
main [str K] :- !, coq.locate K GR, with-attributes (with-logging (instance.saturate-instances (cs-gref GR))).
main [trm T] :- !, term->cs-pattern T P, with-attributes (with-logging (instance.saturate-instances P)).
main _ :- coq.error "Usage: HB.saturate [key]".
}}.
Elpi Typecheck.
Elpi Export HB.saturate.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** [HB.instance] associates to a type all the structures that can be
    obtained from the provided factory inhabitant.

    Syntax for declaring a canonical instance:

[[
HB.instance Definition N Params := Factory.Build Params T …
]]

    Supported attributes:
    - [#[export]] to flag the instance so that it is redeclared by [#[HB.reexport]]
    - [#[local]] to indicate that the instance should not survive the section.
    - [#[non_forgetful_inheritance]] allows non forgetful inheritance, i.e.
      inheritance via an instance declaration rather than via dependencies.
      See tests/non_forgetful_inheritance.v and
      "Competing inheritance paths in dependent type theory"
      (https://hal.inria.fr/hal-02463336)
    - [#[verbose]] for a verbose output.
    - [#[hnf] to compute the head normal form of CS instances before declaring
      them
*)

#[arguments(raw)] Elpi Command HB.instance.
Elpi Accumulate Db tc.db.
Elpi Accumulate File tc_aux.
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/compat_acc_clauses_all.elpi".
Elpi Accumulate File "HB/common/compat_add_secvar_all.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate File "HB/common/synthesis.elpi".
Elpi Accumulate File "HB/context.elpi".
Elpi Accumulate File "HB/instance.elpi".
Elpi Accumulate lp:{{

:name "start"
main [const-decl Name (some BodySkel) TyWPSkel] :- !,
  P = with-attributes (with-logging (instance.declare-const Name BodySkel TyWPSkel _ _)),
  if (current-mode (builder-from _ _ _ _)) (get-option "local" tt => P) (P).
main [T0, F0] :- !,
  coq.warning "HB" "HB.deprecated" "The syntax \"HB.instance Key FactoryInstance\" is deprecated, use \"HB.instance Definition\" instead",
  P = with-attributes (with-logging (instance.declare-existing T0 F0)),
  if (current-mode (builder-from _ _ _ _)) (get-option "local" tt => P) (P).

}}.
#[synterp] Elpi Accumulate lp:{{

shorten coq.env.{ begin-section, end-section }.

main [const-decl _ _ (arity _)] :- !.
main [const-decl _ _ (parameter _ _ _ _)] :- !,
  SectionName is "hb_instance_" ^ {std.any->string {new_int} },
  begin-section SectionName, end-section.
main [_, _] :- !.

main _ :- coq.error "Usage: HB.instance Definition <Name> := <Builder> T ...".
}}.
Elpi Typecheck.
Elpi Export HB.instance.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** [HB.factory] declares a factory. It has the same syntax of [HB.mixin] *)

#[arguments(raw)] Elpi Command HB.factory.
Elpi Accumulate Db tc.db.
Elpi Accumulate File tc_aux.
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/compat_acc_clauses_all.elpi".
Elpi Accumulate File "HB/common/compat_add_secvar_all.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate File "HB/common/synthesis.elpi".
Elpi Accumulate File "HB/common/phant-abbreviation.elpi".
Elpi Accumulate File "HB/instance.elpi".
Elpi Accumulate File "HB/context.elpi".
Elpi Accumulate File "HB/export.elpi".
Elpi Accumulate File "HB/factory.elpi".
Elpi Accumulate lp:{{

:name "start"
main [A] :- with-attributes (with-logging (factory.declare A)).

}}.
#[synterp] Elpi Accumulate File "HB/common/utils-synterp.elpi".
#[synterp] Elpi Accumulate Db export.db.
#[synterp] Elpi Accumulate lp:{{

shorten coq.env.{ begin-module, end-module, begin-section, end-section, export-module }.

pred actions i:id.
actions N :-
  begin-module N none,
    begin-section N,
    end-section,
    begin-module "Exports" none,
    end-module E,
  end-module _,
  export-module E,
  coq.env.current-library File,
  coq.elpi.accumulate current "export.db" (clause _ _ (module-to-export File E)).

main [indt-decl D] :- record-decl->id D N, with-attributes (actions N).
main [const-decl N _ _] :- with-attributes (actions N).

main _ :-
  coq.error "Usage: HB.factory Record <FactoryName> T & F A & … := { … }.\nUsage: HB.factory Definition <FactoryName> T of F A := t.".
}}.
Elpi Typecheck.
Elpi Export HB.factory.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** [HB.builders] starts a section to declare the builders associated
    to a factory. [HB.end] ends that section.

    Syntax to declare builders for factory [Factory]:

[[
HB.builders Context A (f : Factory A).
…
HB.instance A someFactoryInstance.
…
HB.end.
]]

    [HB.builders] starts a section (inside a module of unspecified name) where:
    - [A] is a type variable
    - all the requirements of [Factory] were postulated as variables
    - [f] is variable of type [Factory A]
    - all classes whose requirements can be obtained from [Factory] are
      declared canonical on [A]
    - for each operation [op] and property [prop] (named fields) of
      [Factory A] a [Notation] named [op] and [property]
      for the partial application of [op] and [property] to the variable [f]
      The former [op] and [property] are aliased [Super.op] and [Super.property]

    [HB.end] ends the section and closes the module and synthesizes
    - for each structure inhabited via [HB.instance] it defined all
      builders to known mixins

    Supported attributes:
    - [#[verbose]] for a verbose output.
*)

#[arguments(raw)] Elpi Command HB.builders.
Elpi Accumulate Db tc.db.
Elpi Accumulate File tc_aux.
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/compat_acc_clauses_all.elpi".
Elpi Accumulate File "HB/common/compat_add_secvar_all.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate File "HB/common/synthesis.elpi".
Elpi Accumulate File "HB/common/phant-abbreviation.elpi".
Elpi Accumulate File "HB/instance.elpi".
Elpi Accumulate File "HB/context.elpi".
Elpi Accumulate File "HB/export.elpi".
Elpi Accumulate File "HB/factory.elpi".
Elpi Accumulate File "HB/builders.elpi".
Elpi Accumulate lp:{{

:name "start"
main [ctx-decl C] :- with-attributes (with-logging (builders.begin C)).

}}.
#[synterp] Elpi Accumulate File "HB/common/utils-synterp.elpi".
#[synterp] Elpi Accumulate lp:{{

shorten coq.env.{ begin-module, end-module, begin-section }.

pred actions i:id.
actions N :-
  begin-module N none,
    begin-module "Super" none,
    end-module _,
    begin-section N.

main [ctx-decl _] :- !, with-attributes (actions {calc ("Builders_" ^ {std.any->string {new_int} })}).

main _ :- coq.error "Usage: HB.builders Context A (f : F1 A).".
}}.
Elpi Typecheck.
Elpi Export HB.builders.


#[arguments(raw)] Elpi Command HB.end.
Elpi Accumulate Db tc.db.
Elpi Accumulate File tc_aux.
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/compat_acc_clauses_all.elpi".
Elpi Accumulate File "HB/common/compat_add_secvar_all.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate File "HB/common/synthesis.elpi".
Elpi Accumulate File "HB/instance.elpi".
Elpi Accumulate File "HB/context.elpi".
Elpi Accumulate File "HB/export.elpi".
Elpi Accumulate File "HB/builders.elpi".
Elpi Accumulate lp:{{

:name "start"
main [] :- with-attributes (with-logging builders.end).

}}.
#[synterp] Elpi Accumulate File "HB/common/utils-synterp.elpi".
#[synterp] Elpi Accumulate Db export.db.
#[synterp] Elpi Accumulate lp:{{

shorten coq.env.{ end-module, end-section, begin-module, end-module, export-module }.

pred actions.
actions :-
    end-section,
    begin-module {calc ("Builders_Export_" ^ {std.any->string {new_int} })} none,
    end-module M,
  end-module _,
  export-module M,
  coq.env.current-library File,
  coq.elpi.accumulate current "export.db" (clause _ _ (module-to-export File M)).

main [] :- !, with-attributes actions.
main _ :- coq.error "Usage: HB.end.".

}}.
Elpi Typecheck.
Elpi Export HB.end.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** [HB.export Modname] does the work of [Export Modname] but also schedules [Modname]
   to be exported later on, when [HB.reexport] is called.
   [HB.export Constname] does nothing, but schedules [Constname] to be made
   available via a Notation at HB.reexport time.

   Note that the list of things to be exported is stored in the current module,
   hence the recommended way to do is
[[
Module Algebra.
  HB.mixin .... HB.structure ...
  Module MoreExports. ... End MoreExports. HB.export MoreExports.
  ...
  HB.builders ...
  Lemma aux_fact : ....
  HB.export aux_fact.
  ...
  HB.end.
  ...
  Module Export. HB.reexport. End Exports.
End Algebra.
Export Algebra.Exports.
]]

    Supported attributes:
    - [#[verbose]] for a verbose output.

*)

#[arguments(raw)] Elpi Command HB.export.
Elpi Accumulate Db tc.db.
Elpi Accumulate File tc_aux.
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/compat_acc_clauses_all.elpi".
Elpi Accumulate File "HB/common/compat_add_secvar_all.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate File "HB/export.elpi".
Elpi Accumulate lp:{{

:name "start"
main [str M] :- !, with-attributes (with-logging (export.any M)).
main _ :- coq.error "Usage: HB.export M.".

}}.
#[synterp] Elpi Accumulate File "HB/common/utils-synterp.elpi".
#[synterp] Elpi Accumulate Db export.db.
#[synterp] Elpi Accumulate lp:{{

shorten coq.env.{ export-module }.

pred actions i:list located.
actions [loc-modpath MP] :- !,
  export-module MP,
  coq.env.current-library File,
  coq.elpi.accumulate current "export.db" (clause _ _ (module-to-export File MP)).
actions [].

main [str M] :- !, with-attributes (actions {coq.locate-all M}).
main _ :- coq.error "Usage: HB.export M.".

}}.
Elpi Typecheck.
Elpi Export HB.export.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** [HB.reexport] Exports all modules, canonical instances and constants that
   were previously exported via [HB.export].
   It is useful to create one big module with all exports at the end of a file.
   It optionally takes the name of a module or a component of the current module path
   (a module which is not closed yet) *)

#[arguments(raw)] Elpi Command HB.reexport.
Elpi Accumulate Db tc.db.
Elpi Accumulate File tc_aux.
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/compat_acc_clauses_all.elpi".
Elpi Accumulate File "HB/common/compat_add_secvar_all.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate File "HB/export.elpi".
Elpi Accumulate lp:{{

:name "start"
main [] :- !, with-attributes (with-logging (export.reexport-all-modules-and-CS none)).
main [str M] :- !, with-attributes (with-logging (export.reexport-all-modules-and-CS (some M))).
main _ :- coq.error "Usage: HB.reexport.".

}}.
#[synterp] Elpi Accumulate File "HB/common/utils-synterp.elpi".
#[synterp] Elpi Accumulate Db export.db.
#[synterp] Elpi Accumulate lp:{{

shorten coq.env.{ export-module }.

pred module-in-module i:list string, i:prop.
module-in-module PM (module-to-export _ M) :-
  coq.modpath->path M PC,
  std.appendR PM _ PC. % sublist

pred actions i:option id.
actions Filter :-
  coq.env.current-library File,
  compute-filter Filter MFilter,
  std.findall (module-to-export File Module_) ModsCL,
  std.filter {list-uniq ModsCL} (module-in-module MFilter) ModsCLFiltered,
  std.forall ModsCLFiltered (x\sigma mp\x = module-to-export _ mp, export-module mp).

main [] :- !, with-attributes (actions none).
main [str M] :- !, with-attributes (actions (some M)).
main _ :- coq.error "Usage: HB.reexport.".

}}.
Elpi Typecheck.
Elpi Export HB.reexport.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

From elpi.apps Require Import locker.

Elpi Export mlock As HB.lock.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(*
Inactive command: [HB.declare]
This command populates the current section with canonical instances.

  Syntax:
[[
HB.declare Context (p1 : P1) ... (pn : Pn) (t : T) & F0 & ... & Fk.
]]
  Effect:
[[
Variables (p1 : P1) ... (pn : Pn) (t : T).

Variable m0 : M0 ... T.
HB.instance Definition _ : M0 ... T := m0.
..
Variable mk : Ml ... T.
HB.instance Definition _ : Ml ... T := ml.
]]

  where:
  - factories F0 .. Fk produce mixins M0 .. Ml.

  Supported attributes:
  - [#[verbose]] for a verbose output.

*)

#[arguments(raw)] Elpi Command HB.declare.
Elpi Accumulate Db tc.db.
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/compat_acc_clauses_all.elpi".
Elpi Accumulate File "HB/common/compat_add_secvar_all.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate File "HB/common/synthesis.elpi".
Elpi Accumulate File "HB/common/phant-abbreviation.elpi".
Elpi Accumulate File "HB/export.elpi".
Elpi Accumulate File "HB/instance.elpi".
Elpi Accumulate File "HB/context.elpi".
Elpi Accumulate File "HB/factory.elpi".
Elpi Accumulate lp:{{

:name "start"
main [Ctx] :- Ctx = ctx-decl _, !,
  with-attributes (with-logging (
    factory.argument->w-mixins Ctx (pr FLwP _),
    context.declare FLwP _ _ _ _ _)).

main _ :- coq.error "Usage: HB.declare Context <Parameters> <Key> <Factories>".

}}.
Elpi Typecheck.
Elpi Export HB.declare.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** [HB.check T] acts like [Check T] but supports the attribute [#[skip="rex"]]
    that skips the action on Coq version matches rex. It also understands the
    [#[fail]] attribute. *)

#[arguments(raw)] Elpi Command HB.check.
Elpi Accumulate Db tc.db.
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/compat_acc_clauses_all.elpi".
Elpi Accumulate File "HB/common/compat_add_secvar_all.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate lp:{{

:name "start"
main [trm Skel] :- !, with-attributes (with-logging (check-or-not Skel)).
main _ :- coq.error "usage: HB.check (term).".

pred check-or-not i:term.
check-or-not Skel :-
  coq.version VersionString _ _ _,
  if (get-option "skip" R, rex_match R VersionString)
     (coq.warning "HB" "HB.skip" {get-option "elpi.loc"} "Skipping test on Coq" VersionString "as requested")
     (log.coq.check Skel Ty T Result,
      if (Result = error Msg)
         (if (get-option "fail" tt)
             (coq.say "The command did fail as expected with message:" Msg)
             (coq.error "HB.check:" Msg))
         (if (get-option "fail" tt)
             (coq.error "The command did not fail")
             (coq.say "HB.check:" {coq.term->string T} ":" {coq.term->string Ty}))).

}}.
Elpi Typecheck.
Elpi Export HB.check.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** Technical notations from /Canonical Structures for the working Coq user/ *)
Notation "`Error_cannot_unify: t1 'with' t2" := (unify t1 t2 None)
  (at level 0, format "`Error_cannot_unify:  t1  'with'  t2", only printing) :
  form_scope.
  Notation "`Error: t `is_not_canonically_a T" := (unify t _ (Some (is_not_canonically_a, T)))
  (at level 0, T at level 0, format "`Error:  t  `is_not_canonically_a  T", only printing) :
  form_scope.

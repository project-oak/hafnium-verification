(*
 * Copyright 2020 Youngju Song
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)
From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Structures.Foldable
     Structures.Reducible
     Structures.Maps
     Data.List.

From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.StateFacts.

From ITree Require Import
     ITree ITreeFacts.

Import ITreeNotations.
Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.
Require Import Any.
Require Import sflib.
Require Import Coqlib.

Require Import ClassicalDescription EquivDec.
About excluded_middle_informative.

Set Implicit Arguments.
(* Set Typeclasess Depth 4. *)
(* Typeclasses eauto := debug 4. *)





Definition var : Set := string.

Inductive val: Type :=
| Vnat (n: nat)
| Vptr (paddr: option nat) (contents: list val)
(* | Vundef *)
(* | Vnodef *)
.

Definition val_dec (v1 v2: val): {v1 = v2} + {v1 <> v2}.
  revert v1 v2.
  fix H 1.
  intros.
  decide equality.
  - apply (Nat.eq_dec n n0).
  - apply (list_eq_dec H contents contents0).
  - destruct paddr, paddr0; decide equality; try apply Nat.eq_dec.
Defined.

Definition Vnull := Vptr (Some 0) [].
(* YJ: (Some 0) or None?
Some 0 로 하면 처음에 ptable_buf 넣는거는 Vnull 이 아님을 (i.e. paddr <> 0) 알아야 함 *)
(* YJ: is it really the same with nodef? or do we need explicit nodef? *)
Definition Vnodef := Vnull.

Definition Vtrue := Vnat 1.
Definition Vfalse := Vnat 0.

(** Casting vals into [bool]:  [0] corresponds to [false] and any nonzero
      val corresponds to [true].  *)
Definition is_true (v : val) : bool :=
  match v with
  | Vnat n => if (n =? 0)%nat then false else true
  (* YJ: THIS IS TEMPORARY HACKING *)
  (* | Vptr _ (_ :: _) => true (* nonnull pointer *) *)
  (* | Vptr _ _ => false (* null pointer *) *)
  | Vptr paddr _ =>
    match paddr with
    | Some O => false
    | _ => true
    end
  end
.

Definition bool_to_val (b: bool): val :=
  match b with
  | true => Vtrue
  | false => Vfalse
  end
.

Coercion bool_to_val: bool >-> val.



(** Expressions are made of variables, constant literals, and arithmetic operations. *)
Inductive expr : Type :=
| Var (_ : var)
| Lit (_ : val)
| Plus  (_ _ : expr)
| Minus (_ _ : expr)
| Mult  (_ _ : expr)
| Div   (_ _ : expr)
| Equal (_ _: expr)
| Neg (_: expr)
| LE (_ _: expr)
| Load (_: var) (_: expr)
| CoqCode (_: list expr) (P: list val -> val)
| Put (msg: string) (e: expr)
| Debug (msg: string) (e: expr)
| Get
| Call (func_name: string) (params: list (var + expr))
| Ampersand (_: expr)
| GetLen (_: expr)
(* YJ: Vptr에 addr: nat 추가하면?
     int x = 5;
     int *y = &x;
     int *z = &x;
 *)

(* YJ: fixpoint decreasing argument thing *)
(* | SubPointer (_: expr) (from: option expr) (to: option expr) *)
(* | SubPointer (_: expr) (from: expr + unit) (to: expr + unit) *)
| SubPointerFrom (_: expr) (from: expr)
| SubPointerTo (_: expr) (to: expr)
.

Definition CBV: expr -> var + expr := inr.
Definition CBR: var -> var + expr := inl.

(** The statements are straightforward. The [While] statement is the only
 potentially diverging one. *)

Inductive stmt : Type :=
| Assign (x : var) (e : expr)    (* x = e *)
| Seq    (a b : stmt)            (* a ; b *)
| If     (i : expr) (t e : stmt) (* if (i) then { t } else { e } *)
| While  (t : expr) (b : stmt)   (* while (t) { b } *)
| Skip                           (* ; *)
| Assume
| Guarantee
| Store (x: var) (ofs: expr) (e: expr) (* x->ofs := e *)
(* YJ: I used "var" instead of "var + val". We should "update" retvs into variables. *)
| Expr (e: expr)
(* YJ: What kind of super power do we need?
e.g. See if x has even number --> we need something like "MetaIf (var -> P: Prop)"
 *)
| Return (e: expr)
| Break
| Continue
| Yield
.

Inductive function: Type := mk_function { params: list var ; body: stmt }.
Definition program: Type := list (string * function).

(* ========================================================================== *)
(** ** Notations *)

Module LangNotations.

  (** A few notations for convenience.  *)
  Definition Expr_coerce: expr -> stmt := Expr.
  Definition Var_coerce: string -> expr := Var.
  Definition Lit_coerce: val -> expr := Lit.
  Definition nat_coerce: nat -> val := Vnat.
  Coercion Expr_coerce: expr >-> stmt.
  Coercion Var_coerce: string >-> expr.
  Coercion Lit_coerce: val >-> expr.
  Coercion nat_coerce: nat >-> val.

  Bind Scope expr_scope with expr.

  Infix "+" := Plus : expr_scope.
  Infix "-" := Minus : expr_scope.
  Infix "*" := Mult : expr_scope.
  Infix "/" := Div : expr_scope.
  Infix "==" := Equal : expr_scope.
  Infix "<=" := LE : expr_scope.
  (* Notation "'NULL'" := (Vptr []) (at level 40): expr_scope. *)

  Notation "'!' e" :=
    (Neg e) (at level 40, e at level 50): stmt_scope.

  Bind Scope stmt_scope with stmt.

  Notation "x '#:=' e" :=
    (Assign x e) (at level 60, e at level 50): stmt_scope.

  Notation "a '#;' b" :=
    (Seq a b)
      (at level 120, right associativity,
       format
         "'[v' a  '#;' '/' '[' b ']' ']'"
      ): stmt_scope.

  Notation "'#if' i 'then' t 'else' e" :=
    (If i t e)
      (at level 100,
       right associativity,
       format
         "'[v ' '#if'  i '/' '[' 'then'  t  ']' '/' '[' 'else'  e ']' ']'").

  Notation "'#while' t 'do' b" :=
    (While t b)
      (at level 100,
       right associativity,
       format
         "'[v  ' '#while'  t  'do' '/' '[v' b  ']' ']'").

  (* Notation "x '#->' ofs '#:=' e" := *)
  (*   (Store x ofs e) (at level 60, e at level 50): stmt_scope. *)

  (* Notation "x '#->' ofs" := *)
  (*   (Load x ofs) (at level 99): expr_scope. *)

  Notation "#put e" :=
    (Put "" e) (at level 60, e at level 50): stmt_scope.

  (* Notation "x '#:=' '#get' e" := *)
  (*   (Get x e) (at level 60, e at level 50): stmt_scope. *)

  Notation "#& e" :=
    (Ampersand e) (at level 60, e at level 50): stmt_scope.

  Notation "#* e" :=
    (Load e 0) (at level 40, e at level 50): stmt_scope.

End LangNotations.

Import LangNotations.

Variant LocalE : Type -> Type :=
| GetVar (x : var) : LocalE val
| SetVar (x : var) (v : val) : LocalE unit
| PushEnv: LocalE unit
| PopEnv: LocalE unit
(* | StoreVar (x: var) (ofs: nat) (v: val): LocalE bool *)
.

Variant Event: Type -> Type :=
| ENB (msg: string): Event void
| EUB (msg: string): Event void
| ESyscall
    (name: string)
    (msg: string)
    (args: list val): Event val
| EYield: Event unit
.

(* YJ: Will be consumed internally *)
Variant CallInternalE: Type -> Type :=
| CallInternal (func_name: string) (args: list val): CallInternalE (val * list val)
.

Variant CallExternalE: Type -> Type :=
| CallExternal (func_name: string) (args: list val): CallExternalE (val * list val)
.

Definition triggerUB {E A} `{Event -< E} (msg: string): itree E A :=
  vis (EUB msg) (fun v => match v: void with end)
.
Definition triggerNB {E A} `{Event -< E} (msg: string) : itree E A :=
  vis (ENB msg) (fun v => match v: void with end)
.
Definition triggerSyscall {E} `{Event -< E} : string -> string -> list val -> itree E val :=
  embed ESyscall
.

Definition unwrapN {E X} `{Event -< E} (x: option X): itree E X :=
  match x with
  | Some x => ret x
  | None => triggerNB "unwrap"
  end.

Definition unwrapU {E X} `{Event -< E} (x: option X): itree E X :=
  match x with
  | Some x => ret x
  | None => triggerUB "unwrap"
  end.

Section Denote.

  (** We now proceed to denote _Imp_ expressions and statements.
      We could simply fix in stone the universe of events to be considered,
      taking as a semantic domain for _Imp_ [itree ImpState X]. That would be
      sufficient to give meaning to _Imp_, but would prohibit us from relating this
      meaning to [itree]s stemmed from other entities. Therefore, we
      parameterize the denotation of _Imp_ by a larger universe of events [eff],
      of which [ImpState] is assumed to be a subevent. *)

  Context {eff : Type -> Type}.
  Context {HasLocalE: LocalE -< eff}.
  Context {HasEvent : Event -< eff}.
  Context {HasCallInternalE: CallInternalE -< eff}.
  Context {HasCallExternalE: CallExternalE -< eff}.

  (** _Imp_ expressions are denoted as [itree eff val], where the returned
      val in the tree is the val computed by the expression.
      In the [Var] case, the [trigger] operator smoothly lifts a single event to
      an [itree] by performing the corresponding [Vis] event and returning the
      environment's answer immediately.
      A constant (literal) is simply returned.
      Usual monadic notations are used in the other cases: we can [bind]
      recursive computations in the case of operators as one would expect. *)

  Variable ctx: program.

  From ExtLib Require Import Structures.Applicative.
  Print Instances Applicative.

  Fixpoint denote_expr (e : expr) : itree eff val :=
    match e with
    | Var v     => trigger (GetVar v)
    | Lit n     => ret n
    | Plus a b  => l <- denote_expr a ;; r <- denote_expr b ;;
                     match l, r with
                     | Vnat l, Vnat r => ret (Vnat (l + r))
                     | _, _ => triggerNB "expr-plus"
                     end
    | Minus a b => l <- denote_expr a ;; r <- denote_expr b ;;
                     match l, r with
                     | Vnat l, Vnat r => ret (Vnat (l - r))
                     | _, _ => triggerNB "expr-minus"
                     end
    | Mult a b  => l <- denote_expr a ;; r <- denote_expr b ;;
                     match l, r with
                     | Vnat l, Vnat r => ret (Vnat (l * r))
                     | _, _ => triggerNB "expr-mult"
                     end
    | Div a b   => l <- denote_expr a ;; r <- denote_expr b ;;
                     match l, r with
                     | Vnat l, Vnat r => ret (Vnat (l / r))
                     | _, _ => triggerNB "expr-mult"
                     end
    | Equal a b => l <- denote_expr a ;; r <- denote_expr b ;;
                     Ret (if val_dec l r then Vtrue else Vfalse)
    | Neg a => v <- denote_expr a ;; Ret (if is_true v then Vfalse else Vtrue)
    | LE a b => l <- denote_expr a ;; r <- denote_expr b ;;
                  match l, r with
                  | Vnat l, Vnat r => Ret (if Nat.leb l r then Vtrue else Vfalse)
                  | _, _ => triggerNB "expr-LE"
                  end
    | Load x ofs => x <- trigger (GetVar x) ;; ofs <- denote_expr ofs ;;
                      match x, ofs with
                      | Vptr _ cts, Vnat ofs =>
                        match nth_error cts ofs with
                        | Some v => ret v
                        | _ => triggerNB "expr-load1"
                        end
                      | _, _ => triggerNB "expr-load2"
                      end
    | CoqCode es P => vs <- mapT (denote_expr) es ;; ret (P vs)
    | Put msg e => v <- denote_expr e ;;
                 triggerSyscall "p" msg [v] ;; Ret (Vnodef)
    | Debug msg e => v <- denote_expr e ;;
                       triggerSyscall "d" msg [v] ;; Ret (Vnodef)
    | Get => triggerSyscall "g" "" []
    | Call func_name params =>
      (* | Call retv_name func_name arg_names => *)
      (* args <- mapT (fun arg => trigger (GetVar arg)) arg_names;; *)
      (* '(retv, args_updated) <- trigger (CallInternal func_name args);; *)
      (* if (length args_updated =? length arg_names)%nat *)
      (* then *)
      (*   mapT (fun '(arg_name, arg_updated) => trigger (SetVar arg_name arg_updated)) *)
      (*        (combine arg_names args_updated);; *)
      (*        trigger (SetVar retv_name retv) ;; *)
      (*        ret (CNormal, Vnodef) *)
      (* else triggerNB *)

      args <- (mapT (case_ (Case:=case_sum)
                           (fun name => trigger (GetVar name))
                           (fun e => denote_expr e)) params) ;;
      '(retv, args_updated) <- match (find (fun '(n, _) => string_dec func_name n) ctx) with
                               | Some _ => trigger (CallInternal func_name args)
                               | None => trigger (CallExternal func_name args)
                               end ;;
      let nvs: list (var * val) := (filter_map (fun '(ne, v) =>
                                                  match ne with
                                                  | inl n => Some (n, v)
                                                  | _ => None
                                                  end)
                                               (combine params args_updated))
      in
      mapT (fun '(n, v) => trigger (SetVar n v)) nvs ;;
      ret retv
    | Ampersand e => v <- (denote_expr e) ;; Ret (Vptr None [v])
    | SubPointerFrom p from =>
      p <- (denote_expr p) ;; from <- (denote_expr from) ;;
        match p with
        | Vptr paddr cts =>
          match from with
          | Vnat from => Ret (Vptr (liftA (Nat.add from) paddr) (skipn from cts))
          | _ => triggerNB "expr-subpointer1"
          end
        | _ => triggerNB "expr-subpointer2"
        end
    | SubPointerTo p to =>
      p <- (denote_expr p) ;; to <- (denote_expr to) ;;
        match p with
        | Vptr paddr cts =>
          match to with
          | Vnat to => Ret (Vptr paddr (firstn to cts))
          | _ => triggerNB "expr-subpointer1"
          end
        | _ => triggerNB "expr-subpointer2"
        end
    (* | SubPointer p from to => *)
    (*   p <- (denote_expr p) ;; *)
    (*     match p with *)
    (*     | Vptr cts => *)
          (* from <- denote_expr (match from with *)
          (*                      | inl from => from *)
          (*                      | inr _ => 0 *)
          (*                      end) ;; *)
          (* to <- denote_expr (match to with *)
          (*                    | inl to => to *)
          (*                    | inr _ => 0 *)
          (*                    end) ;; *)
        (*   match from, to with *)
        (*   | Vnat from, Vnat to => Ret (Vptr (firstn to (skipn from cts))) *)
        (*   | _, _ => triggerNB "expr-subpointer1" *)
        (*   end *)
        (* | _ => triggerNB "expr-subpointer2" *)
        (* end *)
    | GetLen e => e <- denote_expr e ;;
                    match e with
                    | Vptr _ cts => Ret ((length cts): val)
                    | _ => triggerNB "expr-getlen"
                    end
    end.

  Inductive control: Type :=
  | CNormal
  | CContinue
  | CBreak
  | CReturn
  .

  Definition is_normal (c: control): bool := match c with | CNormal => true | _ => false end.

  (** We turn to the denotation of statements. As opposed to expressions,
      statements do not return any val: their semantic domain is therefore
      [itree eff unit]. The most interesting construct is, naturally, [while].

      To define its meaning, we make use of the [iter] combinator provided by
      the [itree] library:

      [iter : (A -> itree E (A + B)) -> A -> itree E B].

      The combinator takes as argument the body of the loop, i.e. a function
      that maps inputs of type [A], the accumulator, to an [itree] computing
      either a new [A] that can be fed back to the loop, or a return val of
      type [B]. The combinator builds the fixpoint of the body, hiding away the
      [A] argument from the return type.

      Compared to the [mrec] and [rec] combinators introduced in
      [Introduction.v], [iter] is more restricted in that it naturally
      represents tail recursive functions.  It, however, enjoys a rich equational
      theory: its addition grants the type of _continuation trees_ (named
      [ktree]s in the library), a structure of _traced monoidal category_.

      We use [loop] to first build a new combinator [while].
      The accumulator degenerates to a single [unit] val indicating
      whether we entered the body of the while loop or not. Since the
      the operation does not return any val, the return type is also
      taken to be [unit].
      That is, the right tag [inr tt] says to exit the loop,
      while the [inl tt] says to continue. *)

  Definition while (step: itree eff (unit + (control * val))): itree eff (control * val) :=
    (* iter (C := Kleisli _) (fun _ => step) tt *)
    ITree.iter (fun _ => step) tt
  .

  (** The meaning of Imp statements is now easy to define.  They are all
      straightforward, except for [While], which uses our new [while] combinator
      over the computation that evaluates the conditional, and then the body if
      the former was true.  *)
  Typeclasses eauto := debug 4.

  Fixpoint denote_stmt (s : stmt) : itree eff (control * val) :=
    match s with
    | Assign x e =>  v <- denote_expr e ;; trigger (SetVar x v) ;; ret (CNormal, Vnodef)
    | Seq a b    =>  '(c, v) <- denote_stmt a ;; if (is_normal c)
                                                 then denote_stmt b
                                                 else ret (c, v)
    | If i t e   =>
      v <- denote_expr i ;;
      if is_true v then denote_stmt t else denote_stmt e

    | While t b =>
      (while (v <- denote_expr t ;;
                if is_true v
                then '(c, v) <- denote_stmt b ;;
                      match c with
                      | CNormal | CContinue => ret (inl tt)
                      | CBreak => ret (inr (CNormal, v))
                      | CReturn => ret (inr (CReturn, v))
                      end
                else ret (inr (CNormal, Vnodef (* YJ: this is temporary *)))))
    | Skip => ret (CNormal, Vnodef)
    | Assume => triggerUB "stmt-assume"
    | Guarantee => triggerNB "stmt-grnt"
    | Store x ofs e => ofs <- denote_expr ofs ;; e <- denote_expr e ;;
                           v <- trigger (GetVar x) ;;
                           match ofs, v with
                           | Vnat ofs, Vptr paddr cts0 =>
                             cts1 <- (unwrapN (update_err cts0 ofs e)) ;;
                                  trigger (SetVar x (Vptr paddr cts1))
                           | _, _ => triggerNB "stmt-store"
                           end ;;
                           ret (CNormal, Vnodef)
    | Expr e => v <- denote_expr e ;; Ret (CNormal, v)
    | Return e => v <- denote_expr e ;; Ret (CReturn, v)
    | Break => Ret (CBreak, Vnodef)
    | Continue => Ret (CContinue, Vnodef)
    | Yield => trigger EYield ;; Ret (CNormal, Vnodef)
    end.

End Denote.

Section Denote.

  Open Scope expr_scope.
  Open Scope stmt_scope.

  Context {eff : Type -> Type}.
  Context {HasLocalE : LocalE -< eff}.
  Context {HasEvent : Event -< eff}.
  Context {HasCallExternalE: CallExternalE -< eff}.

  Print Instances Traversable.
  Print Instances Reducible.
  Print Instances Foldable.

  Definition denote_function (ctx: program):
    (CallInternalE ~> itree (CallInternalE +' eff)) :=
    fun T ei =>
      let '(CallInternal func_name args) := ei in
      nf <- unwrapN (find (fun nf => string_dec func_name (fst nf)) ctx) ;;
         let f := (snd nf) in
         if (length f.(params) =? length args)%nat
         then
           trigger PushEnv ;;
           let new_body := fold_left (fun s i => (fst i) #:= (Lit (snd i)) #; s)
                                     (* YJ: Why coercion does not work ?? *)
                                     (combine f.(params) args) f.(body) in
           '(_, retv) <- denote_stmt ctx new_body ;;
           (* YJ: maybe we can check whether "control" is return (not break/continue) here *)
           params_updated <- mapT (fun param => trigger (GetVar param)) (f.(params));;
           trigger PopEnv ;;
           ret (retv, params_updated)
         else triggerNB "denote_function"
  .

  Definition denote_program (p: program): itree eff (val * (list val)) :=
    let sem: CallInternalE ~> itree eff := mrec (denote_function p) in
    sem _ (CallInternal "main" []).
  (* Better readability *)

  Definition denote_program2 (p: program): CallInternalE ~> itree eff :=
    mrec (denote_function p)
  .

End Denote.

(* ========================================================================== *)
(** ** EXAMPLE: Factorial *)

Section Example_Fact.

  (** We briefly illustrate the language by writing the traditional factorial.
      example.  *)

  Open Scope expr_scope.
  Open Scope stmt_scope.
  Variable input: var.
  Variable output: var.

  Definition fact (n:nat): stmt :=
    input #:= n#;
    output #:= 1#;
    #while input
    do output #:= output * input#;
       input  #:= input - Vnat 1.

  (** We have given _a_ notion of denotation to [fact 6] via [denote_imp].
      However, this is naturally not actually runnable yet, since it contains
      uninterpreted [ImpState] events.  We therefore now need to _handle_ the
      events contained in the trees, i.e. give a concrete interpretation of the
      environment.  *)

End Example_Fact.

(* ========================================================================== *)
(** ** Interpretation *)

(* begin hide *)
From ITree Require Import
     Events.MapDefault.

From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

(** These enable typeclass instances for Maps keyed by strings and vals *)
Instance RelDec_string : RelDec (@eq string) :=
  { rel_dec := fun s1 s2 => if string_dec s1 s2 then true else false}.

Instance RelDec_string_Correct: RelDec_Correct RelDec_string.
Proof.
  constructor; intros x y.
  split.
  - unfold rel_dec; simpl.
    destruct (string_dec x y) eqn:EQ; [intros _; apply string_dec_sound; assumption | intros abs; inversion abs].
  - intros EQ; apply string_dec_sound in EQ; unfold rel_dec; simpl; rewrite EQ; reflexivity.
Qed.
(* end hide *)

(** We provide an _ITree event handler_ to interpret away [ImpState] events.  We
    use an _environment event_ to do so, modeling the environment as a
    0-initialized map from strings to vals.  Recall from [Introduction.v] that
    a _handler_ for the events [ImpState] is a function of type [forall R, ImpState R
    -> M R] for some monad [M].  Here we take for our monad the special case of
    [M = itree E] for some universe of events [E] required to contain the
    environment events [mapE] provided by the library. It comes with an event
    interpreter [interp_map] that yields a computation in the state monad.  *)
Definition env := list (alist var val).
Definition handle_LocalE {E: Type -> Type}
  : LocalE ~> stateT env (itree E) :=
  fun _ e env =>
    let hd := hd empty env in
    (** YJ: error handling needed?
error does not happen by construction for now, but when development changes..?
How can we add error check here?
     **)
    let tl := tl env in
    match e with
    | GetVar x => Ret (env, (lookup_default x (Vnat 0) hd))
    | SetVar x v => Ret ((Maps.add x v hd) :: tl, tt)
    | PushEnv => Ret (empty :: hd :: tl, tt)
    | PopEnv => Ret (tl, tt)
    end.

(** We now concretely implement this environment using ExtLib's finite maps. *)
(* Definition env := alist var val. *)

(** Finally, we can define an evaluator for our statements.
   To do so, we first denote them, leading to an [itree ImpState unit].
   We then [interp]ret [ImpState] into [mapE] using [handle_ImpState], leading to
   an [itree (mapE var val) unit].
   Finally, [interp_map] interprets the latter [itree] into the state monad,
   resulting in an [itree] free of any event, but returning the final
   _Imp_ env.
 *)
(* SAZ: would rather write something like the following:
 h : E ~> M A
 h' : F[void1] ~> M A
forall eff, {pf:E -< eff == F[E]} (t : itree eff A)
        interp pf h h' t : M A
*)

(** YJ: copied from interp_map's definition **)
Definition interp_imp  {E A} (t : itree (LocalE +' E) A) :
  stateT env (itree E) A :=
  let t' := State.interp_state (case_ handle_LocalE State.pure_state) t in
  t'
.

Definition ignore_l {A B}: itree (A +' B) ~> itree B :=
  interp (fun _ e =>
            match e with
            | inl1 a => ITree.spin
            | inr1 b => trigger b
            end)
.

Definition eval_program (p: program): itree Event unit
  := @ignore_l CallExternalE Event _ (ITree.ignore (interp_imp (denote_program p) [])).
  (* := ignore_l (ITree.ignore (interp_imp (denote_program p) [])). *)

Print Instances Iter.
Print Instances MonadIter.

Variant AnyState: Type -> Type :=
| GetAny (midx: nat): AnyState Any
| SetAny (midx: nat) (a: Any): AnyState unit
.

Inductive ModSem: Type :=
  mk_ModSem { genv: string -> bool ;
              owned_heap: Type;
              initial_owned_heap: owned_heap;
              customE: Type -> Type ;
              handler: customE ~> stateT owned_heap (itree Event);

              (* handler: forall E, AnyState ~> stateT Any (itree E); *)
              (* sem: CallExternalE ~> itree (CallExternalE +' Event); *)

              sem: CallExternalE ~> itree (CallExternalE +' Event +' customE);
            }.

Arguments mk_ModSem _ {owned_heap}.

Fixpoint sum_all1 (Es: list (Type -> Type)): Type -> Type :=
  match Es with
  | [] => void1
  | hd :: tl => hd +' sum_all1 tl
  end
.
Print Instances Embeddable.
Print Instances ReSum.

Definition INCL: forall Es E (IN: { n & nth_error Es n = Some E} ), E ~> (sum_all1 Es).
  intro. induction Es; ii; ss.
  - destruct IN. destruct x; ss.
  - destruct IN. destruct x; ss.
    + left. clarify.
    + right. eapply IHEs; eauto.
Defined.

Definition INCL2: forall Es (nE: { nE & nth_error Es (fst nE) = Some (snd nE)}),
    (snd (projT1 nE)) ~> (sum_all1 Es).
  intro. induction Es; ii; ss.
  - destruct nE. ss. destruct x; ss. destruct n; ss.
  - destruct nE. ss. destruct x; ss. rename T0 into E. destruct n; ss.
    + left. clarify.
    + right. unshelve eapply IHEs; eauto.
      { exists (n, E). ss. }
      ss.
Defined.

Definition INCL3: forall Es (nE: { nE & nth_error Es (fst nE) = Some (snd nE)}),
    (customE (snd (projT1 nE))) ~> (sum_all1 (List.map customE Es)).
  intro. induction Es; ii; ss.
  - destruct nE. ss. destruct x; ss. destruct n; ss.
  - destruct nE. ss. destruct x; ss. destruct n; ss.
    + left. clarify.
    + right. unshelve eapply IHEs; eauto.
      { exists (n, m). ss. }
      ss.
Defined.

Definition FINDN: forall A (a: A) l cond (FIND: List.find cond l = Some a),
    { n & nth_error l n = Some a}.
  i. ginduction l; ii; ss.
  des_ifs.
  - exists 0. ss.
  - exploit IHl; eauto. i. destruct x. exists (S x). ss.
Defined.

Fixpoint find_informative A (cond: A -> bool) (l: list A):
  option ({ na & nth_error l (fst na) = Some (snd na)}).
  destruct l.
  - apply None.
  - destruct (cond a) eqn:T.
    + apply Some.
      exists (0, a).
      ss.
    + hexploit (@find_informative _ cond l). intro. destruct X.
      * destruct s. destruct x. ss. apply Some. exists (S n, a0). ss.
      * apply None.
Defined.

Obligation Tactic := idtac.

Definition eval_multimodule_aux (mss: list ModSem):
  itree (Event +' (sum_all1 (List.map customE mss))) (val * list val)
  :=
  let sem: CallExternalE ~> itree (Event +' (sum_all1 (List.map customE mss))) :=
      mrec (fun T (c: CallExternalE T) =>
              let '(CallExternal func_name args) := c in
              match find_informative (fun ms => ms.(genv) func_name) mss with
              | Some nms =>
                let ms := (snd (projT1 nms)) in
                let t: itree (CallExternalE +' Event +' customE ms) T := (ms.(sem) c) in
                translate (fun T e =>
                             match e with
                             | inl1 e => inl1 e
                             | inr1 (inl1 e) => inr1 (inl1 e)
                             | inr1 (inr1 e) =>
                               let tmp: (sum_all1 (List.map customE mss)) T :=
                                   (@INCL3 mss
                                           nms
                                           T e)
                                   (* @INCL (List.map customE mss) *)
                                   (*       (customE ms) *)
                                   (*       (admit "") *)
                                   (*       T e *)
                               in
                               inr1 (inr1 tmp)
                             end) t
                (* ITree.spin *)
              | _ => triggerUB "eval_multimodule_aux"
              end)
              (* match (List.find (fun ms => ms.(genv) func_name) mss) as H with *)
              (* | Some ms => *)
              (*   let t: itree (CallExternalE +' Event +' customE ms) T := (ms.(sem) c) in *)
              (*   translate (fun T e => *)
              (*                match e with *)
              (*                | inl1 e => inl1 e *)
              (*                | inr1 (inl1 e) => inr1 (inl1 e) *)
              (*                | inr1 (inr1 e) => *)
              (*                  let tmp := *)
              (*                      @INCL (List.map customE mss) *)
              (*                            (customE ms) *)
              (*                            (admit "") *)
              (*                            T e *)
              (*                  in *)
              (*                  inr1 (inr1 tmp) *)
              (*                end) t *)
              (*   (* ITree.spin *) *)
              (* | _ => triggerUB *)
              (* end) *)
  in
  sem _ (CallExternal "main" [])
.

Inductive hlist (mss: list ModSem): Type :=
| hlist_nil
    (NIL: mss = [])
| hlist_cons
    hd tl
    (MATCH: mss = hd :: tl)
    (HD: hd.(owned_heap))
    (TL: hlist tl)
.

Inductive hvec (n: nat): Type :=
  (* mk_hlist { hlist_body: list Any ; LEN: length hlist_body = n }. *)
| mk_hvec
    (l: list Any)
    (LEN: length l = n)
.

Definition HANDLE: forall mss,
    (sum_all1 (List.map customE mss)) ~> stateT (list Any) (itree Event)
.
  intro. induction mss.
  { i; ss. }
  (* eapply case_. *)
  i. destruct X.
  - eapply a.(handler) in c.
    ii. ss.
    destruct X. ss.
    { eapply (triggerUB "HANDLE1"). }
    rename a0 into hd. rename X into tl.
    eapply downcast with (T:= owned_heap a) in hd.
    destruct hd; cycle 1.
    { apply (triggerUB "HANDLE2"). }
    eapply c in o. eapply ITree.map; try eapply o.
    intro. destruct X. econs.
    { eapply cons.
      - apply (existT id _ o0).
      - apply tl.
    }
    apply t.
  - eapply IHmss in s. ss.
Defined.

Definition HANDLE2: forall mss,
    (sum_all1 (List.map customE mss)) ~> stateT (hvec (length mss)) (itree Event)
.
  intro. induction mss.
  { i; ss. }
  (* eapply case_. *)
  i. destruct X.
  - eapply a.(handler) in c.
    ii. ss.
    destruct X. destruct l; ss. clarify.
    rename a0 into hd. rename l into tl.
    eapply downcast with (T:= owned_heap a) in hd.
    destruct hd; cycle 1.
    { apply (triggerUB "HANDLE2A"). }
    eapply c in o. eapply ITree.map; try eapply o.
    intro. destruct X. econs.
    { unshelve econs.
      - eapply cons.
        { apply (existT id _ o0). }
        { apply tl. }
      - ss. eauto.
    }
    apply t.
  - eapply IHmss in s. ss.
    ii. inv X. destruct l; ss. clarify.
    rename a0 into hd. rename l into tl.
    assert(tl':= @mk_hvec (length mss) tl H0).
    eapply s in tl'.
    eapply ITree.map; try eapply tl'.
    intro. destruct X. inv h. rename l into tl2. econs.
    { unshelve econs.
      - eapply (hd :: tl2).
      - ss. eauto.
    }
    apply t.
Defined.

Fixpoint INITIAL (mss: list ModSem): list Any :=
  match mss with
  | [] => []
  | hd :: tl => (existT id _ hd.(initial_owned_heap)) :: INITIAL tl
  end
.

Definition INITIAL2 (mss: list ModSem): hvec (length mss).
  induction mss.
  - ss. econs. instantiate (1:=[]). ss.
  - ss. inv IHmss. econs. instantiate (1:=(existT id _ a.(initial_owned_heap))::l). ss.
    eauto.
Defined.

Inductive unit1: Type -> Type :=
.

Definition program_to_ModSem (p: program): ModSem :=
  mk_ModSem
    (* (fun s => in_dec Strings.String.string_dec s (List.map fst p)) *)
    (fun s => existsb (string_dec s) (List.map fst p))
    tt
    void1
    (fun T e _ => ITree.map (fun t => (tt, t)) (Handler.empty _ e))
    (fun T (c: CallExternalE T) =>
       let '(CallExternal func_name args) := c in
       ITree.map snd (interp_imp ((denote_program2 p) _ (CallInternal func_name args)) [])
    )
.

Definition eval_multimodule (mss: list ModSem): itree Event unit :=
  let t := eval_multimodule_aux mss in
  let st := State.interp_state (case_ State.pure_state (HANDLE2 mss)) t in
  ITree.ignore (st (INITIAL2 mss))
.

(** Equipped with this evaluator, we can now compute.
    Naturally since Coq is total, we cannot do it directly inside of it.
    We can either rely on extraction, or use some fuel.
 *)


(* ========================================================================== *)
Section InterpImpProperties.
  (** We can lift the underlying equational theory on [itree]s to include new
      equations for working with [interp_imp].

      In particular, we have:
         - [interp_imp] respects [≈]
         - [interp_imp] commutes with [bind].

      We could justify more equations than just the ones below.  For instance,
      _Imp_ programs also respect a coarser notation of equivalence for the
      [env] state.  We exploit this possibility to implement optimzations
      at the _Asm_ level (see AsmOptimizations.v).
   *)

  Context {E': Type -> Type}.
  Notation E := (LocalE +' E').

  (** This interpreter is compatible with the equivalence-up-to-tau. *)
  Global Instance eutt_interp_imp {R}:
    Proper (@eutt E R R eq ==> eq ==> @eutt E' (prod (env) R) (prod _ R) eq)
           interp_imp.
  Proof.
    repeat intro.
    unfold interp_imp.
    unfold interp_map.
    rewrite H0. eapply eutt_interp_state_eq; auto.
    (* rewrite H. reflexivity. *)
  Qed.

  (** [interp_imp] commutes with [bind]. *)
  Lemma interp_imp_bind: forall {R S} (t: itree E R) (k: R -> itree E S) (g : env),
      (interp_imp (ITree.bind t k) g)
    ≅ (ITree.bind (interp_imp t g) (fun '(g',  x) => interp_imp (k x) g')).
  Proof.
    intros.
    unfold interp_imp.
    unfold interp_map.
    repeat rewrite interp_bind.
    repeat rewrite interp_state_bind.
    apply eqit_bind. red. intros.
    destruct a as [g'  x].
    simpl.
    reflexivity.
    reflexivity.
  Qed.

End InterpImpProperties.



(** We now turn to our target language, in file [Asm].v *)


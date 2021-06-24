(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Elimination of unreferenced static definitions *)

Require Import FSets Coqlib Maps Ordered Iteration Errors.
Require Import AST Linking.
Require Import Integers Values Memory Globalenvs Events Smallstep.
Require Import Op Registers RTL.
Require Import Unusedglob.

Module ISF := FSetFacts.Facts(IS).
Module ISP := FSetProperties.Properties(IS).


(** * Relational specification of the transformation *)

(** The transformed program is obtained from the original program
  by keeping only the global definitions that belong to a given
  set [u] of names.  *)

Record match_prog_1 (u: IS.t) (p tp: program) : Prop := {
  match_prog_main:
    tp.(prog_main) = p.(prog_main);
  match_prog_public:
    tp.(prog_public) = p.(prog_public);
  match_prog_def:
    forall id,
       (prog_defmap tp)!id = if IS.mem id u then (prog_defmap p)!id else None;
  match_prog_unique:
    list_norepet (prog_defs_names tp)
}.

(** This set [u] (as "used") must be closed under references, and
  contain the entry point and the public identifiers of the program. *)

Definition ref_function (f: function) (id: ident) : Prop :=
  exists pc i, f.(fn_code)!pc = Some i /\ In id (ref_instruction i).

Definition ref_fundef (fd: fundef) (id: ident) : Prop :=
  match fd with Internal f => ref_function f id | External ef => False end.

Definition ref_init (il: list init_data) (id: ident) : Prop :=
  exists ofs, In (Init_addrof id ofs) il.

Definition ref_def (gd: globdef fundef unit) (id: ident) : Prop :=
  match gd with
  | Gfun fd => ref_fundef fd id
  | Gvar gv => ref_init gv.(gvar_init) id
  end.

Record valid_used_set (p: program) (u: IS.t) : Prop := {
  used_closed: forall id gd id',
    IS.In id u -> (prog_defmap p)!id = Some gd -> ref_def gd id' ->
    IS.In id' u;
  used_main:
    IS.In p.(prog_main) u;
  used_public: forall id,
    In id p.(prog_public) -> IS.In id u;
  used_defined: forall id,
    IS.In id u -> In id (prog_defs_names p) \/ id = p.(prog_main)
}.

Definition match_prog (p tp: program) : Prop :=
  exists u: IS.t, valid_used_set p u /\ match_prog_1 u p tp.

(** * Properties of the static analysis *)

(** Monotonic evolution of the workset. *)

Inductive workset_incl (w1 w2: workset) : Prop :=
  workset_incl_intro:
    forall (SEEN: IS.Subset w1.(w_seen) w2.(w_seen))
           (TODO: List.incl w1.(w_todo) w2.(w_todo))
           (TRACK: forall id, IS.In id w2.(w_seen) ->
                      IS.In id w1.(w_seen) \/ List.In id w2.(w_todo)),
    workset_incl w1 w2.

Lemma seen_workset_incl:
  forall w1 w2 id, workset_incl w1 w2 -> IS.In id w1 -> IS.In id w2.
Proof.
  intros. destruct H. auto.
Qed.

Lemma workset_incl_refl: forall w, workset_incl w w.
Proof.
  intros; split. red; auto. red; auto. auto.
Qed.

Lemma workset_incl_trans:
  forall w1 w2 w3, workset_incl w1 w2 -> workset_incl w2 w3 -> workset_incl w1 w3.
Proof.
  intros. destruct H, H0; split.
  red; eauto.
  red; eauto.
  intros. edestruct TRACK0; eauto. edestruct TRACK; eauto.
Qed.

Lemma add_workset_incl:
  forall id w, workset_incl w (add_workset id w).
Proof.
  unfold add_workset; intros. destruct (IS.mem id w) eqn:MEM.
- apply workset_incl_refl.
- split; simpl.
  + red; intros. apply IS.add_2; auto.
  + red; simpl; auto.
  + intros. destruct (ident_eq id id0); auto. apply IS.add_3 in H; auto.
Qed.

Lemma addlist_workset_incl:
  forall l w, workset_incl w (addlist_workset l w).
Proof.
  induction l; simpl; intros.
  apply workset_incl_refl.
  eapply workset_incl_trans. apply add_workset_incl. eauto.
Qed.

Lemma add_ref_function_incl:
  forall f w, workset_incl w (add_ref_function f w).
Proof.
  unfold add_ref_function; intros. apply PTree_Properties.fold_rec.
- auto.
- apply workset_incl_refl.
- intros. apply workset_incl_trans with a; auto.
  unfold add_ref_instruction. apply addlist_workset_incl.
Qed.

Lemma add_ref_globvar_incl:
  forall gv w, workset_incl w (add_ref_globvar gv w).
Proof.
  unfold add_ref_globvar; intros.
  revert w. induction (gvar_init gv); simpl; intros.
  apply workset_incl_refl.
  eapply workset_incl_trans; [ | eauto ].
  unfold add_ref_init_data.
  destruct a; (apply workset_incl_refl || apply add_workset_incl).
Qed.

Lemma add_ref_definition_incl:
  forall pm id w, workset_incl w (add_ref_definition pm id w).
Proof.
  unfold add_ref_definition; intros.
  destruct (pm!id) as [[[] | ? ] | ].
  apply add_ref_function_incl.
  apply workset_incl_refl.
  apply add_ref_globvar_incl.
  apply workset_incl_refl.
Qed.

Lemma initial_workset_incl:
  forall p, workset_incl {| w_seen := IS.empty; w_todo := nil |} (initial_workset p).
Proof.
  unfold initial_workset; intros.
  eapply workset_incl_trans. 2: apply add_workset_incl.
  generalize {| w_seen := IS.empty; w_todo := nil |}. induction (prog_public p); simpl; intros.
  apply workset_incl_refl.
  eapply workset_incl_trans. apply add_workset_incl. apply IHl.
Qed.

(** Soundness properties for functions that add identifiers to the workset *)

Lemma seen_add_workset:
  forall id (w: workset), IS.In id (add_workset id w).
Proof.
  unfold add_workset; intros.
  destruct (IS.mem id w) eqn:MEM.
  apply IS.mem_2; auto.
  simpl. apply IS.add_1; auto.
Qed.

Lemma seen_addlist_workset:
  forall id l (w: workset),
  In id l -> IS.In id (addlist_workset l w).
Proof.
  induction l; simpl; intros.
  tauto.
  destruct H. subst a.
  eapply seen_workset_incl. apply addlist_workset_incl. apply seen_add_workset.
  apply IHl; auto.
Qed.

Lemma seen_add_ref_function:
  forall id f w,
  ref_function f id -> IS.In id (add_ref_function f w).
Proof.
  intros until w. unfold ref_function, add_ref_function. apply PTree_Properties.fold_rec; intros.
- destruct H1 as (pc & i & A & B). apply H0; auto. exists pc, i; split; auto. rewrite H; auto.
- destruct H as (pc & i & A & B). rewrite PTree.gempty in A; discriminate.
- destruct H2 as (pc & i & A & B). rewrite PTree.gsspec in A. destruct (peq pc k).
  + inv A. unfold add_ref_instruction. apply seen_addlist_workset; auto.
  + unfold add_ref_instruction. eapply seen_workset_incl. apply addlist_workset_incl.
    apply H1. exists pc, i; auto.
Qed.

Lemma seen_add_ref_definition:
  forall pm id gd id' w,
  pm!id = Some gd -> ref_def gd id' -> IS.In id' (add_ref_definition pm id w).
Proof.
  unfold add_ref_definition; intros. rewrite H. red in H0; destruct gd as [[f|ef]|gv].
  apply seen_add_ref_function; auto.
  contradiction.
  destruct H0 as (ofs & IN).
  unfold add_ref_globvar.
  assert (forall l (w: workset),
          IS.In id' w \/ In (Init_addrof id' ofs) l ->
          IS.In id' (fold_left add_ref_init_data l w)).
  {
    induction l; simpl; intros.
    tauto.
    apply IHl. intuition auto.
    left. destruct a; simpl; auto. eapply seen_workset_incl. apply add_workset_incl. auto.
    subst; left; simpl. apply seen_add_workset.
  }
  apply H0; auto.
Qed.

Lemma seen_main_initial_workset:
  forall p, IS.In p.(prog_main) (initial_workset p).
Proof.
  intros. apply seen_add_workset.
Qed.

Lemma seen_public_initial_workset:
  forall p id, In id p.(prog_public) -> IS.In id (initial_workset p).
Proof.
  intros. unfold initial_workset. eapply seen_workset_incl. apply add_workset_incl.
  assert (forall l (w: workset),
          IS.In id w \/ In id l -> IS.In id (fold_left (fun w id => add_workset id w) l w)).
  {
    induction l; simpl; intros.
    tauto.
    apply IHl. intuition auto; left.
    eapply seen_workset_incl. apply add_workset_incl. auto.
    subst a. apply seen_add_workset.
  }
  apply H0. auto.
Qed.

(** * Correctness of the transformation with respect to the relational specification *)

(** Correctness of the dependency graph traversal. *)

Section ANALYSIS.

Variable p: program.
Let pm := prog_defmap p.

Definition workset_invariant (w: workset) : Prop :=
  forall id gd id',
  IS.In id w -> ~List.In id (w_todo w) -> pm!id = Some gd -> ref_def gd id' ->
  IS.In id' w.

Definition used_set_closed (u: IS.t) : Prop :=
  forall id gd id',
  IS.In id u -> pm!id = Some gd -> ref_def gd id' -> IS.In id' u.

Lemma iter_step_invariant:
  forall w,
  workset_invariant w ->
  match iter_step pm w with
  | inl u => used_set_closed u
  | inr w' => workset_invariant w'
  end.
Proof.
  unfold iter_step, workset_invariant, used_set_closed; intros.
  destruct (w_todo w) as [ | id rem ]; intros.
- eapply H; eauto.
- set (w' := {| w_seen := w.(w_seen); w_todo := rem |}) in *.
  destruct (add_ref_definition_incl pm id w').
  destruct (ident_eq id id0).
  + subst id0. eapply seen_add_ref_definition; eauto.
  + exploit TRACK; eauto. intros [A|A].
    * apply SEEN. eapply H; eauto. simpl.
      assert (~ In id0 rem).
      { change rem with (w_todo w'). red; intros. elim H1; auto. }
      tauto.
    * contradiction.
Qed.

Theorem used_globals_sound:
  forall u, used_globals p pm = Some u -> used_set_closed u.
Proof.
  unfold used_globals; intros. eapply PrimIter.iterate_prop with (P := workset_invariant); eauto.
- intros. apply iter_step_invariant; auto.
- destruct (initial_workset_incl p).
  red; intros. edestruct TRACK; eauto.
  simpl in H4. eelim IS.empty_1; eauto.
  contradiction.
Qed.

Theorem used_globals_incl:
  forall u, used_globals p pm = Some u -> IS.Subset (initial_workset p) u.
Proof.
  unfold used_globals; intros.
  eapply PrimIter.iterate_prop with (P := fun (w: workset) => IS.Subset (initial_workset p) w); eauto.
- fold pm; unfold iter_step; intros. destruct (w_todo a) as [ | id rem ].
  auto.
  destruct (add_ref_definition_incl pm id {| w_seen := a; w_todo := rem |}).
  red; auto.
- red; auto.
Qed.

Corollary used_globals_valid:
  forall u,
  used_globals p pm = Some u ->
  IS.for_all (global_defined p pm) u = true ->
  valid_used_set p u.
Proof.
  intros. constructor.
- intros. eapply used_globals_sound; eauto.
- eapply used_globals_incl; eauto. apply seen_main_initial_workset.
- intros. eapply used_globals_incl; eauto. apply seen_public_initial_workset; auto.
- intros. apply ISF.for_all_iff in H0.
+ red in H0. apply H0 in H1. unfold global_defined in H1.
  destruct pm!id as [g|] eqn:E.
* left. change id with (fst (id,g)). apply in_map. apply in_prog_defmap; auto.
* InvBooleans; auto.
+ hnf. simpl; intros; congruence.
Qed.

End ANALYSIS.

(** Properties of the elimination of unused global definitions. *)

Section TRANSFORMATION.

Variable p: program.
Variable used: IS.t.

Let add_def (m: prog_map) idg := PTree.set (fst idg) (snd idg) m.

Remark filter_globdefs_accu:
  forall defs accu1 accu2 u,
  filter_globdefs u (accu1 ++ accu2) defs = filter_globdefs u accu1 defs ++ accu2.
Proof.
  induction defs; simpl; intros.
  auto.
  destruct a as [id gd]. destruct (IS.mem id u); auto.
  rewrite <- IHdefs. auto.
Qed.

Remark filter_globdefs_nil:
  forall u accu defs,
  filter_globdefs u accu defs = filter_globdefs u nil defs ++ accu.
Proof.
  intros. rewrite <- filter_globdefs_accu. auto.
Qed.

Lemma filter_globdefs_map_1:
  forall id l u m1,
  IS.mem id u = false ->
  m1!id = None ->
  (fold_left add_def (filter_globdefs u nil l) m1)!id = None.
Proof.
  induction l as [ | [id1 gd1] l]; simpl; intros.
- auto.
- destruct (IS.mem id1 u) eqn:MEM.
+ rewrite filter_globdefs_nil. rewrite fold_left_app. simpl.
  unfold add_def at 1. simpl. rewrite PTree.gso by congruence. eapply IHl; eauto.
  rewrite ISF.remove_b. rewrite H; auto.
+ eapply IHl; eauto.
Qed.

Lemma filter_globdefs_map_2:
  forall id l u m1 m2,
  IS.mem id u = true ->
  m1!id = m2!id ->
  (fold_left add_def (filter_globdefs u nil l) m1)!id = (fold_left add_def (List.rev l) m2)!id.
Proof.
  induction l as [ | [id1 gd1] l]; simpl; intros.
- auto.
- rewrite fold_left_app. simpl.
  destruct (IS.mem id1 u) eqn:MEM.
+ rewrite filter_globdefs_nil. rewrite fold_left_app. simpl.
  unfold add_def at 1 3. simpl.
  rewrite ! PTree.gsspec. destruct (peq id id1). auto.
  apply IHl; auto.
  apply IS.mem_1. apply IS.remove_2; auto. apply IS.mem_2; auto.
+ unfold add_def at 2. simpl. rewrite PTree.gso by congruence. apply IHl; auto.
Qed.

Lemma filter_globdefs_map:
  forall id u defs,
  (PTree_Properties.of_list (filter_globdefs u nil (List.rev defs)))! id =
  if IS.mem id u then (PTree_Properties.of_list defs)!id else None.
Proof.
  intros. unfold PTree_Properties.of_list. fold prog_map. unfold PTree.elt. fold add_def.
  destruct (IS.mem id u) eqn:MEM.
- erewrite filter_globdefs_map_2. rewrite List.rev_involutive. reflexivity.
  auto. auto.
- apply filter_globdefs_map_1. auto. apply PTree.gempty.
Qed.

Lemma filter_globdefs_domain:
  forall id l u,
  In id (map fst (filter_globdefs u nil l)) -> IS.In id u /\ In id (map fst l).
Proof.
  induction l as [ | [id1 gd1] l]; simpl; intros.
- tauto.
- destruct (IS.mem id1 u) eqn:MEM.
+ rewrite filter_globdefs_nil, map_app, in_app_iff in H. destruct H.
  apply IHl in H. rewrite ISF.remove_iff in H. tauto.
  simpl in H. destruct H; try tauto. subst id1. split; auto. apply IS.mem_2; auto.
+ apply IHl in H. tauto.
Qed.

Lemma filter_globdefs_unique_names:
  forall l u, list_norepet (map fst (filter_globdefs u nil l)).
Proof.
  induction l as [ | [id1 gd1] l]; simpl; intros.
- constructor.
- destruct (IS.mem id1 u) eqn:MEM; auto.
  rewrite filter_globdefs_nil, map_app. simpl.
  apply list_norepet_append; auto.
  constructor. simpl; tauto. constructor.
  red; simpl; intros. destruct H0; try tauto. subst y.
  apply filter_globdefs_domain in H. rewrite ISF.remove_iff in H. intuition.
Qed.

End TRANSFORMATION.

Theorem transf_program_match:
  forall p tp, transform_program p = OK tp -> match_prog p tp.
Proof.
  unfold transform_program; intros p tp TR. set (pm := prog_defmap p) in *.
  destruct (used_globals p pm) as [u|] eqn:U; try discriminate.
  destruct (IS.for_all (global_defined p pm) u) eqn:DEF; inv TR.
  exists u; split.
  apply used_globals_valid; auto.
  constructor; simpl; auto.
  intros. unfold prog_defmap; simpl. apply filter_globdefs_map.
  apply filter_globdefs_unique_names.
Qed.

(** * Semantic preservation *)

Section SOUNDNESS.

Variable p: program.
Variable tp: program.
Variable used: IS.t.
Hypothesis USED_VALID: valid_used_set p used.
Hypothesis TRANSF: match_prog_1 used p tp.
Let ge := Genv.globalenv p.
Let tge := Genv.globalenv tp.
Let pm := prog_defmap p.

Definition meminjP_eq : meminj -> Prop :=
  fun f => forall b b' delta, f b = Some (b',delta) ->
                       (b=b' /\ delta = 0).

Definition kept (id: ident) : Prop := IS.In id used.

Lemma kept_closed:
  forall id gd id',
  kept id -> pm!id = Some gd -> ref_def gd id' -> kept id'.
Proof.
  intros. eapply used_closed; eauto.
Qed.

Lemma kept_main:
  kept p.(prog_main).
Proof.
  eapply used_main; eauto.
Qed.

Lemma kept_public:
  forall id, In id p.(prog_public) -> kept id.
Proof.
  intros. eapply used_public; eauto.
Qed.

(** Relating [Genv.find_symbol] operations in the original and transformed program *)

Definition kept_dec : forall id, {kept id} + {~ kept id}.
Proof.
  intros.
  unfold kept.
  apply ISP.In_dec.
Qed.

Definition kept_block (b:block) : Prop :=
  match b with
   |Global id => kept id
   |_ => True
  end.

Definition kept_val (v:val) : Prop :=
  match v with
  |Vptr b _ => kept_block b
  |_ => True
  end.

Inductive kept_vl : list val -> Prop :=
  |kept_vl_nil : kept_vl nil
  |kept_vl_cons : forall vl' v,
      kept_vl vl' -> kept_val v -> kept_vl (v::vl').

Definition kept_regs (rs:regset) :=
 forall r, kept_val rs#r.

Inductive kept_stack : list stackframe -> Prop :=
  |kept_stack_nil : kept_stack nil
  |kept_stack_cons : forall s f res sp pc rs
     (KEPT: forall id, ref_function f id -> kept id)
     (STACKS: kept_stack s)
     (REGS: kept_regs rs)
     (SP: kept_block sp),
      kept_stack (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: s).

Lemma transform_find_symbol_1':
  forall id b,
  Genv.find_symbol ge id = Some b -> kept id -> exists b', Genv.find_symbol tge id = Some b'.
Proof.
  intros.
  assert (A: exists g, (prog_defmap p)!id = Some g).
  { apply prog_defmap_dom. eapply Genv.find_symbol_inversion; eauto. }
  destruct A as (g & P).
  apply Genv.find_symbol_exists with g.
  apply in_prog_defmap.
  erewrite match_prog_def by eauto. rewrite IS.mem_1 by auto. auto.
Qed.

Lemma transform_find_symbol_1:
  forall id b,
    Genv.find_symbol ge id = Some b -> kept id -> Genv.find_symbol tge id = Some b.
Proof.
  intros. exploit transform_find_symbol_1'; eauto.
  intros (b' & H1).
  apply Genv.genv_symb_eq in H.
  apply Genv.genv_symb_eq in H1 as H2.
  subst. auto.
Qed.

Lemma transform_find_symbol_2':
  forall id b,
  Genv.find_symbol tge id = Some b -> kept id /\ exists b', Genv.find_symbol ge id = Some b'.
Proof.
  intros.
  assert (A: exists g, (prog_defmap tp)!id = Some g).
  { apply prog_defmap_dom. eapply Genv.find_symbol_inversion; eauto. }
  destruct A as (g & P).
  erewrite match_prog_def in P by eauto.
  destruct (IS.mem id used) eqn:U; try discriminate.
  split. apply IS.mem_2; auto.
  apply Genv.find_symbol_exists with g.
  apply in_prog_defmap. auto.
Qed.

Lemma transform_find_symbol_2:
  forall id b,
    Genv.find_symbol tge id = Some b -> kept id /\ Genv.find_symbol ge id = Some b.
Proof.
  intros. exploit transform_find_symbol_2'; eauto.
  intros (H1 & b' & H2).
  apply Genv.genv_symb_eq in H.
  apply Genv.genv_symb_eq in H2 as H3.
  subst. auto.
Qed.

(** Injections that preserve used globals. *)

Definition kept_gblock (b:block) : Prop :=
  match b with
    |Global id => kept id
    |_ => False
  end.
(*
Lemma defs_inject: forall i gd,
    kept i-> Genv.find_def ge (Global i) = Some gd ->
    Genv.find_def tge (Global i) = Some gd /\
    (forall id, ref_def gd id -> kept id).
Proof.
  intros.
  Search Genv.find_def.
  apply Genv.find_def_inversion in H0.
  destruct H0.
  Search prog_defmap.
  apply prog_defmap_dom in H0.
  
Record preserves_globals: Prop := {

  defs_rev_inject: forall b gd,
    kept_gblock b-> Genv.find_def tge b = Some gd ->
    Genv.find_def ge b = Some gd
}.
*)
Remark transform_find_symbol_3:
  forall id b b',
  Genv.find_symbol ge id = Some b -> Genv.find_symbol tge id = Some b' ->
  kept id /\ b = b'.
Proof.
  intros. split.
  assert (A: exists g, (prog_defmap p)!id = Some g).
  { apply prog_defmap_dom. eapply Genv.find_symbol_inversion; eauto. }
  assert (B: exists g, (prog_defmap tp)!id = Some g).
  { apply prog_defmap_dom. eapply Genv.find_symbol_inversion; eauto. }
  destruct B.
  exploit match_prog_def; eauto. instantiate (1:= id).
  intro. destruct (IS.mem id used) eqn:?.
  apply IS.mem_2. auto. congruence.
  apply Genv.genv_symb_eq in H.
  apply Genv.genv_symb_eq in H0.
  congruence.
Qed.

(*
Remark transform_find_symbol_4:
  forall id,
  kept id ->
  Genv.find_symbol ge id = Some (Global id) /\ Genv.find_symbol tge id = Some (Global id).
Proof.
  intros.
  Check match_prog_1.
  unfold init_meminj; intros.
  destruct (Genv.invert_symbol ge b) as [id|] eqn:S; try discriminate.
  destruct (Genv.find_symbol tge id) as [b''|] eqn:F; inv H.
  split. auto. exists id. split. apply Genv.invert_find_symbol; auto. auto.
Qed.
*)
(*
Lemma preserves_globals1:
  preserves_globals.
Proof.
  constructor; intros.
- destruct b. inv H. simpl in H.
  assert (pm!i = Some gd).
  { unfold pm; rewrite Genv.find_def_symbol. exists (Global i); auto. }
  assert ((prog_defmap tp)!id = Some gd).
  { erewrite match_prog_def by eauto. rewrite IS.mem_1 by auto. auto. }
  rewrite Genv.find_def_symbol in H3. destruct H3 as (b1 & P & Q).
  fold tge in P.
  exploit init_meminj_eq; eauto. intro.
  apply init_meminjP in H3 as H4. inv H4.
  rewrite P in C. inv C.
  split; auto. split; auto. split; auto.
  intros. eapply kept_closed; eauto.
- exploit init_meminj_invert; eauto. intros (A & id & B & C).
  apply init_meminjP in H as H'. inv H'.
  assert ((prog_defmap tp)!id = Some gd).
  { rewrite Genv.find_def_symbol. exists b'; auto. }
  erewrite match_prog_def in H1 by eauto.
  destruct (IS.mem id used); try discriminate.
  rewrite Genv.find_def_symbol in H1. destruct H1 as (b1 & P & Q).
  fold ge in P. replace b' with b1 by congruence. auto.
Qed.

Lemma globals_symbols_inject:
  forall j, meminj_preserves_globals j -> symbols_inject j ge tge.
Proof.
  intros.
  assert (E1: Genv.genv_public ge = p.(prog_public)).
  { apply Genv.globalenv_public. }
  assert (E2: Genv.genv_public tge = p.(prog_public)).
  { unfold tge; rewrite Genv.globalenv_public. eapply match_prog_public; eauto. }
  split; [|split;[|split]]; intros.
  + simpl; unfold Genv.public_symbol; rewrite E1, E2.
    destruct (Genv.find_symbol tge id) as [b'|] eqn:TFS.
    exploit symbols_inject_3; eauto. intros (FS & INJ). rewrite FS. auto.
    destruct (Genv.find_symbol ge id) as [b|] eqn:FS; auto.
    destruct (in_dec ident_eq id (prog_public p)); simpl; auto.
    exploit symbols_inject_2; eauto.
    eapply kept_public; eauto.
    intros (TFS' & INJ). congruence.
  + exploit symbols_inject_1 ; eauto.
    apply H1. intros. inv H2. inv H4. auto.
  + simpl in *; unfold Genv.public_symbol in H0.
    destruct (Genv.find_symbol ge id) as [b|] eqn:FS; try discriminate.
    rewrite E1 in H0.
    destruct (in_dec ident_eq id (prog_public p)); try discriminate. inv H1.
    exploit symbols_inject_2; eauto.
    eapply kept_public; eauto.
    intros (A & B); exists b1; auto.
  + simpl. unfold Genv.block_is_volatile.
    destruct (Genv.find_var_info ge b1) as [gv|] eqn:V1.
    rewrite Genv.find_var_info_iff in V1.
    exploit defs_inject; eauto. intros (A & B & C & D). subst.
    rewrite <- Genv.find_var_info_iff in A. rewrite A; auto.
    destruct (Genv.find_var_info tge b2) as [gv|] eqn:V2; auto.
    rewrite Genv.find_var_info_iff in V2.
    apply meminjP in H0 as H1. inv H1.
    exploit defs_rev_inject; eauto. intros (A & B).
    rewrite <- Genv.find_var_info_iff in A. congruence.
    auto.
Qed.
Lemma symbol_address_inject:
  forall j id ofs,
  meminj_preserves_globals j -> kept id ->
  Val.inject j (Genv.symbol_address ge id ofs) (Genv.symbol_address tge id ofs).
Proof.
  intros. unfold Genv.symbol_address. destruct (Genv.find_symbol ge id) as [b|] eqn:FS; auto.
  exploit symbols_inject_2; eauto. intros (TFS & INJ). rewrite TFS.
  econstructor; eauto. rewrite Ptrofs.add_zero; auto.
Qed.
*)
(** Semantic preservation *)

Definition stack_eq (m1 m2 : mem) : Prop :=
  (Mem.stack (Mem.support m1)) = (Mem.stack (Mem.support m2)).

Inductive match_states: state -> state -> Prop :=
  | match_states_regular: forall s f sp pc rs m tm
         (KEPT: forall id, ref_function f id -> kept id)
         (MEMINJ: partial_mem_iff kept_block m tm)
         (STACKS: kept_stack s)
         (SPINJ: kept_block sp)
         (REGINJ : kept_regs rs)
         (MEMSTACK : stack_eq m tm),
      match_states (State s f (Vptr sp Ptrofs.zero) pc rs m)
                   (State s f (Vptr sp Ptrofs.zero) pc rs tm)
  | match_states_call: forall s fd args m tm
         (STACKS: kept_stack s)
         (KEPT: forall id, ref_fundef fd id -> kept id)
         (MEMINJ: partial_mem_iff kept_block m tm)
         (MEMSTACK : stack_eq m tm)
         (ARGS: kept_vl args),
      match_states (Callstate s fd args m)
                   (Callstate s fd args tm)
  | match_states_return: forall s res m tm
         (STACKS: kept_stack s)
         (RESINJ: kept_val res)
         (MEMINJ: partial_mem_iff kept_block m tm)
         (MEMSTACK : stack_eq m tm),
      match_states (Returnstate s res m)
                   (Returnstate s res tm).

Lemma external_call_inject:
  forall ef vargs m1 t vres m2 m1',
  external_call ef ge vargs m1 t vres m2 ->
  partial_mem_iff kept_block m1 m1' ->
  stack_eq m1 m1' ->
  kept_vl vargs ->
  exists m2',
    external_call ef tge vargs m1' t vres m2'
    /\ partial_mem_iff kept_block m2 m2'
(*    /\ Mem.unchanged_on (loc_unmapped f) m1 m2
    /\ Mem.unchanged_on (loc_out_of_reach f m1) m1' m2' *)
    /\ stack_eq m2 m2'.
Proof.
  Admitted.
(*
  intros. eapply external_call_mem_inject_gen; eauto.
  apply globals_symbols_inject; auto.
*)
(*
Lemma find_function_inject:
  forall ros rs fd,
  find_function ge ros rs = Some fd ->
  match ros with inl r => kept_regs rs | inr id => kept id end ->
  find_function tge ros rs = Some fd /\ (forall id, ref_fundef fd id -> kept id).
Proof.
 intros. destruct ros as [r|id]; simpl in *.
- exploit Genv.find_funct_inv; eauto. intros (b & R). rewrite R in H.
  rewrite Genv.find_funct_find_funct_ptr in H.
  specialize (H0 r). rewrite R in H0.
  simpl in H0.
  rewrite Genv.find_funct_ptr_iff in H.
  exploit defs_inject; eauto. intros (A & B & C & D).
  subst.
  rewrite <- Genv.find_funct_ptr_iff in A.
  rewrite Genv.find_funct_find_funct_ptr.
  split; auto.
- destruct (Genv.find_symbol ge id) as [b|] eqn:FS; try discriminate.
  exploit symbols_inject_2; eauto. intros (P & Q). rewrite P.
  rewrite Genv.find_funct_ptr_iff in H0.
  exploit defs_inject; eauto. intros (A & B & C & D).
  subst.
  rewrite <- Genv.find_funct_ptr_iff in A.
  auto.
Qed.

Lemma eval_builtin_arg_inject:
  forall rs sp m j rs' m' a v,
  eval_builtin_arg ge (fun r => rs#r) (Vptr sp Ptrofs.zero) m a v ->
  j sp = Some(sp, 0) ->
  meminj_preserves_globals j ->
  regset_inject j rs rs' ->
  Mem.inject j m m' ->
  (forall id, In id (globals_of_builtin_arg a) -> kept id) ->
  exists v',
     eval_builtin_arg tge (fun r => rs'#r) (Vptr sp Ptrofs.zero) m' a v'
  /\ Val.inject j v v'.
Proof.
  induction 1; intros SP GL RS MI K; simpl in K.
- exists rs'#x; split; auto. constructor.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- simpl in H. exploit Mem.load_inject; eauto. rewrite Z.add_0_r.
  intros (v' & A & B). exists v'; auto with barg.
- econstructor; split; eauto with barg. simpl. econstructor; eauto. rewrite Ptrofs.add_zero; auto.
- assert (Val.inject j (Senv.symbol_address ge id ofs) (Senv.symbol_address tge id ofs)).
  { unfold Senv.symbol_address; simpl; unfold Genv.symbol_address.
    destruct (Genv.find_symbol ge id) as [b|] eqn:FS; auto.
    exploit symbols_inject_2; eauto. intros (A & B). rewrite A.
    econstructor; eauto. rewrite Ptrofs.add_zero; auto. }
  exploit Mem.loadv_inject; eauto. intros (v' & A & B). exists v'; auto with barg.
- econstructor; split; eauto with barg.
  unfold Senv.symbol_address; simpl; unfold Genv.symbol_address.
  destruct (Genv.find_symbol ge id) as [b|] eqn:FS; auto.
  exploit symbols_inject_2; eauto. intros (A & B). rewrite A.
  econstructor; eauto. rewrite Ptrofs.add_zero; auto.
- destruct IHeval_builtin_arg1 as (v1' & A1 & B1); eauto using in_or_app.
  destruct IHeval_builtin_arg2 as (v2' & A2 & B2); eauto using in_or_app.
  exists (Val.longofwords v1' v2'); split; auto with barg.
  apply Val.longofwords_inject; auto.
- destruct IHeval_builtin_arg1 as (v1' & A1 & B1); eauto using in_or_app.
  destruct IHeval_builtin_arg2 as (v2' & A2 & B2); eauto using in_or_app.
  econstructor; split; eauto with barg.
  destruct Archi.ptr64; auto using Val.add_inject, Val.addl_inject.
Qed.

Lemma eval_builtin_args_inject:
  forall rs sp m j rs' m' al vl,
  eval_builtin_args ge (fun r => rs#r) (Vptr sp Ptrofs.zero) m al vl ->
  j sp = Some(sp, 0) ->
  meminj_preserves_globals j ->
  regset_inject j rs rs' ->
  Mem.inject j m m' ->
  (forall id, In id (globals_of_builtin_args al) -> kept id) ->
  exists vl',
     eval_builtin_args tge (fun r => rs'#r) (Vptr sp Ptrofs.zero) m' al vl'
  /\ Val.inject_list j vl vl'.
Proof.
  induction 1; intros.
- exists (@nil val); split; constructor.
- simpl in H5.
  exploit eval_builtin_arg_inject; eauto using in_or_app. intros (v1' & A & B).
  destruct IHlist_forall2 as (vl' & C & D); eauto using in_or_app.
  exists (v1' :: vl'); split; constructor; auto.
Qed.
*)

Lemma eval_operation_kept : forall sp op rs args m tm v,
    eval_operation ge (Vptr sp Ptrofs.zero) op rs##args m = Some v ->
    kept_block sp ->
    kept_regs rs ->
    eval_operation tge (Vptr sp Ptrofs.zero) op rs##args tm = Some v
    /\ kept_val v.
Proof.
  Check eval_operation_lessdef.
  intros. split.
  destruct op; simpl in *; eauto.
  

  destruct (rs##args); try congruence.
  destruct (l); try congruence. inv H.
Theorem step_simulation:
  forall S1 t S2, step ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'),
  exists S2', step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; intros; inv MS.

- (* nop *)
  econstructor; split.
  eapply exec_Inop; eauto.
  econstructor; eauto.

- (* op *)
  assert (A :eval_operation tge (Vptr sp0 Ptrofs.zero) op rs##args tm = Some v /\  kept_val v).

  { 
  split.
  destruct op; eauto; simpl in *. admit.
  destruct a; eauto. simpl in *. admit.
  admit (*condition*).
  admit. (*condition*)
  admit.
}
  destruct A.
  econstructor; split. eapply exec_Iop; eauto.
  econstructor; eauto.
  
  admit.
- (* load *)
  assert (A: exists ta,
               eval_addressing tge (Vptr sp0 Ptrofs.zero) addr trs##args = Some ta
            /\ Val.inject j a ta).
  { apply eval_addressing_inj with (ge1 := ge) (sp1 := Vptr sp0 Ptrofs.zero) (vl1 := rs##args).
    intros. apply symbol_address_inject.
    eapply match_stacks_preserves_globals; eauto.
    apply KEPT. red. exists pc, (Iload chunk addr args dst pc'); auto.
    econstructor; eauto.
    apply regs_inject; auto.
    assumption. }
  destruct A as (ta & B & C).
  exploit Mem.loadv_inject; eauto. intros (tv & D & E).
  econstructor; split. eapply exec_Iload; eauto.
  econstructor; eauto. apply set_reg_inject; auto.

- (* store *)
  assert (A: exists ta,
               eval_addressing tge (Vptr sp0 Ptrofs.zero) addr trs##args = Some ta
            /\ Val.inject j a ta).
  { apply eval_addressing_inj with (ge1 := ge) (sp1 := Vptr sp0 Ptrofs.zero) (vl1 := rs##args).
    intros. apply symbol_address_inject. auto.
    eapply match_stacks_preserves_globals; eauto.
    apply KEPT. red. exists pc, (Istore chunk addr args src pc'); auto.
    econstructor; eauto.
    apply regs_inject; auto.
    assumption. }
  destruct A as (ta & B & C).
  exploit Mem.storev_mapped_inject; eauto. intros (tm' & D & E).
  econstructor; split. eapply exec_Istore; eauto.
  econstructor; eauto.
  unfold stack_eq.
  rewrite <- (Mem.support_storev _ _ _ _ _ H1).
  rewrite <- (Mem.support_storev _ _ _ _ _ D).
  congruence.
- (* call *)
  exploit find_function_inject.
  eapply match_stacks_preserves_globals; eauto. eauto.
  destruct ros as [r|id]. eauto. apply KEPT. red. econstructor; econstructor; split; eauto. simpl; auto.
  intros (A & B).
  econstructor; split. eapply exec_Icall; eauto.
  econstructor; eauto.
  econstructor; eauto.
  apply regs_inject; eauto.

- (* tailcall *)
  exploit find_function_inject.
  eapply match_stacks_preserves_globals; eauto. eauto.
  destruct ros as [r|id]. eauto. apply KEPT. red. econstructor; econstructor; split; eauto. simpl; auto.
  intros (A & B).
  exploit Mem.free_parallel_inject; eauto. rewrite ! Z.add_0_r. intros (tm' & C & D).
  assert (stack_eq m' tm').
  unfold stack_eq.
  rewrite (Mem.support_free _ _ _ _ _ C).
  rewrite (Mem.support_free _ _ _ _ _ H2).
  congruence.
  exploit Mem.return_frame_parallel_inject; eauto.
  apply Mem.return_frame_nonempty in H3.
  unfold Mem.empty_stack in *.
  rewrite <- H1. auto.
  intros (tm''& RETURN&INJ').
  exploit Mem.return_frame_parallel_stackeq. apply H3. apply RETURN.
  eauto. intro.
  apply Mem.support_return_frame in H3 as H5.
  apply Mem.support_return_frame in RETURN as E.
  econstructor; split.
  eapply exec_Itailcall; eauto.
  econstructor; eauto.
  eapply regs_inject; eauto.
- (* builtin *)
  exploit eval_builtin_args_inject; eauto.
  eapply match_stacks_preserves_globals; eauto.
  intros. apply KEPT. red. econstructor; econstructor; eauto.
  intros (vargs' & P & Q).
  exploit external_call_inject; eauto.
  eapply match_stacks_preserves_globals; eauto.
  intros (j' & tv & tm' & A & B & C & D & E & F & G & I & J & K).
  econstructor; split.
  eapply exec_Ibuiltin; eauto.
  eapply match_states_regular with (j := j'); eauto.
  eapply match_stacks_incr; eauto.
  apply set_res_inject; auto. apply regset_inject_incr with j; auto.
- (* cond *)
  assert (C: eval_condition cond trs##args tm = Some b).
  { eapply eval_condition_inject; eauto. apply regs_inject; auto. }
  econstructor; split.
  eapply exec_Icond with (pc' := if b then ifso else ifnot); eauto.
  econstructor; eauto.

- (* jumptbl *)
  generalize (REGINJ arg); rewrite H0; intros INJ; inv INJ.
  econstructor; split.
  eapply exec_Ijumptable; eauto.
  econstructor; eauto.

- (* return *)
  exploit Mem.free_parallel_inject; eauto.
  intros (tm' & FREE & INJ1).
  assert (stack_eq m' tm').
  unfold stack_eq.
  rewrite (Mem.support_free _ _ _ _ _ H0).
  rewrite (Mem.support_free _ _ _ _ _ FREE).
  congruence.
  exploit Mem.return_frame_parallel_inject; eauto.
  apply Mem.return_frame_nonempty in H1.
  unfold Mem.empty_stack in *.
  rewrite <- H2. auto.
  intros (tm''& RETURN & INJ2).
  econstructor; split.
  eapply exec_Ireturn; eauto.
  replace (0+0) with 0 in FREE by lia.
  replace (fn_stacksize f + 0) with (fn_stacksize f) in FREE by lia.
  auto.
  econstructor; eauto.
  destruct or; simpl; auto.
  eapply Mem.return_frame_parallel_stackeq; eauto.
- (* internal function *)
  exploit Mem.alloc_frame_parallel_inject; eauto. intro.
  exploit Mem.alloc_parallel_inject; eauto. eauto. apply Z.le_refl. apply Z.le_refl.
  intros (j' & tm' & tstk & C & D & E & F & G).
  assert (STK: stk = Mem.nextblock (Mem.alloc_frame m)) by (eapply Mem.alloc_result; eauto).
  assert (TSTK: tstk = Mem.nextblock (Mem.alloc_frame tm)) by (eapply Mem.alloc_result; eauto).
  assert (MEMINJP' : meminjP_eq j').
  {
    unfold meminjP_eq. intros.
      destruct (eq_block b stk).
      subst b. rewrite F in H1. inv H1.
      split. eapply Mem.stack_eq_nextblock.
      eapply Mem.alloc_frame_parallel_stackeq. auto.
      auto.
      apply G in n. rewrite n in H1.
      apply MEMINJP in H1. auto.
  }
  apply MEMINJP' in F as H1. destruct H1.
  subst tstk.
  assert (STACKS': match_stacks j' s ts).
  { eapply match_stacks_incr; eauto.
    intro.
    symmetry. apply G.
    exploit Mem.nextblock_stack.
    instantiate (1:= (Mem.alloc_frame m)).
    intros (b & path & pos & H1).
    subst. rewrite H1. congruence.
 }
  econstructor; split.
  eapply exec_function_internal; eauto.
  eapply match_states_regular with (j := j'); eauto.
  apply init_regs_inject; auto. apply val_inject_list_incr with j; auto.
  unfold stack_eq.
  eapply Mem.alloc_parallel_stackeq; eauto.
  eapply Mem.alloc_frame_parallel_stackeq; eauto.
- (* external function *)
  exploit external_call_inject; eauto.
  eapply match_stacks_preserves_globals; eauto.
  intros (j' & tres & tm' & A & B & C & D & E & F & G & I & J & K).
  econstructor; split.
  eapply exec_function_external; eauto.
  eapply match_states_return with (j := j'); eauto.
  eapply match_stacks_incr; eauto.
- (* return *)
  inv STACKS. econstructor; split.
  eapply exec_return.
  econstructor; eauto.
  apply set_reg_inject; auto.
Qed.

(** Relating initial memory states *)

(*
Remark genv_find_def_exists:
  forall (F V: Type) (p: AST.program F V) b,
  Plt b (Genv.genv_next (Genv.globalenv p)) ->
  exists gd, Genv.find_def (Genv.globalenv p) b = Some gd.
Proof.
  intros until b.
  set (P := fun (g: Genv.t F V) =>
        Plt b (Genv.genv_next g) -> exists gd, (Genv.genv_defs g)!b = Some gd).
  assert (forall l g, P g -> P (Genv.add_globals g l)).
  { induction l as [ | [id1 g1] l]; simpl; intros.
  - auto.
  - apply IHl. unfold Genv.add_global, P; simpl. intros LT. apply Plt_succ_inv in LT. destruct LT.
  + rewrite PTree.gso. apply H; auto. apply Plt_ne; auto.
  + rewrite H0. rewrite PTree.gss. exists g1; auto. }
  apply H. red; simpl; intros. exfalso; extlia.
Qed.
*)

Lemma init_meminj_invert_strong:
  forall b b' delta,
  init_meminj b = Some(b', delta) ->
  delta = 0 /\
  exists id gd,
     Genv.find_symbol ge id = Some b
  /\ Genv.find_symbol tge id = Some b'
  /\ Genv.find_def ge b = Some gd
  /\ Genv.find_def tge b' = Some gd
  /\ (forall i, ref_def gd i -> kept i).
Proof.
  intros. exploit init_meminj_invert; eauto. intros (A & id & B & C).
  assert (exists gd, (prog_defmap p)!id = Some gd).
  { apply prog_defmap_dom. eapply Genv.find_symbol_inversion; eauto. }
  destruct H0 as [gd DM]. rewrite Genv.find_def_symbol in DM.
  destruct DM as (b'' & P & Q). fold ge in P. rewrite P in B; inv B.
  fold ge in Q. exploit defs_inject. apply init_meminj_preserves_globals.
  eauto. eauto. intros (X & _ & Y & Z). subst.
  split. auto. exists id, gd; auto.
Qed.

Section INIT_MEM.

Variables m tm: mem.
Hypothesis IM: Genv.init_mem p = Some m.
Hypothesis TIM: Genv.init_mem tp = Some tm.

Lemma bytes_of_init_inject:
  forall il,
  (forall id, ref_init il id -> kept id) ->
  list_forall2 (memval_inject init_meminj) (Genv.bytes_of_init_data_list ge il) (Genv.bytes_of_init_data_list tge il).
Proof.
  induction il as [ | i1 il]; simpl; intros.
- constructor.
- apply list_forall2_app.
+ destruct i1; simpl; try (apply inj_bytes_inject).
  induction (Z.to_nat z); simpl; constructor. constructor. auto.
  destruct (Genv.find_symbol ge i) as [b|] eqn:FS.
  assert (kept i). { apply H. red. exists i0; auto with coqlib. }
  exploit symbols_inject_2. apply init_meminj_preserves_globals. eauto. eauto.
  intros (A & B). rewrite A. apply inj_value_inject.
  econstructor; eauto. symmetry; apply Ptrofs.add_zero.
  destruct (Genv.find_symbol tge i) as [b'|] eqn:FS'.
  exploit symbols_inject_3. apply init_meminj_preserves_globals. eauto.
  intros (A & B). congruence.
  apply repeat_Undef_inject_self.
+ apply IHil. intros id [ofs IN]. apply H. exists ofs; auto with coqlib.
Qed.

Lemma Mem_getN_forall2:
  forall (P: memval -> memval -> Prop) c1 c2 i n p,
  list_forall2 P (Mem.getN n p c1) (Mem.getN n p c2) ->
  p <= i -> i < p + Z.of_nat n ->
  P (ZMap.get i c1) (ZMap.get i c2).
Proof.
  induction n; simpl Mem.getN; intros.
- simpl in H1. extlia.
- inv H. rewrite Nat2Z.inj_succ in H1. destruct (zeq i p0).
+ congruence.
+ apply IHn with (p0 + 1); auto. lia. lia.
Qed.

Lemma init_mem_inj_1:
  Mem.mem_inj init_meminj m tm.
Proof.
  intros; constructor; intros.
- exploit init_meminj_invert_strong; eauto. intros (A & id & gd & B & C & D & E & F).
  exploit (Genv.init_mem_characterization_gen p); eauto.
  exploit (Genv.init_mem_characterization_gen tp); eauto.
  destruct gd as [f|v].
+ intros (P2 & Q2) (P1 & Q1).
  apply Q1 in H0. destruct H0. subst.
  apply Mem.perm_cur. auto.
+ intros (P2 & Q2 & R2 & S2) (P1 & Q1 & R1 & S1).
  apply Q1 in H0. destruct H0. subst.
  apply Mem.perm_cur. eapply Mem.perm_implies; eauto.
  apply P2. lia.
- exploit init_meminj_invert; eauto. intros (A & id & B & C).
  subst delta. apply Z.divide_0_r.
- exploit init_meminj_invert_strong; eauto. intros (A & id & gd & B & C & D & E & F).
  exploit (Genv.init_mem_characterization_gen p); eauto.
  exploit (Genv.init_mem_characterization_gen tp); eauto.
  destruct gd as [f|v].
+ intros (P2 & Q2) (P1 & Q1).
  apply Q1 in H0. destruct H0; discriminate.
+ intros (P2 & Q2 & R2 & S2) (P1 & Q1 & R1 & S1).
  apply Q1 in H0. destruct H0.
  assert (NO: gvar_volatile v = false).
  { unfold Genv.perm_globvar in H1. destruct (gvar_volatile v); auto. inv H1. }
Local Transparent Mem.loadbytes.
  generalize (S1 NO). unfold Mem.loadbytes. destruct Mem.range_perm_dec; intros E1; inv E1.
  generalize (S2 NO). unfold Mem.loadbytes. destruct Mem.range_perm_dec; intros E2; inv E2.
  rewrite Z.add_0_r.
  apply Mem_getN_forall2 with (p := 0) (n := Z.to_nat (init_data_list_size (gvar_init v))).
  rewrite H3, H4. apply bytes_of_init_inject. auto.
  lia.
  rewrite Z2Nat.id by (apply Z.ge_le; apply init_data_list_size_pos). lia.
Qed.

Lemma init_mem_inj_2:
  Mem.inject init_meminj m tm.
Proof.
  constructor; intros.
- apply init_mem_inj_1.
- destruct (init_meminj b) as [[b' delta]|] eqn:INJ; auto.
  elim H. exploit init_meminj_invert; eauto. intros (A & id & B & C).
  eapply Genv.find_symbol_not_fresh; eauto.
- exploit init_meminj_invert; eauto. intros (A & id & B & C).
  eapply Genv.find_symbol_not_fresh; eauto.
- red; intros.
  exploit init_meminj_invert. eexact H0. intros (A1 & id1 & B1 & C1).
  exploit init_meminj_invert. eexact H1. intros (A2 & id2 & B2 & C2).
  destruct (ident_eq id1 id2). congruence. left; eapply Genv.global_addresses_distinct; eauto.
- exploit init_meminj_invert; eauto. intros (A & id & B & C). subst delta.
  split. lia. generalize (Ptrofs.unsigned_range_2 ofs). lia.
- exploit init_meminj_invert_strong; eauto. intros (A & id & gd & B & C & D & E & F).
  exploit (Genv.init_mem_characterization_gen p); eauto.
  exploit (Genv.init_mem_characterization_gen tp); eauto.
  destruct gd as [f|v].
+ intros (meminjP_eq & Q2) (P1 & Q1).
  apply Q2 in H0. destruct H0. subst. replace ofs with 0 by lia.
  left; apply Mem.perm_cur; auto.
+ intros (meminjP_eq & Q2 & R2 & S2) (P1 & Q1 & R1 & S1).
  apply Q2 in H0. destruct H0. subst.
  left. apply Mem.perm_cur. eapply Mem.perm_implies; eauto.
  apply P1. lia.
Qed.

End INIT_MEM.

Lemma init_mem_exists:
  forall m, Genv.init_mem p = Some m ->
  exists tm, Genv.init_mem tp = Some tm.
Proof.
  intros. apply Genv.init_mem_exists.
  intros.
  assert (P: (prog_defmap tp)!id = Some (Gvar v)).
  { eapply prog_defmap_norepet; eauto. eapply match_prog_unique; eauto. }
  rewrite (match_prog_def _ _ _ TRANSF) in P. destruct (IS.mem id used) eqn:U; try discriminate.
  exploit Genv.init_mem_inversion; eauto. apply in_prog_defmap; eauto. intros [AL FV].
  split. auto.
  intros. exploit FV; eauto. intros (b & FS).
  apply transform_find_symbol_1 with b; auto.
  apply kept_closed with id (Gvar v).
  apply IS.mem_2; auto. auto. red. red. exists o; auto.
Qed.

Theorem init_mem_inject:
  forall m,
  Genv.init_mem p = Some m ->
  exists tm, Genv.init_mem tp = Some tm /\ Mem.inject (init_meminj) m tm.
Proof.
  intros.
  exploit init_mem_exists; eauto. intros [tm INIT].
  exists tm.
  split. auto.
  eapply init_mem_inj_2; eauto.
(*  apply init_meminj_preserves_globals. *)
Qed.

Lemma transf_initial_states:
  forall S1, initial_state p S1 -> exists S2, initial_state tp S2 /\ match_states S1 S2.
Proof.
  intros. inv H. exploit init_mem_inject; eauto. intros (tm & A & B).
  generalize init_meminj_preserves_globals. intro.
  exploit symbols_inject_2. eauto. eapply kept_main. eexact H1.
  intros (P & Q).
  rewrite Genv.find_funct_ptr_iff in H2.
  exploit defs_inject. eauto. eexact Q. exact H2.
  intros (R & S & T & L). subst.
  rewrite <- Genv.find_funct_ptr_iff in R.
  exists (Callstate nil f nil tm); split.
  econstructor; eauto.
  fold tge. erewrite match_prog_main by eauto. auto.
  econstructor; eauto.
  constructor. auto.
  intro. intros.   apply init_meminj_invert in H4.
  destruct H4 as (H4 & id & H5 & H6).
  apply Genv.genv_symb_eq in H5.
  apply Genv.genv_symb_eq in H6.
  subst. auto.
  apply Genv.init_mem_stack in H0.
  apply Genv.init_mem_stack in A.
  congruence.
Qed.

Lemma transf_final_states:
  forall S1 S2 r,
  match_states S1 S2 -> final_state S1 r -> final_state S2 r.
Proof.
  intros. inv H0. inv H. inv STACKS. inv RESINJ. constructor.
Qed.

Lemma transf_program_correct_1:
  forward_simulation (semantics p) (semantics tp).
Proof.
  intros.
  eapply forward_simulation_step.
  exploit globals_symbols_inject. apply init_meminj_preserves_globals. intros [A B]. exact A.
  eexact transf_initial_states.
  eexact transf_final_states.
  eexact step_simulation.
Qed.

End SOUNDNESS.

Theorem transf_program_correct:
  forall p tp, match_prog p tp -> forward_simulation (semantics p) (semantics tp).
Proof.
  intros p tp (used & A & B).  apply transf_program_correct_1 with used; auto.
Qed.

(** * Commutation with linking *)

Remark link_def_either:
  forall (gd1 gd2 gd: globdef fundef unit),
  link_def gd1 gd2 = Some gd -> gd = gd1 \/ gd = gd2.
Proof with (try discriminate).
  intros until gd.
Local Transparent Linker_def Linker_fundef Linker_varinit Linker_vardef Linker_unit.
  destruct gd1 as [f1|v1], gd2 as [f2|v2]...
(* Two fundefs *)
  destruct f1 as [f1|ef1], f2 as [f2|ef2]; simpl...
  destruct ef2; intuition congruence.
  destruct ef1; intuition congruence.
  destruct (external_function_eq ef1 ef2); intuition congruence.
(* Two vardefs *)
  simpl. unfold link_vardef. destruct v1 as [info1 init1 ro1 vo1], v2 as [info2 init2 ro2 vo2]; simpl.
  destruct (link_varinit init1 init2) as [init|] eqn:LI...
  destruct (eqb ro1 ro2) eqn:RO...
  destruct (eqb vo1 vo2) eqn:VO...
  simpl.
  destruct info1, info2.
  assert (EITHER: init = init1 \/ init = init2).
  { revert LI. unfold link_varinit.
    destruct (classify_init init1), (classify_init init2); intro EQ; inv EQ; auto.
    destruct (zeq sz (Z.max sz0 0 + 0)); inv H0; auto.
    destruct (zeq sz (init_data_list_size il)); inv H0; auto.
    destruct (zeq sz (init_data_list_size il)); inv H0; auto. }
  apply eqb_prop in RO. apply eqb_prop in VO.
  intro EQ; inv EQ. destruct EITHER; subst init; auto.
Qed.

Remark used_not_defined:
  forall p used id,
  valid_used_set p used ->
  (prog_defmap p)!id = None ->
  IS.mem id used = false \/ id = prog_main p.
Proof.
  intros. destruct (IS.mem id used) eqn:M; auto.
  exploit used_defined; eauto using IS.mem_2. intros [A|A]; auto.
  apply prog_defmap_dom in A. destruct A as [g E]; congruence.
Qed.

Remark used_not_defined_2:
  forall p used id,
  valid_used_set p used ->
  id <> prog_main p ->
  (prog_defmap p)!id = None ->
  ~IS.In id used.
Proof.
  intros. exploit used_not_defined; eauto. intros [A|A].
  red; intros; apply IS.mem_1 in H2; congruence.
  congruence.
Qed.

Lemma link_valid_used_set:
  forall p1 p2 p used1 used2,
  link p1 p2 = Some p ->
  valid_used_set p1 used1 ->
  valid_used_set p2 used2 ->
  valid_used_set p (IS.union used1 used2).
Proof.
  intros until used2; intros L V1 V2.
  destruct (link_prog_inv _ _ _ L) as (X & Y & Z).
  rewrite Z; clear Z; constructor.
- intros. rewrite ISF.union_iff in H. rewrite ISF.union_iff.
  rewrite prog_defmap_elements, PTree.gcombine in H0.
  destruct (prog_defmap p1)!id as [gd1|] eqn:GD1;
  destruct (prog_defmap p2)!id as [gd2|] eqn:GD2;
  simpl in H0; try discriminate.
+ (* common definition *)
  exploit Y; eauto. intros (PUB1 & PUB2 & _).
  exploit link_def_either; eauto. intros [EQ|EQ]; subst gd.
* left. eapply used_closed. eexact V1. eapply used_public. eexact V1. eauto. eauto. auto.
* right. eapply used_closed. eexact V2. eapply used_public. eexact V2. eauto. eauto. auto.
+ (* left definition *)
  inv H0. destruct (ISP.In_dec id used1).
* left; eapply used_closed; eauto.
* assert (IS.In id used2) by tauto.
  exploit used_defined. eexact V2. eauto. intros [A|A].
  exploit prog_defmap_dom; eauto. intros [g E]; congruence.
  elim n. rewrite A, <- X. eapply used_main; eauto.
+ (* right definition *)
  inv H0. destruct (ISP.In_dec id used2).
* right; eapply used_closed; eauto.
* assert (IS.In id used1) by tauto.
  exploit used_defined. eexact V1. eauto. intros [A|A].
  exploit prog_defmap_dom; eauto. intros [g E]; congruence.
  elim n. rewrite A, X. eapply used_main; eauto.
+ (* no definition *)
  auto.
- simpl. rewrite ISF.union_iff; left; eapply used_main; eauto.
- simpl. intros id. rewrite in_app_iff, ISF.union_iff.
  intros [A|A]; [left|right]; eapply used_public; eauto.
- intros. rewrite ISF.union_iff in H.
  destruct (ident_eq id (prog_main p1)).
+ right; assumption.
+ assert (E: exists g, link_prog_merge (prog_defmap p1)!id (prog_defmap p2)!id = Some g).
  { destruct (prog_defmap p1)!id as [gd1|] eqn:GD1;
    destruct (prog_defmap p2)!id as [gd2|] eqn:GD2; simpl.
  * apply Y with id; auto.
  * exists gd1; auto.
  * exists gd2; auto.
  * eapply used_not_defined_2 in GD1; [ | eauto | congruence ].
    eapply used_not_defined_2 in GD2; [ | eauto | congruence ].
    tauto.
  }
  destruct E as [g LD].
  left. unfold prog_defs_names; simpl.
  change id with (fst (id, g)). apply in_map. apply PTree.elements_correct.
  rewrite PTree.gcombine; auto.
Qed.

Theorem link_match_program:
  forall p1 p2 tp1 tp2 p,
  link p1 p2 = Some p ->
  match_prog p1 tp1 -> match_prog p2 tp2 ->
  exists tp, link tp1 tp2 = Some tp /\ match_prog p tp.
Proof.
  intros. destruct H0 as (used1 & A1 & B1). destruct H1 as (used2 & A2 & B2).
  destruct (link_prog_inv _ _ _ H) as (U & V & W).
  econstructor; split.
- apply link_prog_succeeds.
+ rewrite (match_prog_main _ _ _ B1), (match_prog_main _ _ _ B2). auto.
+ intros.
  rewrite (match_prog_def _ _ _ B1) in H0.
  rewrite (match_prog_def _ _ _ B2) in H1.
  destruct (IS.mem id used1) eqn:U1; try discriminate.
  destruct (IS.mem id used2) eqn:U2; try discriminate.
  edestruct V as (X & Y & gd & Z); eauto.
  split. rewrite (match_prog_public _ _ _ B1); auto.
  split. rewrite (match_prog_public _ _ _ B2); auto.
  congruence.
- exists (IS.union used1 used2); split.
+ eapply link_valid_used_set; eauto.
+ rewrite W. constructor; simpl; intros.
* eapply match_prog_main; eauto.
* rewrite (match_prog_public _ _ _ B1), (match_prog_public _ _ _ B2). auto.
* rewrite ! prog_defmap_elements, !PTree.gcombine by auto.
  rewrite (match_prog_def _ _ _ B1 id), (match_prog_def _ _ _ B2 id).
  rewrite ISF.union_b.
{
  destruct (prog_defmap p1)!id as [gd1|] eqn:GD1;
  destruct (prog_defmap p2)!id as [gd2|] eqn:GD2.
- (* both defined *)
  exploit V; eauto. intros (PUB1 & PUB2 & _).
  assert (EQ1: IS.mem id used1 = true) by (apply IS.mem_1; eapply used_public; eauto).
  assert (EQ2: IS.mem id used2 = true) by (apply IS.mem_1; eapply used_public; eauto).
  rewrite EQ1, EQ2; auto.
- (* left defined *)
  exploit used_not_defined; eauto. intros [A|A].
  rewrite A, orb_false_r. destruct (IS.mem id used1); auto.
  replace (IS.mem id used1) with true. destruct (IS.mem id used2); auto.
  symmetry. apply IS.mem_1. rewrite A, <- U. eapply used_main; eauto.
- (* right defined *)
  exploit used_not_defined. eexact A1. eauto. intros [A|A].
  rewrite A, orb_false_l. destruct (IS.mem id used2); auto.
  replace (IS.mem id used2) with true. destruct (IS.mem id used1); auto.
  symmetry. apply IS.mem_1. rewrite A, U. eapply used_main; eauto.
- (* none defined *)
  destruct (IS.mem id used1), (IS.mem id used2); auto.
}
* intros. apply PTree.elements_keys_norepet.
Qed.

Instance TransfSelectionLink : TransfLink match_prog := link_match_program.

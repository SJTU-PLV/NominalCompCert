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

(** Recognition of tail calls: correctness proof *)

Require Import Coqlib Maps Integers AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Registers RTL Conventions Tailcall.

(** * Syntactic properties of the code transformation *)

(** ** Measuring the number of instructions eliminated *)

(** The [return_measure c pc] function counts the number of instructions
  eliminated by the code transformation, where [pc] is the successor
  of a call turned into a tailcall.  This is the length of the
  move/nop/return sequence recognized by the [is_return] boolean function.
*)

Fixpoint return_measure_rec (n: nat) (c: code) (pc: node)
                            {struct n}: nat :=
  match n with
  | O => O
  | S n' =>
      match c!pc with
      | Some(Inop s) => S(return_measure_rec n' c s)
      | Some(Iop op args dst s) => S(return_measure_rec n' c s)
      | _ => O
      end
  end.

Definition return_measure (c: code) (pc: node) :=
  return_measure_rec niter c pc.

Lemma return_measure_bounds:
  forall f pc, (return_measure f pc <= niter)%nat.
Proof.
  intro f.
  assert (forall n pc, (return_measure_rec n f pc <= n)%nat).
    induction n; intros; simpl.
    lia.
    destruct (f!pc); try lia.
    destruct i; try lia.
    generalize (IHn n0). lia.
    generalize (IHn n0). lia.
  intros. unfold return_measure. apply H.
Qed.

Remark return_measure_rec_incr:
  forall f n1 n2 pc,
  (n1 <= n2)%nat ->
  (return_measure_rec n1 f pc <= return_measure_rec n2 f pc)%nat.
Proof.
  induction n1; intros; simpl.
  lia.
  destruct n2. extlia. assert (n1 <= n2)%nat by lia.
  simpl. destruct f!pc; try lia. destruct i; try lia.
  generalize (IHn1 n2 n H0). lia.
  generalize (IHn1 n2 n H0). lia.
Qed.

Lemma is_return_measure_rec:
  forall f n n' pc r,
  is_return n f pc r = true -> (n <= n')%nat ->
  return_measure_rec n f.(fn_code) pc = return_measure_rec n' f.(fn_code) pc.
Proof.
  induction n; simpl; intros.
  congruence.
  destruct n'. extlia. simpl.
  destruct (fn_code f)!pc; try congruence.
  destruct i; try congruence.
  decEq. apply IHn with r. auto. lia.
  destruct (is_move_operation o l); try congruence.
  destruct (Reg.eq r r1); try congruence.
  decEq. apply IHn with r0. auto. lia.
Qed.

(** ** Relational characterization of the code transformation *)

(** The [is_return_spec] characterizes the instruction sequences
  recognized by the [is_return] boolean function.  *)

Inductive is_return_spec (f:function): node -> reg -> Prop :=
  | is_return_none: forall pc r,
      f.(fn_code)!pc = Some(Ireturn None) ->
      is_return_spec f pc r
  | is_return_some: forall pc r,
      f.(fn_code)!pc = Some(Ireturn (Some r)) ->
      is_return_spec f pc r
  | is_return_nop: forall pc r s,
      f.(fn_code)!pc = Some(Inop s) ->
      is_return_spec f s r ->
      (return_measure f.(fn_code) s < return_measure f.(fn_code) pc)%nat ->
      is_return_spec f pc r
  | is_return_move: forall pc r r' s,
      f.(fn_code)!pc = Some(Iop Omove (r::nil) r' s) ->
      is_return_spec f s r' ->
      (return_measure f.(fn_code) s < return_measure f.(fn_code) pc)%nat ->
     is_return_spec f pc r.

Lemma is_return_charact:
  forall f n pc rret,
  is_return n f pc rret = true -> (n <= niter)%nat ->
  is_return_spec f pc rret.
Proof.
  induction n; intros.
  simpl in H. congruence.
  generalize H. simpl.
  caseEq ((fn_code f)!pc); try congruence.
  intro i. caseEq i; try congruence.
  intros s; intros. eapply is_return_nop; eauto. eapply IHn; eauto. lia.
  unfold return_measure.
  rewrite <- (is_return_measure_rec f (S n) niter pc rret); auto.
  rewrite <- (is_return_measure_rec f n niter s rret); auto.
  simpl. rewrite H2. lia. lia.

  intros op args dst s EQ1 EQ2.
  caseEq (is_move_operation op args); try congruence.
  intros src IMO. destruct (Reg.eq rret src); try congruence.
  subst rret. intro.
  exploit is_move_operation_correct; eauto. intros [A B]. subst.
  eapply is_return_move; eauto. eapply IHn; eauto. lia.
  unfold return_measure.
  rewrite <- (is_return_measure_rec f (S n) niter pc src); auto.
  rewrite <- (is_return_measure_rec f n niter s dst); auto.
  simpl. rewrite EQ2. lia. lia.

  intros or EQ1 EQ2. destruct or; intros.
  assert (r = rret). eapply proj_sumbool_true; eauto. subst r.
  apply is_return_some; auto.
  apply is_return_none; auto.
Qed.

(** The [transf_instr_spec] predicate relates one instruction in the
  initial code with its possible transformations in the optimized code. *)

Inductive transf_instr_spec (f: function): instruction -> instruction -> Prop :=
  | transf_instr_tailcall: forall sig ros args res s,
      f.(fn_stacksize) = 0 ->
      is_return_spec f s res ->
      transf_instr_spec f (Icall sig ros args res s) (Itailcall sig ros args)
  | transf_instr_default: forall i,
      transf_instr_spec f i i.

Lemma transf_instr_charact:
  forall f pc instr,
  f.(fn_stacksize) = 0 ->
  transf_instr_spec f instr (transf_instr f pc instr).
Proof.
  intros. unfold transf_instr. destruct instr; try constructor.
  destruct (is_return niter f n r && tailcall_is_possible s &&
            rettype_eq (sig_res s) (sig_res (fn_sig f))) eqn:B.
- InvBooleans. eapply transf_instr_tailcall; eauto. eapply is_return_charact; eauto.
- constructor.
Qed.

Lemma transf_instr_lookup:
  forall f pc i,
  f.(fn_code)!pc = Some i ->
  exists i',  (transf_function f).(fn_code)!pc = Some i' /\ transf_instr_spec f i i'.
Proof.
  intros. unfold transf_function.
  destruct (zeq (fn_stacksize f) 0).
  simpl. rewrite PTree.gmap. rewrite H. simpl.
  exists (transf_instr f pc i); split. auto. apply transf_instr_charact; auto.
  exists i; split. auto. constructor.
Qed.

(** * Semantic properties of the code transformation *)

(** ** The ``less defined than'' relation between register states *)

(** A call followed by a return without an argument can be turned
  into a tail call.  In this case, the original function returns
  [Vundef], while the transformed function can return any value.
  We account for this situation by using the ``less defined than''
  relation between values and between memory states.  We need to
  extend it pointwise to register states. *)

Lemma regs_lessdef_init_regs:
  forall params vl vl',
  Val.lessdef_list vl vl' ->
  regs_lessdef (init_regs vl params) (init_regs vl' params).
Proof.
  induction params; intros.
  simpl. red; intros. rewrite Regmap.gi. constructor.
  simpl. inv H.   red; intros. rewrite Regmap.gi. constructor.
  apply set_reg_lessdef. auto. auto.
Qed.

(** * Proof of semantic preservation *)

Definition match_prog (p tp: RTL.program) :=
  match_program (fun cu f tf => tf = transf_fundef f) eq p tp.

Lemma transf_program_match:
  forall p, match_prog p (transf_program p).
Proof.
  intros. apply match_transform_program; auto.
Qed.

Section PRESERVATION.

Variable fn_stack_requirements : ident -> Z.
Variable prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_transf TRANSL).

Lemma functions_translated:
  forall (v: val) (f: RTL.fundef),
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (transf_fundef f).
Proof (Genv.find_funct_transf TRANSL).

Lemma funct_ptr_translated:
  forall (b: block) (f: RTL.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  Genv.find_funct_ptr tge b = Some (transf_fundef f).
Proof (Genv.find_funct_ptr_transf TRANSL).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_transf TRANSL).

Lemma sig_preserved:
  forall f, funsig (transf_fundef f) = funsig f.
Proof.
  destruct f; auto. simpl. unfold transf_function.
  destruct (zeq (fn_stacksize f) 0); auto.
Qed.

Lemma stacksize_preserved:
  forall f, fn_stacksize (transf_function f) = fn_stacksize f.
Proof.
  unfold transf_function. intros.
  destruct (zeq (fn_stacksize f) 0); auto.
Qed.

Lemma find_function_translated:
  forall ros rs rs' f,
  find_function ge ros rs = Some f ->
  regs_lessdef rs rs' ->
  find_function tge ros rs' = Some (transf_fundef f).
Proof.
  intros until f; destruct ros; simpl.
  intros.
  assert (rs'#r = rs#r).
    exploit Genv.find_funct_inv; eauto. intros [b EQ].
    generalize (H0 r). rewrite EQ. intro LD. inv LD. auto.
  rewrite H1. apply functions_translated; auto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge i); intros.
  apply funct_ptr_translated; auto.
  discriminate.
Qed.

Lemma find_function_id_preserved:
  forall ros rs rs' id,
  ros_is_function ge ros rs id ->
  regs_lessdef rs rs' ->
  ros_is_function tge ros rs' id.
Proof.
  unfold ros_is_function. intros.
  destruct ros.
  - destruct H as (b & o & RS & FS).
  specialize (H0 r). rewrite RS in H0; inv H0.
  eexists; eexists; split; eauto.
  rewrite symbols_preserved. auto.
  - auto.
Qed.

(** Consider an execution of a call/move/nop/return sequence in the
  original code and the corresponding tailcall in the transformed code.
  The transition sequences are of the following form
  (left: original code, right: transformed code).
  [f] is the calling function and [fd] the called function.
<<
     State stk f (Icall instruction)       State stk' f' (Itailcall)

     Callstate (frame::stk) fd args        Callstate stk' fd' args'
            .                                       .
            .                                       .
            .                                       .
     Returnstate (frame::stk) res          Returnstate stk' res'

     State stk f (move/nop/return seq)
            .
            .
            .
     State stk f (return instr)

     Returnstate stk res
>>
The simulation invariant must therefore account for two kinds of
mismatches between the transition sequences:
- The call stack of the original program can contain more frames
  than that of the transformed program (e.g. [frame] in the example above).
- The regular states corresponding to executing the move/nop/return
  sequence must all correspond to the single [Returnstate stk' res']
  state of the transformed program.

We first define the simulation invariant between call stacks.
The first two cases are standard, but the third case corresponds
to a frame that was eliminated by the transformation. *)

Inductive match_stackframes: nat -> list nat -> list stackframe -> list stackframe -> Prop :=
  | match_stackframes_nil:
      match_stackframes 0 nil nil nil
  | match_stackframes_normal: forall n l stk stk' res sp pc rs rs' f,
      match_stackframes n l stk stk' ->
      regs_lessdef rs rs' ->
      match_stackframes 0 ((S n)::l)
        (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk)
        (Stackframe res (transf_function f) (Vptr sp Ptrofs.zero) pc rs' :: stk')
  | match_stackframes_tail: forall n l stk stk' res sp pc rs f,
      match_stackframes n l stk stk' ->
      is_return_spec f pc res ->
      f.(fn_stacksize) = 0 ->
      match_stackframes (S n) l
        (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk)
        stk'.

Section TAKEDROP.
  Context {A: Type}.

  Fixpoint take (n: nat) (l: list A) : option (list A) :=
    match n with
    | O => Some nil
    | S m => match l with
            | h::t =>
               match take m t with
                 Some r => Some (h::r)
               | None => None
               end
            | _ => None
            end
    end.

  Fixpoint drop (n: nat) (l: list A) : list A :=
    match n with
    | O => l
    | S m => drop m (tl l)
    end.

  Lemma take_drop:
    forall n l t,
      take n l = Some t ->
      l = t ++ drop n l.
  Proof.
    induction n; simpl; intros; eauto. inv H. reflexivity.
    repeat destr_in H. simpl. f_equal. eauto.
  Qed.

  Lemma take_succeeds:
    forall n l,
      (n <= length l)%nat ->
      exists t, take n l = Some t.
  Proof.
    induction n; simpl; intros; eauto.
    destr; simpl in *. lia.
    edestruct (IHn l0) as (t & EQ). lia.
    rewrite EQ. eauto.
  Qed.

  Lemma take_succeeds_inv:
    forall n l t,
      take n l = Some t ->
      (n <= length l)%nat.
  Proof.
    induction n; simpl; intros; eauto. lia.
    repeat destr_in H.
    apply IHn in Heqo. simpl. lia.
  Qed.

  Lemma drop_length:
    forall n l,
      (n <= length l)%nat ->
      length (drop n l) = (length l - n)%nat.
  Proof.
    induction n; simpl; intros; eauto. lia.
    destruct l; simpl in *; try lia.
    rewrite IHn; lia.
  Qed.

  Lemma take_length:
    forall n l t,
      take n l = Some t ->
      length t = n.
  Proof.
    induction n; simpl; intros; eauto. inv H; auto.
    repeat destr_in H. simpl. erewrite IHn; eauto.
  Qed.

  Variable P: A -> Prop.

  Lemma take_forall:
    forall n l t,
      Forall P l ->
      take n l = Some t ->
      Forall P t.
  Proof.
    intros.
    rewrite (take_drop _ _ _ H0) in H.
    rewrite Forall_forall in H.
    rewrite Forall_forall. intros; apply H. rewrite in_app. auto.
  Qed.

  Lemma drop_forall:
    forall n l,
      Forall P l ->
      Forall P (drop n l).
  Proof.
    induction n; simpl; intros; eauto.
    apply IHn. inv H; simpl; auto.
  Qed.

End TAKEDROP.

Inductive tc_sizes : list nat -> Mem.stackadt -> Mem.stackadt -> Prop :=
| sizes_nil: tc_sizes nil nil nil
| sizes_cons l s1 s2 t1 n t2:
    tc_sizes l (drop (S n) s1) s2 ->
    take (S n) s1 = Some t1 ->
    Mem.stack_size_vm t1 = Mem.size_of_all_frames t2 ->
    tc_sizes (S n::l) s1 (t2 :: s2).

Lemma tc_sizes_upstar:
  forall n g s1 s2,
    tc_sizes (n :: g) s1 s2 ->
    tc_sizes (S n :: g) ((nil) :: s1) s2.
Proof.
  intros n g s1 s2 SZ.
  inv SZ. simpl in *. repeat destr_in H2.
  econstructor; simpl; auto. rewrite Heqo. eauto.
  auto.
Qed.

Lemma tc_sizes_upstar':
  forall n g s1 s2 t f,
    tc_sizes (n :: g) s1 (t::s2) ->
    tc_sizes (S n :: g) ((f::nil) :: s1) ((f::t)::s2).
Proof.
  intros n g s1 s2 f l SZ.
  inv SZ. simpl in *. repeat destr_in H5.
  econstructor; simpl; auto. rewrite Heqo. eauto.
  simpl in *. lia.
Qed.

Lemma tc_sizes_up:
  forall g s1 s2,
    tc_sizes g s1 s2 ->
    tc_sizes (1%nat :: g) ((nil) :: s1) ((nil) :: s2).
Proof.
  intros g s1 s2 SZ. econstructor; simpl; eauto.
Qed.

Lemma tc_sizes_record:
  forall g t1 s1 t2 s2 f
    (SZ: tc_sizes g (t1 :: s1) (t2 :: s2)),
    tc_sizes g ((f::t1):: s1) ((f::t2) :: s2).
Proof.
  intros. inv SZ.
  simpl in *. repeat destr_in H4.
  econstructor; simpl; auto. rewrite Heqo. eauto.
  simpl in *. lia.
Qed.
(* to mem*)
Lemma stack_size_vm_app : forall s1 s2,
    Mem.stack_size_vm (s1++s2) = Mem.stack_size_vm s1 + Mem.stack_size_vm s2.
Proof.
  intros. induction s1. auto. simpl. lia.
Qed.

Theorem stack_tc_size_vm: forall l stk stk',
    tc_sizes l stk stk' -> Mem.stack_size_vm stk = Mem.stack_size_vm stk'.
Proof.
  intros. induction H. auto.
  simpl. apply take_drop in H0. rewrite H0.
  rewrite stack_size_vm_app. lia.
Qed.

(** Here is the invariant relating two states.  The first three
  cases are standard.  Note the ``less defined than'' conditions
  over values and register states, and the corresponding ``extends''
  relation over memory states. *)

Inductive match_states: state -> state -> Prop :=
  | match_states_normal:
      forall s sp pc rs m s' rs' m' f n l
             (STACKS: match_stackframes n l s s')
             (RLD: regs_lessdef rs rs')
             (MLD: Mem.extends' m m')
             (STK: tc_sizes ((S n)::l)(Mem.stack (Mem.support m)) (Mem.stack(Mem.support m'))),
      match_states (State s f (Vptr sp Ptrofs.zero) pc rs m)
                   (State s' (transf_function f) (Vptr sp Ptrofs.zero) pc rs' m')
  | match_states_call:
      forall s f args m s' args' m' sz n l,
      match_stackframes n l s s' ->
      Val.lessdef_list args args' ->
      Mem.extends' m m' ->
      tc_sizes ((S n)::l)(Mem.stack (Mem.support m)) (Mem.stack(Mem.support m')) ->
      match_states (Callstate s f args m sz)
                   (Callstate s' (transf_fundef f) args' m' sz)
  | match_states_return:
      forall s v m s' v' m' n l,
      match_stackframes n l s s' ->
      Val.lessdef v v' ->
      Mem.extends' m m' ->
      tc_sizes l (drop (S n)(Mem.stack (Mem.support m)))(tl (Mem.stack(Mem.support m'))) ->
      match_states (Returnstate s v m)
                   (Returnstate s' v' m')
  | match_states_interm:
      forall s sp pc rs m s' m' f r v' n l
             (STACKS: match_stackframes n l s s')
             (MLD: Mem.extends' m m')
             (STK: tc_sizes l (drop (S n)(Mem.stack (Mem.support m))) (tl (Mem.stack(Mem.support m')))),
      is_return_spec f pc r ->
      f.(fn_stacksize) = 0 ->
      Val.lessdef (rs#r) v' ->
      match_states (State s f (Vptr sp Ptrofs.zero) pc rs m)
                   (Returnstate s' v' m').

(** The last case of [match_states] corresponds to the execution
  of a move/nop/return sequence in the original code that was
  eliminated by the transformation:
<<
     State stk f (move/nop/return seq)  ~~  Returnstate stk' res'
            .
            .
            .
     State stk f (return instr)         ~~  Returnstate stk' res'
>>
  To preserve non-terminating behaviors, we need to make sure
  that the execution of this sequence in the original code cannot
  diverge.  For this, we introduce the following complicated
  measure over states, which will decrease strictly whenever
  the original code makes a transition but the transformed code
  does not. *)

Definition measure (st: state) : nat :=
  match st with
  | State s f sp pc rs m => (List.length s * (niter + 2) + return_measure f.(fn_code) pc + 1)%nat
  | Callstate s f args m sz => 0%nat
  | Returnstate s v m => (List.length s * (niter + 2))%nat
  end.

Ltac TransfInstr :=
  match goal with
  | H: (PTree.get _ (fn_code _) = _) |- _ =>
      destruct (transf_instr_lookup _ _ _ H) as [i' [TINSTR TSPEC]]; inv TSPEC
  end.

Ltac EliminatedInstr :=
  match goal with
  | H: (is_return_spec _ _ _) |- _ => inv H; try congruence
  | _ => idtac
  end.

(** The proof of semantic preservation, then, is a simulation diagram
  of the ``option'' kind. *)

Lemma transf_step_correct:
  forall s1 t s2, step fn_stack_requirements ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1'),
  (exists s2', step fn_stack_requirements tge s1' t s2' /\ match_states s2 s2')
  \/ (measure s2 < measure s1 /\ t = E0 /\ match_states s2 s1')%nat.
Proof.
  induction 1; intros; inv MS; EliminatedInstr.

- (* nop *)
  TransfInstr. left. econstructor; split.
  eapply exec_Inop; eauto. econstructor; eauto.

- (* eliminated nop *)
  assert (s0 = pc') by congruence. subst s0.
  right. split. simpl. lia. split. auto.
  econstructor; eauto.

- (* op *)
  TransfInstr.
  assert (Val.lessdef_list (rs##args) (rs'##args)). apply regs_lessdef_regs; auto.
  exploit eval_operation_lessdef; eauto.
  intros [v' [EVAL' VLD]].
  left. exists (State s' (transf_function f) (Vptr sp0 Ptrofs.zero) pc' (rs'#res <- v') m'); split.
  eapply exec_Iop; eauto.  rewrite <- EVAL'.
  apply eval_operation_preserved. exact symbols_preserved.
  econstructor; eauto. apply set_reg_lessdef; auto.
- (* eliminated move *)
  rewrite H1 in H. clear H1. inv H.
  right. split. simpl. lia. split. auto.
  econstructor; eauto. simpl in H0. rewrite PMap.gss. congruence.

- (* load *)
  TransfInstr.
  assert (Val.lessdef_list (rs##args) (rs'##args)). apply regs_lessdef_regs; auto.
  exploit eval_addressing_lessdef; eauto.
  intros [a' [ADDR' ALD]].
  exploit Mem.loadv_extends'; eauto.
  intros [v' [LOAD' VLD]].
  left. exists (State s' (transf_function f) (Vptr sp0 Ptrofs.zero) pc' (rs'#dst <- v') m'); split.
  eapply exec_Iload with (a := a'). eauto.  rewrite <- ADDR'.
  apply eval_addressing_preserved. exact symbols_preserved. eauto.
  econstructor; eauto. apply set_reg_lessdef; auto.

- (* store *)
  TransfInstr.
  assert (Val.lessdef_list (rs##args) (rs'##args)). apply regs_lessdef_regs; auto.
  exploit eval_addressing_lessdef; eauto.
  intros [a' [ADDR' ALD]].
  exploit Mem.storev_extends'. 2: eexact H1. eauto. eauto. apply RLD.
  intros [m'1 [STORE' MLD']].
  left. exists (State s' (transf_function f) (Vptr sp0 Ptrofs.zero) pc' rs' m'1); split.
  eapply exec_Istore with (a := a'). eauto.  rewrite <- ADDR'.
  apply eval_addressing_preserved. exact symbols_preserved. eauto.
  destruct a; simpl in H1; try discriminate.
  econstructor; eauto.
  apply Mem.support_store in H1.
  apply Mem.support_storev in STORE'.
  rewrite H1. rewrite <- STORE'.
  auto.
- (* call *)
  exploit find_function_translated; eauto. intro FIND'.
  TransfInstr.
+ (* call turned tailcall *)
  assert ({ m'' | Mem.free m' sp0 0 (fn_stacksize (transf_function f)) = Some m''}).
    apply Mem.range_perm_free. rewrite stacksize_preserved. rewrite H8.
    red; intros; extlia.
  destruct X as [m'' FREE].
  left. exists (Callstate s' (transf_fundef fd) (rs'##args) m'' (fn_stack_requirements id)); split.
  eapply exec_Itailcall; eauto. eapply find_function_id_preserved; eauto.
  apply sig_preserved.
  econstructor. eapply match_stackframes_tail; eauto. apply regs_lessdef_regs; auto.
  eapply Mem.free_right_extends'; eauto. eapply Mem.push_stage_left_extends'; eauto.
  rewrite stacksize_preserved. rewrite H8. intros. extlia.
  simpl. apply tc_sizes_upstar.
  rewrite (Mem.support_free _ _ _ _ _ FREE).
  auto.
+ (* call that remains a call *)
  left. exists (Callstate (Stackframe res (transf_function f) (Vptr sp0 Ptrofs.zero) pc' rs' :: s')
               (transf_fundef fd) (rs'##args) (Mem.push_stage m') (fn_stack_requirements id)); split.
  eapply exec_Icall; eauto. eapply find_function_id_preserved; eauto.
  apply sig_preserved.
  econstructor; eauto. econstructor; eauto. apply regs_lessdef_regs; auto.
  eapply Mem.push_stage_extends'; eauto.
  apply tc_sizes_up. auto.
- (* tailcall *)
  exploit find_function_translated; eauto. intro FIND'.
  exploit Mem.free_parallel_extends'; eauto. intros [m'1 [FREE EXT]].
  TransfInstr.
  left. exists (Callstate s' (transf_fundef fd) (rs'##args) m'1 (fn_stack_requirements id)); split.
  eapply exec_Itailcall; eauto. eapply find_function_id_preserved; eauto.
  apply sig_preserved.
  rewrite stacksize_preserved; auto.
  econstructor. eauto.  apply regs_lessdef_regs; auto. auto.
  rewrite (Mem.support_free _ _ _ _ _ H3).
  rewrite (Mem.support_free _ _ _ _ _ FREE).
  auto.
- (* builtin *)
  TransfInstr.
  exploit (@eval_builtin_args_lessdef _ ge (fun r => rs#r) (fun r => rs'#r)); eauto.
  intros (vargs' & P & Q).
  exploit external_call_mem_extends'; eauto.
  eapply Mem.push_stage_extends'; eauto.
  intros [v' [m'1 [A [B [C D]]]]].
    assert ({m'2:mem|Mem.pop_stage m'1 = Some m'2}).
    apply Mem.nonempty_pop_stage.
    erewrite <- external_call_mem_stackeq; eauto.
    simpl. congruence.
  destruct X as [m'2 Y].
  left. exists (State s' (transf_function f) (Vptr sp0 Ptrofs.zero) pc' (regmap_setres res v' rs') m'2); split.
  eapply exec_Ibuiltin; eauto.
  eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor; eauto. apply set_res_lessdef; auto.
  eapply Mem.pop_stage_extends'; eauto.
  {
    apply Mem.stack_pop_stage in H2. destruct H2 as [hd STK1].
    eapply external_call_mem_stackeq in H1. rewrite <- H1 in STK1.
    simpl in STK1. inv STK1.
    apply Mem.stack_pop_stage in Y. destruct Y as [hd' STK2].
    eapply external_call_mem_stackeq in A. rewrite <- A in STK2.
    simpl in STK2. inv STK2.
    auto.
  }
- (* cond *)
  TransfInstr.
  left. exists (State s' (transf_function f) (Vptr sp0 Ptrofs.zero) (if b then ifso else ifnot) rs' m'); split.
  eapply exec_Icond; eauto.
  apply eval_condition_lessdef with (rs##args) m; auto. apply regs_lessdef_regs; auto.
  econstructor; eauto.

- (* jumptable *)
  TransfInstr.
  left. exists (State s' (transf_function f) (Vptr sp0 Ptrofs.zero) pc' rs' m'); split.
  eapply exec_Ijumptable; eauto.
  generalize (RLD arg). rewrite H0. intro. inv H2. auto.
  econstructor; eauto.

- (* return *)
  exploit Mem.free_parallel_extends'; eauto. intros [m'1 [FREE EXT]].
  TransfInstr.
  left. exists (Returnstate s' (regmap_optget or Vundef rs') m'1); split.
  apply exec_Ireturn; auto. rewrite stacksize_preserved; auto.
  econstructor. eauto.
  destruct or; simpl. apply RLD. constructor.
  auto.
  rewrite (Mem.support_free _ _ _ _ _ H0).
  rewrite (Mem.support_free _ _ _ _ _ FREE).
  inv STK. auto.
- (* eliminated return None *)
  assert (or = None) by congruence. subst or.
  right. split. simpl. lia. split. auto.
  econstructor. eauto.
  simpl. constructor.
  eapply Mem.free_left_extends'; eauto.
  rewrite (Mem.support_free _ _ _ _ _ H0).
  auto.
- (* eliminated return Some *)
  assert (or = Some r) by congruence. subst or.
  right. split. simpl. lia. split. auto.
  econstructor. eauto.
  simpl. auto.
  eapply Mem.free_left_extends'; eauto.
  rewrite (Mem.support_free _ _ _ _ _ H0).
  auto.
- (* internal call *)
  exploit Mem.alloc_extends'; eauto.
    instantiate (1 := 0). lia.
    instantiate (1 := fn_stacksize f). lia.
  intros [m'1 [ALLOC EXT]].
  assert (fn_stacksize (transf_function f) = fn_stacksize f /\
          fn_entrypoint (transf_function f) = fn_entrypoint f /\
          fn_params (transf_function f) = fn_params f).
    unfold transf_function. destruct (zeq (fn_stacksize f) 0); auto.
  destruct H1 as [EQ1 [EQ2 EQ3]].
  apply Mem.record_frame_vm_size in H0 as H1.
  inversion H10. subst.
    (*we need stacksize here*)
  assert ({m'2:mem|Mem.record_frame_vm m'1 (Mem.mk_frame sz) = Some m'2}).
    assert ({m'2:mem|Mem.record_frame m'1 (Mem.mk_frame sz) = Some m'2}).
    apply Mem.nonempty_record_frame.
    apply Mem.support_alloc in ALLOC. rewrite ALLOC. simpl.
    congruence.
    destruct X as [m'2 Y]. unfold Mem.record_frame_vm. rewrite Y. simpl.
    assert ((Mem.stack_size_vm (Mem.stack (Mem.support m'2)))<= Mem.max_stacksize).
    apply Mem.stack_alloc in H. apply Mem.stack_alloc in ALLOC.
    apply Mem.record_frame_vm_result in H0. apply Mem.stack_record_frame in H0.
    apply Mem.stack_record_frame in Y.
    destruct H0 as (hd & tl & A & B).
    destruct Y as (hd' & tl' & A' & B').
    apply stack_tc_size_vm in H10.
    rewrite <- H in H10. rewrite A in H10. rewrite <- ALLOC in H10.
    rewrite A' in H10.
    rewrite B'. rewrite B in H1. simpl. simpl in H1.
    simpl in H10. lia. rewrite zle_true; eauto.
  destruct X as [m'2 Y].
  left. econstructor; split.
  simpl. eapply exec_function_internal. rewrite EQ1; eauto. eauto.
  rewrite EQ2. rewrite EQ3. econstructor; eauto.
  apply regs_lessdef_init_regs. auto.
  eapply Mem.record_frame_vm_extends'; eauto.
  apply Mem.stack_alloc in H. apply Mem.stack_alloc in ALLOC.
  apply Mem.record_frame_vm_result in H0. apply Mem.stack_record_frame in H0.
  apply Mem.record_frame_vm_result in Y. apply Mem.stack_record_frame in Y.
    destruct H0 as (hd & tl & A & B).
    destruct Y as (hd' & tl' & A' & B').
    rewrite B'. rewrite B.
    rewrite <- H in H10. rewrite A in H10.
    rewrite <- ALLOC in H10. rewrite A' in H10.
    apply tc_sizes_record. auto.
- (* external call *)
  exploit external_call_mem_extends'; eauto.
  intros [res' [m2' [A [B [C D]]]]].
  left. exists (Returnstate s' res' m2'); split.
  simpl. econstructor; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor; eauto.
  apply external_call_mem_stackeq in H.
  apply external_call_mem_stackeq in A.
  rewrite <- A. rewrite <- H.
  inv H9. auto.
- (* returnstate *)
  inv H3.
+ (* synchronous return in both programs *)
  inversion H7. subst.
  assert ({m'1:mem|Mem.pop_stage m'0 = Some m'1}).
  apply Mem.nonempty_pop_stage.
  destruct (Mem.stack(Mem.support m'0)). inv H2. congruence.
  destruct X as [m'1 POP].
  left. econstructor; split.
  apply exec_return. eauto.
  econstructor; eauto. apply set_reg_lessdef; auto.
  eapply Mem.pop_stage_extends'; eauto.
  eapply Mem.stack_pop_stage in H.
  eapply Mem.stack_pop_stage in POP.
  destruct H as [hd H].
  destruct POP as [hd' POP].
  rewrite H in H7.
  rewrite POP in H7.
  simpl in *. auto.
+ (* return instr in source program, eliminated because of tailcall *)
  right. split. unfold measure. simpl length.
  change (S (length s) * (niter + 2))%nat
   with ((niter + 2) + (length s) * (niter + 2))%nat.
  generalize (return_measure_bounds (fn_code f) pc). lia.
  split. auto.
  econstructor; eauto.
  eapply Mem.pop_stage_left_extends' in H; eauto.
  eapply Mem.stack_pop_stage in H. destruct H as [hd H].
  rewrite H in H7. simpl in *. auto.
  rewrite Regmap.gss. auto.
Qed.

Lemma transf_initial_states:
  forall st1, initial_state fn_stack_requirements prog st1 ->
  exists st2, initial_state fn_stack_requirements tprog st2 /\ match_states st1 st2.
Proof.
  intros. inv H.
  exploit funct_ptr_translated; eauto. intro FIND.
  exists (Callstate nil (transf_fundef f) nil (Mem.push_stage m0) (fn_stack_requirements (prog_main tprog))); split.
  econstructor; eauto. apply (Genv.init_mem_transf TRANSL). auto.
  replace (prog_main tprog) with (prog_main prog).
  rewrite symbols_preserved. eauto.
  symmetry; eapply match_program_main; eauto.
  rewrite <- H3. apply sig_preserved.
  destruct TRANSL as (_&MAIN& _). rewrite MAIN.
  econstructor. constructor. constructor. apply Mem.extends'_refl.
  eapply tc_sizes_up.
  erewrite Genv.init_mem_stack; eauto.
  constructor.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. inv H4. inv H3. constructor.
Qed.


(** The preservation of the observable behavior of the program then
  follows. *)

Theorem transf_program_correct:
  forward_simulation (RTL.semantics fn_stack_requirements prog) (RTL.semantics fn_stack_requirements tprog).
Proof.
  eapply forward_simulation_opt with (measure := measure); eauto.
  apply senv_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  exact transf_step_correct.
Qed.

End PRESERVATION.


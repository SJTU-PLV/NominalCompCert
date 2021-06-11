Require Import Coq.Lists.List.
Require Import Program.

Import List.ListNotations.

(** * Stack Tree *)

Inductive stree :=
| Node : list stree    (**r Trees containing inactive frames *)
       -> option stree  (**r An active sub-stackframe (if any) *)
       -> stree.

Definition empty_tree := Node [] None.

(* Fixpoint stree_length t :=  *)
(*   match t with *)
(*   | Node l None => 0 *)
(*   | Node l (Some t') => S (stree_length t') *)
(*   end. *)

(* Fixpoint stree_depth t := *)
(*   match t with  *)
(*   | Node l o => *)
(*     let d := match o with *)
(*             | None => 0 *)
(*             | Some t' => stree_depth t' *)
(*             end  *)
(*     in *)
(*     fold_right (fun t' d' => Nat.max (stree_depth t') d') d l *)
(*   end. *)

(** Fold left and right functions for stree *)
(* Fixpoint stree_fold_left {A:Type} (f: A -> stree -> A) (t:stree) (acc:A) := *)
(*   let acc' := f acc t in *)
(*   match t with *)
(*   | Node l None => acc' *)
(*   | Node l (Some t') => stree_fold_left f t' acc' *)
(*   end. *)

(* Fixpoint stree_fold_right {A:Type} (f: stree -> A -> A) (acc:A) (t:stree) := *)
(*   match t with *)
(*   | Node l None => f t acc *)
(*   | Node l (Some t') => f t' (stree_fold_right f acc t') *)
(*   end. *)


(** Path *)
Definition path := list nat.

(** Next tree and path *)
Fixpoint next_stree (t: stree) : (stree * path) :=
  match t with 
  | Node l None => 
    let idx := length l in    
    (Node l (Some empty_tree), [idx])
  | Node l (Some t') =>
    let (t'', p) := next_stree t' in
    (Node l (Some t''), (length l) :: p)
  end.

(** Return from the active node (use well-founded induction) *)

Fixpoint return_stree (t: stree) : option stree :=
  match t with
  | Node l None =>
    None
  | Node l (Some t) =>
    match return_stree t with
    | None => Some (Node (l ++ [t]) None)
    | Some t' => Some (Node l (Some t'))
    end
  end.

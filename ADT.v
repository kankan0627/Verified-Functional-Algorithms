From Coq Require Import String.  
From VFA Require Import Perm.
From VFA Require Import Maps.
From VFA Require Import SearchTree.

Module Type Table.

Parameter table : Type.
Definition key := nat.
Parameter V : Type.
Parameter default : V.
Parameter empty : table.
Parameter get : key -> table -> V.
Parameter set : key -> V -> table -> table.
Axiom get_empty_default : forall (k : key),
      get k empty = default.
Axiom get_set_same : forall (k : key) (v : V) (t : table),
      get k (set k v t) = v.
Axiom get_set_other : forall (k k' : key) (v : V) (t : table),
      k <> k' -> get k' (set k v t) = get k' t.
End Table.

Module Type ValType.
  Parameter V : Type.
  Parameter default : V.
End ValType.

Module FunTable (VT : ValType) <: Table.
  Definition V := VT.V.
  Definition default := VT.default.
  Definition key := nat.
  Definition table := key -> V.

  Definition empty : table :=
    fun _ => default.

  Definition get (k : key) (t : table) : V := t k.

  Definition set (k : key) (v : V) (t : table) : table :=
    fun k' => if k =? k' then v else t k'.

Theorem get_empty_default: forall (k : key),
   get k empty = default.
Proof. 
   intros. unfold get. unfold empty. auto. 
Qed.

Theorem get_set_same: forall (k : key) (v : V) (t : table), 
      get k (set k v t) = v.
Proof.
   intros.  unfold set. unfold get. rewrite Nat.eqb_refl. auto.
Qed.

Theorem get_set_other: forall (k k' : key) (v : V) (t : table),
      k <> k' -> get k' (set k v t) = get k' t.
Proof.
intros. unfold set. unfold get. apply Nat.eqb_neq in H. 
rewrite H. auto.
Qed.

End FunTable.

Module StringVal.
  Definition V := string.
  Definition default := ""%string.
End StringVal.

Module FunTableExamples.
Module StringFunTable := FunTable StringVal.
Import StringFunTable.
Open Scope string_scope.

Example ex1 : get 0 empty = "".
Proof. reflexivity. Qed.

Example ex2 : get 0 (set 0 "A" empty) = "A".
Proof. reflexivity. Qed.

Example ex3 : get 1 (set 0 "A" empty) = "".
Proof. reflexivity. Qed.

End FunTableExamples.

Module NatVal.
Definition V := nat.
Definition default := 0.
End NatVal.

Module NatFunTableExamples.
Module NatFunTable := FunTable NatVal.
Import NatFunTable.

Example ex1 : get 0 empty = 0.
Proof. reflexivity. Qed.

Example ex2 : get 0 (set 0 1 empty) = 1.
Proof. reflexivity. Qed.

Example ex3 : get 1 (set 0 1 empty) = 0.
Proof. reflexivity. Qed.

End NatFunTableExamples.

Module ListsTable (VT : ValType) <: Table.
Definition V := VT.V.
Definition default := VT.default.
Definition key := nat.
Definition table := list (key * V).
Definition empty : table := [].

Fixpoint get (k : key) (t : table) : V :=
  match t with
  | (k', v') :: t' => if k =? k' then v' else (get k t')
  | [] => default
  end.

Definition set (k : key) (v : V) (t : table) : table := (k,v)::t.


Theorem get_empty_default: forall (k : key),
   get k empty = default.
Proof.
   intros. simpl. auto.
Qed. 

Theorem get_set_same: forall (k : key) (v : V) (t : table),
  get k (set k v t) = v.
Proof.
  intros. unfold set. simpl. rewrite Nat.eqb_refl. auto.   
Qed.

Theorem get_set_other: forall (k k' : key) (v : V) (t : table),
   k <> k' -> get k' (set k v t) = get k' t.
Proof.
   intros. unfold set. simpl. rewrite Nat.eqb_sym.   
   apply Nat.eqb_neq in H. rewrite H. auto.  
Qed.

End ListsTable.

Module StringListsTableExamples.
Module StringListsTable := ListsTable StringVal.
Import StringListsTable.
Open Scope string_scope.

Example ex1 : get 0 empty = "".
Proof.
  simpl. auto.
Qed.

Example ex2 : get 0 (set 0 "A" empty) = "A".
Proof.
   simpl. auto.
Qed.

Example ex3 : get 1 (set 0 "A" empty) = "".
Proof.
  simpl. auto.
Qed.

End StringListsTableExamples.

Module TreeTable (VT : ValType) <: Table.

Definition V := VT.V.
Definition default := VT.default.
Definition key := nat.
Definition table := tree V.

Definition empty : table := 
    @empty_tree V.

Definition get (k : key) (t: table) : V := 
    lookup default k t.

Definition set (k : key) (v : V) (t : table) : table :=
    insert k v t.

Theorem get_empty_default: forall (k : key),
      get k empty = default.
Proof.
  intros. unfold get. apply lookup_empty. 
Qed.

Theorem get_set_same: forall (k : key) (v : V) (t : table),
      get k (set k v t) = v.
Proof.
  intros. unfold set. unfold get. apply lookup_insert_eq. 
Qed.

Theorem get_set_other: forall (k k' : key) (v : V) (t : table),
      k <> k' -> get k' (set k v t) = get k' t.
Proof.
   intros. unfold set. unfold get. apply lookup_insert_neq.  apply H.
Qed.

End TreeTable.






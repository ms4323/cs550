Require Import Coq.Bool.Bool.
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.

Inductive id : Type :=
  | Id : nat -> id.

Inductive partial_map : Type :=
  | empty  : partial_map
  | record : id -> bool -> partial_map -> partial_map.

Inductive booloption : Type :=
  | None : booloption
  | Some : bool -> booloption.

Inductive bool_exp : Type :=
  | BTrue  : bool_exp
  | BFalse : bool_exp
  | BVar   : id -> bool_exp
  | BNot   : bool_exp -> bool_exp
  | BAnd   : bool_exp -> bool_exp -> bool_exp
  | BOr    : bool_exp -> bool_exp -> bool_exp.

Definition update (d : partial_map) (x : id) (value : bool) : partial_map :=
  record x value d.

Fixpoint construct_map (vars : list nat) (vals : list bool) : partial_map :=
  match vars, vals with
  | nil,   nil     => empty
  | v::vs, va::vas => update (construct_map vs vas) (Id v) va 
  | _   , _        => empty
  end.

Definition beq_id (x : id) (y : id) : bool :=
  match x, y with
  | Id x', Id y' => if beq_nat x' y'
                    then true
                    else false
  end.

(* This find function doesn't use booloption, it assumes d always has an x variable*)
Fixpoint find (x : id) (d : partial_map) : booloption :=
  match d with
  | empty => None
  | record y v d' => if beq_id x y
                     then Some v
                     else find x d'
  end.

Definition and_eval (b1 : booloption) (b2 : booloption) : booloption :=
  match b1, b2 with
  | Some b1', Some b2' => Some (andb b1' b2')
  | _       , _        => None
  end.

Definition or_eval (b1 : booloption) (b2 : booloption) : booloption :=
  match b1, b2 with
  | Some b1' , Some b2' => Some (orb b1' b2')
  | _        , _        => None
  end.

Definition not_eval (b1 : booloption) : booloption :=
  match b1 with
  | Some b1' => Some (negb b1')
  | _        => None
  end.

Fixpoint bool_eval (m : partial_map) (b : bool_exp) : booloption :=
  match b with
  | BTrue       => Some true
  | BFalse      => Some false
  | BVar var    => find var m
  | BNot b1     => not_eval (bool_eval m b1)
  | BAnd b1 b2  => and_eval (bool_eval m b1) (bool_eval m b2)
  | BOr b1 b2   => or_eval (bool_eval m b1) (bool_eval m b2)
  end.

(*Just want to save some time contructing a partial_map*)
Definition test_partial_map : partial_map :=
  construct_map (1::2::3::4::nil) (true::false::false::true::nil).

Example test_bool_eval1:
  bool_eval test_partial_map (BOr BTrue BFalse) = Some true.
Proof. reflexivity. Qed.

Example test_bool_eval2:
  bool_eval test_partial_map (BAnd BTrue BFalse) = Some false.
Proof. reflexivity. Qed.

Example test_bool_eval3:
  bool_eval test_partial_map (BNot BFalse) = Some true.
Proof. reflexivity. Qed.

Example test_bool_eval4:
  bool_eval test_partial_map (BAnd (BOr (BVar (Id 1)) (BVar (Id 2))) (BAnd (BVar (Id 3)) (BNot BFalse))) = Some false.
Proof. reflexivity. Qed.

Example test_bool_eval5:
  bool_eval test_partial_map (BNot (BVar (Id 1))) = Some false.
Proof. reflexivity. Qed.


Fixpoint simp_not (b:bool_exp) : bool_exp :=
  match b with
  | BTrue      => BFalse
  | BFalse     => BTrue
  | BVar var   => BNot (BVar var)
  | BNot b'    => b'
  | exp        => BNot exp
(*  | BOr b1 b2  => BOr (simp_not b1) (simp_not b2)
  | BAnd b1 b2 => BAnd (simp_not b1) (simp_not b2) *)
  end.

Example test_simp_not1:
  bool_eval test_partial_map (simp_not (BOr BTrue BFalse)) = Some false.
Proof. simpl. reflexivity. Qed.


Example test_simp_not2:
  bool_eval test_partial_map (simp_not (BAnd (BNot BFalse) BFalse)) = Some true.
Proof. simpl. reflexivity. Qed.


Example test_simp_not3:
  bool_eval test_partial_map (simp_not (BNot (BNot BTrue))) = Some false.
Proof. simpl. reflexivity. Qed.


Example test_simp_not4:
  bool_eval test_partial_map (simp_not (BNot (BNot BTrue))) = Some false.
Proof. simpl. reflexivity. Qed.

Example test_simp_not5:
  bool_eval test_partial_map (simp_not (BNot (BNot BTrue))) = Some false.
Proof. simpl. reflexivity. Qed.

Fixpoint simp_or (b1:bool_exp) (b2:bool_exp) : bool_exp :=
  match b1,b2 with
  | BFalse , b' => b'
  | b' ,  BFalse => b'
  | BTrue , b2 => BTrue
  | b1 , BTrue => BTrue
  | b1, b2 => BOr b1 b2
  end.

Example test_simp_or0:
  simp_or BTrue BFalse = BTrue.
Proof. simpl. reflexivity. Qed.

Example test_simp_or1:
  bool_eval test_partial_map (simp_or BTrue BFalse) = Some true.
Proof. simpl. reflexivity. Qed.

Example test_simp_or2:
  simp_or (BNot BFalse) BFalse = BNot BFalse.
Proof. simpl. reflexivity. Qed.

Fixpoint simp_and (b1:bool_exp) (b2:bool_exp) : bool_exp :=
  match b1,b2 with
  | BFalse , b' => BFalse
  | b' ,  BFalse => BFalse
  | BTrue , b2 => b2
  | b1 , BTrue => b1
  | b1, b2 => BAnd b1 b2
  end.
  

Example test_simp_and0:
  simp_and BTrue BFalse = BFalse.
Proof. simpl. reflexivity. Qed.

Example test_simp_and1:
  bool_eval test_partial_map (simp_and BTrue BFalse) = Some false.
Proof. simpl. reflexivity. Qed.

Example test_simp_and2:
  simp_and (BNot BFalse) BFalse = BFalse.
Proof. simpl. reflexivity. Qed.

Fixpoint simp_bool (b:bool_exp) : bool_exp :=
  match b with 
  | BTrue => BTrue
  | BFalse => BFalse
  | BVar var    => BVar var
  | BNot b' => simp_not (simp_bool b')
  | BOr b1 b2 => simp_or (simp_bool b1) (simp_bool b2)
  | BAnd b1 b2 => simp_and (simp_bool b1) (simp_bool b2)
  end.

Example test_simp_bool1:
  bool_eval test_partial_map (simp_bool (BAnd (BNot BFalse) BFalse)) = Some false.
Proof. simpl. reflexivity. Qed.

Example test_simp_bool2:
  bool_eval test_partial_map (simp_bool (BNot (BAnd BTrue BFalse))) = Some true.
Proof. simpl. reflexivity. Qed.

Example test_simp_bool3:
  simp_bool (BNot (BAnd BTrue BFalse)) = BTrue.
Proof. simpl. reflexivity. Qed.




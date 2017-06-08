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

Fixpoint bool_eval (m : partial_map) (b : bool_exp) : booloption :=
  match b with
  | BTrue       => Some true
  | BFalse      => Some false
  | BVar var    => find var m
  | BNot b1     => match (bool_eval m b1) with
                   | None     => None 
                   | Some val => Some (negb val)
                   end
  | BAnd b1 b2  => match (bool_eval m b1), (bool_eval m b2) with
                   | Some b1' , Some b2' => Some (andb b1' b2')
                   | _ ,_ => None
                   end 
  | BOr b1 b2   => match (bool_eval m b1), (bool_eval m b2) with
                   | Some b1' , Some b2' => Some (orb b1' b2')
                   | _ ,_ => None
                   end  
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

Fixpoint simp_or (b:bool_exp) : bool_exp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BNot b' => BNot (simp_or b')
  | BOr BFalse b' => simp_or b'
  | BOr b' BFalse => simp_or b'
  | BOr b1 b2 => BOr (simp_or b1) (simp_or b2)
  | BAnd b1 b2 => BAnd (simp_or b1) (simp_or b2)
  end.

Example test_simp_or1:
  bool_eval (simp_or (BOr BTrue BFalse)) = true.
Proof. simpl. reflexivity. Qed.

Example test_simp_or2:
  bool_eval (simp_or (BAnd (BNot BFalse) BFalse)) = false.
Proof. simpl. reflexivity. Qed.

Fixpoint simp_and (b:bool_exp) : bool_exp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BNot b' => BNot (simp_and b')
  | BAnd BTrue b' => simp_and b'
  | BAnd b' BTrue => simp_and b'
  | BAnd b1 b2 => BAnd (simp_and b1) (simp_and b2)
  | BOr b1 b2 => BOr (simp_and b1) (simp_and b2)
  end.

Example test_simp_and1:
  bool_eval (simp_and (BOr BTrue BFalse)) = true.
Proof. simpl. reflexivity. Qed.

Example test_simp_and2:
  bool_eval (simp_and (BAnd (BNot BFalse) BFalse)) = false.
Proof. simpl. reflexivity. Qed.

Fixpoint simp_bool (b:bool_exp) : bool_exp :=
  match b with 
  | BTrue => BTrue
  | BFalse => BFalse
  | BNot b' => simp_not (simp_bool b')
  | BOr b1 b2 => simp_or (BOr (simp_bool b1) (simp_bool b2))
  | BAnd b1 b2 => simp_and (BAnd (simp_bool b1) (simp_bool b2))
  end.

Example test_simp_bool1:
  bool_eval (simp_bool (BAnd (BNot BFalse) BFalse)) = false.
Proof. simpl. reflexivity. Qed.

Example test_simp_bool2:
  bool_eval (simp_bool (BNot (BAnd BTrue BFalse))) = true.
Proof. simpl. reflexivity. Qed.




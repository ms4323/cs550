Require Import Coq.Bool.Bool.
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.

Inductive id : Type :=
  | Id : nat -> id.

Definition beq_id (x : id) (y : id) : bool :=
  match x, y with
  | Id x', Id y' => if beq_nat x' y'
                    then true
                    else false
  end.

Definition total_map (A:Type) := id -> A.
Definition t_empty {A:Type} (v : A) : total_map A := (fun _ => v).
Definition t_update {A:Type} (m : total_map A) (x : id) (v : A) :=
  fun x' => if beq_id x x' then v else m x'.
Definition test_map :=
  t_update (t_update (t_update (t_update (t_empty false) 
                                         (Id 1) true)
                               (Id 2) false)
                     (Id 3) false)
           (Id 4) true.

Inductive bool_exp : Type :=
  | BTrue  : bool_exp
  | BFalse : bool_exp
  | BVar   : id -> bool_exp
  | BNot   : bool_exp -> bool_exp
  | BAnd   : bool_exp -> bool_exp -> bool_exp
  | BOr    : bool_exp -> bool_exp -> bool_exp.


Fixpoint bool_eval (m : total_map bool) (b : bool_exp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BVar var    => m var
  | BNot b1     => negb (bool_eval m b1)
  | BAnd b1 b2  => andb (bool_eval m b1) (bool_eval m b2)
  | BOr b1 b2   => orb (bool_eval m b1) (bool_eval m b2)
  end.


Example test_bool_eval1:
  bool_eval test_map (BOr BTrue BFalse) = true.
Proof. reflexivity. Qed.

Example test_bool_eval2:
  bool_eval test_map (BAnd BTrue BFalse) = false.
Proof. reflexivity. Qed.

Example test_bool_eval3:
  bool_eval test_map (BNot BFalse) = true.
Proof. reflexivity. Qed.

Example test_bool_eval4:
  bool_eval test_map (BAnd (BOr (BVar (Id 1)) (BVar (Id 2))) (BAnd (BVar (Id 3)) (BNot BFalse))) = false.
Proof. reflexivity. Qed.

Example test_bool_eval5:
  bool_eval test_map (BNot (BVar (Id 1))) = false.
Proof. reflexivity. Qed.


Fixpoint simp_not (b:bool_exp) : bool_exp :=
  match b with
  | BTrue      => BFalse
  | BFalse     => BTrue
  | BNot b'    => b'
  | exp        => BNot exp
  end.

Example test_simp_not1:
  bool_eval test_map (simp_not (BOr BTrue BFalse)) = false.
Proof. simpl. reflexivity. Qed.


Example test_simp_not2:
  bool_eval test_map (simp_not (BAnd (BNot BFalse) BFalse)) = true.
Proof. simpl. reflexivity. Qed.


Example test_simp_not3:
  bool_eval test_map (simp_not (BNot (BNot BTrue))) = false.
Proof. simpl. reflexivity. Qed.


Example test_simp_not4:
  bool_eval test_map (simp_not (BNot (BNot BTrue))) = false.
Proof. simpl. reflexivity. Qed.

Example test_simp_not5:
  bool_eval test_map (simp_not (BNot (BNot BTrue))) = false.
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
  bool_eval test_map (simp_or BTrue BFalse) = true.
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
  bool_eval test_map (simp_and BTrue BFalse) = false.
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
  bool_eval test_map (simp_bool (BAnd (BNot BFalse) BFalse)) = false.
Proof. simpl. reflexivity. Qed.

Example test_simp_bool2:
  bool_eval test_map (simp_bool (BNot (BAnd BTrue BFalse))) = true.
Proof. simpl. reflexivity. Qed.

Example test_simp_bool3:
  simp_bool (BNot (BAnd BTrue BFalse)) = BTrue.
Proof. simpl. reflexivity. Qed.

Example test_simp_bool4:
  simp_bool (BNot (BNot BFalse)) = BFalse.
Proof. simpl. reflexivity. Qed.

Example test_simp_bool5:
  simp_bool (BAnd (BVar (Id 1)) (BNot (BNot BFalse))) = BFalse.
Proof. simpl. reflexivity. Qed.

Example test_simp_bool6:
  simp_bool (BOr (BVar (Id 2)) (BAnd (BVar (Id 1)) (BNot (BNot BTrue)))) = BOr (BVar (Id 2)) (BVar (Id 1)).
Proof. simpl. reflexivity. Qed.


(**********************************************************************)
(*************************** Theorems *********************************)
(**********************************************************************)

(******NOT********)
Theorem not_eval_involutive: forall b,
  negb (negb b) = b.
Proof.
intros b. induction b.
- reflexivity.
- simpl. reflexivity.
Qed.

Theorem bool_eval_simp_not:forall m b,
  bool_eval m (simp_not b) = bool_eval m (BNot b).
Proof. 
intros m b. induction b.
- reflexivity.
- reflexivity.
- reflexivity.
- simpl. rewrite -> not_eval_involutive. reflexivity.
- reflexivity.
- reflexivity.
Qed.



(*******AND********)

Theorem bool_eval_simp_and:forall m b1 b2,
  bool_eval m (simp_and b1 b2) = bool_eval m (BAnd b1 b2).
Proof. 
intros m b1 b2. induction b1.
- unfold simp_and. destruct b2. 
  + reflexivity. 
  + reflexivity. 
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + reflexivity.
- unfold simp_and. destruct b2.
  + reflexivity. 
  + reflexivity. 
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + reflexivity.
- unfold simp_and. destruct b2. 
  + simpl. rewrite -> andb_true_r. reflexivity.
  + simpl. rewrite -> andb_false_r. reflexivity.
  + simpl. reflexivity.
  + simpl. reflexivity.
  + simpl. reflexivity.
  + simpl. reflexivity.
- unfold simp_and. destruct b2. 
  + simpl. rewrite -> andb_true_r. reflexivity.
  + simpl. rewrite -> andb_false_r. reflexivity.
  + simpl. reflexivity.
  + simpl. reflexivity.
  + simpl. reflexivity.
  + simpl. reflexivity.
- unfold simp_and. destruct b2. 
  + simpl. rewrite -> andb_true_r. reflexivity.
  + simpl. rewrite -> andb_false_r. reflexivity.
  + simpl. reflexivity.
  + simpl. reflexivity.
  + simpl. reflexivity.
  + simpl. reflexivity.
- unfold simp_and. destruct b2. 
  + simpl. rewrite -> andb_true_r. reflexivity.
  + simpl. rewrite -> andb_false_r. reflexivity.
  + simpl. reflexivity.
  + simpl. reflexivity.
  + simpl. reflexivity.
  + simpl. reflexivity.
Qed.


(***********OR***************)

Theorem bool_eval_simp_or:forall m b1 b2,
  bool_eval m (simp_or b1 b2) = bool_eval m (BOr b1 b2).
Proof. 
intros m b1 b2. induction b1.
- unfold simp_and. destruct b2. 
  + reflexivity. 
  + reflexivity. 
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + reflexivity.
- unfold simp_and. destruct b2.
  + reflexivity. 
  + reflexivity. 
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + reflexivity.
- unfold simp_and. destruct b2. 
  + simpl. rewrite -> orb_true_r. reflexivity.
  + simpl. rewrite -> orb_false_r. reflexivity.
  + simpl. reflexivity.
  + simpl. reflexivity.
  + simpl. reflexivity.
  + simpl. reflexivity.
- unfold simp_and. destruct b2. 
  + simpl. rewrite -> orb_true_r. reflexivity.
  + simpl. rewrite -> orb_false_r. reflexivity.
  + simpl. reflexivity.
  + simpl. reflexivity.
  + simpl. reflexivity.
  + simpl. reflexivity.
- unfold simp_and. destruct b2. 
  + simpl. rewrite -> orb_true_r. reflexivity.
  + simpl. rewrite -> orb_false_r. reflexivity.
  + simpl. reflexivity.
  + simpl. reflexivity.
  + simpl. reflexivity.
  + simpl. reflexivity.
- unfold simp_and. destruct b2. 
  + simpl. rewrite -> orb_true_r. reflexivity.
  + simpl. rewrite -> orb_false_r. reflexivity.
  + simpl. reflexivity.
  + simpl. reflexivity.
  + simpl. reflexivity.
  + simpl. reflexivity.
Qed.



(************bool_boolsimp****************)

Theorem bool_boolsimp: forall (m : total_map bool) (b : bool_exp) ,
bool_eval m b = bool_eval m (simp_bool b).
Proof.
intros m b.
induction b.
- reflexivity.
- reflexivity.
- reflexivity.
- simpl. rewrite -> bool_eval_simp_not. rewrite -> IHb. reflexivity.
- simpl. rewrite -> bool_eval_simp_and. rewrite -> IHb1. rewrite -> IHb2. simpl. reflexivity.
- simpl. rewrite -> bool_eval_simp_or. rewrite -> IHb1. rewrite -> IHb2. simpl. reflexivity.
Qed.
  
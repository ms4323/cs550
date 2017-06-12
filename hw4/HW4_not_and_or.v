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
  not_eval (not_eval b) = b.
Proof.
intros b. induction b.
- reflexivity.
- simpl. rewrite -> negb_involutive. reflexivity.
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

Theorem wrong_t:  (*there is a problem with Some false = None, to be corrected.*) 
Some false = None.
Proof. Admitted.

Theorem someb_someb_and_true: forall b,
Some b = Some (b && true).
Proof. Admitted.

Theorem somefalse_someb_and_false: forall b,
Some false = Some (b && false).
Proof. Admitted.

Theorem bool_eval_simp_and:forall m b1 b2,
  bool_eval m (simp_and b1 b2) = bool_eval m (BAnd b1 b2).
Proof. 
intros m b1 b2. induction b1.
- unfold simp_and. destruct b2. 
  + reflexivity. 
  + reflexivity. 
  + simpl. destruct (find i m). 
    * reflexivity. 
    * reflexivity.
  + simpl. destruct (not_eval (bool_eval m b2)).
    * reflexivity. 
    * reflexivity.
  + simpl. destruct (and_eval (bool_eval m b2_1) (bool_eval m b2_2)).
    * reflexivity. 
    * reflexivity.
  + simpl. destruct (or_eval (bool_eval m b2_1) (bool_eval m b2_2)).
    * reflexivity.
    * reflexivity.
- unfold simp_and. destruct b2.
  + reflexivity. 
  + reflexivity. 
  + simpl. destruct (find i m). (*Problem is here*)
    * rewrite -> wrong_t. reflexivity.
    * reflexivity.
  + simpl. destruct (not_eval (bool_eval m b2)).
    * rewrite -> wrong_t. reflexivity.
    * reflexivity.
  + simpl. destruct (and_eval (bool_eval m b2_1) (bool_eval m b2_2)).
    * rewrite -> wrong_t. reflexivity.
    * reflexivity.
  + simpl. destruct (or_eval (bool_eval m b2_1) (bool_eval m b2_2)).
    * rewrite -> wrong_t. reflexivity.
    * reflexivity.
- unfold simp_and. destruct b2. 
  + simpl. unfold and_eval. destruct (find i m). 
    * reflexivity.
    * rewrite -> someb_someb_and_true. reflexivity. 
  + simpl. unfold and_eval. destruct (find i m). 
    * rewrite -> wrong_t. reflexivity.
    * rewrite <- somefalse_someb_and_false. reflexivity. 
  + simpl. unfold and_eval. destruct (find i m). 
    * reflexivity. 
    * reflexivity.
  + simpl. destruct (not_eval (bool_eval m b2)).
    * reflexivity. 
    * reflexivity.
  + simpl. destruct (and_eval (bool_eval m b2_1) (bool_eval m b2_2)).
    * reflexivity. 
    * reflexivity.
  + simpl. destruct (or_eval (bool_eval m b2_1) (bool_eval m b2_2)).
    * reflexivity.
    * reflexivity.
- unfold simp_and. destruct b2. 
  + simpl. unfold and_eval. destruct (not_eval (bool_eval m b1)). 
    * reflexivity.
    * rewrite -> someb_someb_and_true. reflexivity. 
  + simpl. unfold and_eval. destruct (not_eval (bool_eval m b1)). 
    * rewrite -> wrong_t. reflexivity.
    * rewrite <- somefalse_someb_and_false. reflexivity. 
  + simpl. unfold and_eval. destruct (not_eval (bool_eval m b1)). 
    * reflexivity. 
    * reflexivity.
  + simpl. destruct (not_eval (bool_eval m b2)).
    * reflexivity. 
    * reflexivity.
  + simpl. destruct (and_eval (bool_eval m b2_1) (bool_eval m b2_2)).
    * reflexivity. 
    * reflexivity.
  + simpl. destruct (or_eval (bool_eval m b2_1) (bool_eval m b2_2)).
    * reflexivity.
    * reflexivity.
- unfold simp_and. destruct b2. 
  + simpl. unfold and_eval. destruct (bool_eval m b1_1). 
    * reflexivity.
    * destruct (bool_eval m b1_2). reflexivity. rewrite -> someb_someb_and_true. reflexivity. 
  + simpl. unfold and_eval. destruct (bool_eval m b1_1). 
    * rewrite -> wrong_t. reflexivity.
    * destruct (bool_eval m b1_2). rewrite -> wrong_t. reflexivity. rewrite <- somefalse_someb_and_false. reflexivity. 
  + simpl. unfold and_eval. destruct (bool_eval m b1_1). 
    * reflexivity. 
    * destruct (bool_eval m b1_2). reflexivity. destruct (find i m). reflexivity. reflexivity.
  + simpl. destruct (not_eval (bool_eval m b2)).
    * reflexivity. 
    * reflexivity.
  + simpl. destruct (and_eval (bool_eval m b2_1) (bool_eval m b2_2)).
    * reflexivity. 
    * reflexivity.
  + simpl. destruct (or_eval (bool_eval m b2_1) (bool_eval m b2_2)).
    * reflexivity.
    * reflexivity.
- unfold simp_and. destruct b2. 
  + simpl. unfold and_eval. destruct (bool_eval m b1_1). 
    * reflexivity.
    * destruct (bool_eval m b1_2). reflexivity. rewrite -> someb_someb_and_true. destruct (or_eval (Some (b && true)) (Some b0)). reflexivity. rewrite -> someb_someb_and_true. reflexivity.  
  + simpl. unfold and_eval. destruct (bool_eval m b1_1). 
    * rewrite -> wrong_t. reflexivity.
    * destruct (bool_eval m b1_2). rewrite -> wrong_t. reflexivity. destruct (or_eval (Some b) (Some b0)). rewrite <-wrong_t. reflexivity. rewrite <- somefalse_someb_and_false. reflexivity. 
  + simpl. unfold and_eval. destruct (bool_eval m b1_1). 
    * reflexivity. 
    * destruct (bool_eval m b1_2). reflexivity. destruct (find i m). reflexivity. reflexivity.
  + simpl. destruct (not_eval (bool_eval m b2)).
    * reflexivity. 
    * reflexivity.
  + simpl. destruct (and_eval (bool_eval m b2_1) (bool_eval m b2_2)).
    * reflexivity. 
    * reflexivity.
  + simpl. destruct (or_eval (bool_eval m b2_1) (bool_eval m b2_2)).
    * reflexivity.
    * reflexivity.
Qed.


(***********OR***************)

Theorem wrong_t2:  (*there is a problem with Some true = None, to be corrected.*) 
Some true = None.
Proof. Admitted.

Theorem sometrue_someb_or_true: forall b,
Some true = Some (b || true).
Proof. Admitted.

Theorem someb_someb_or_false: forall b,
Some b = Some (b || false).
Proof. Admitted.

Theorem bool_eval_simp_or:forall m b1 b2,
  bool_eval m (simp_or b1 b2) = bool_eval m (BOr b1 b2).
Proof. 
intros m b1 b2. induction b1.
- unfold simp_or. destruct b2. 
  + reflexivity. 
  + reflexivity. 
  + simpl. destruct (find i m). 
    * rewrite -> wrong_t2. reflexivity. 
    * reflexivity.
  + simpl. destruct (not_eval (bool_eval m b2)).
    * rewrite -> wrong_t2. reflexivity. 
    * reflexivity.
  + simpl. destruct (and_eval (bool_eval m b2_1) (bool_eval m b2_2)).
    * rewrite -> wrong_t2. reflexivity. 
    * reflexivity.
  + simpl. destruct (or_eval (bool_eval m b2_1) (bool_eval m b2_2)).
    * rewrite -> wrong_t2. reflexivity.  
    * reflexivity.
- unfold simp_or. destruct b2.
  + reflexivity. 
  + reflexivity. 
  + simpl. destruct (find i m). (*Problem is here*)
    * reflexivity.
    * reflexivity.
  + simpl. destruct (not_eval (bool_eval m b2)).
    * reflexivity.
    * reflexivity.
  + simpl. destruct (and_eval (bool_eval m b2_1) (bool_eval m b2_2)).
    * reflexivity.
    * reflexivity.
  + simpl. destruct (or_eval (bool_eval m b2_1) (bool_eval m b2_2)).
    * reflexivity.
    * reflexivity.
- unfold simp_or. destruct b2. 
  + simpl. unfold and_eval. destruct (find i m). 
    * simpl. rewrite -> wrong_t2. reflexivity. 
    * simpl. rewrite <- sometrue_someb_or_true. reflexivity. 
  + simpl. unfold and_eval. destruct (find i m). 
    * simpl. reflexivity.
    * simpl. rewrite <- someb_someb_or_false. reflexivity. 
  + simpl. unfold and_eval. destruct (find i m). 
    * simpl. reflexivity. 
    * simpl. destruct (find i0 m). reflexivity. reflexivity.
  + simpl. destruct (not_eval (bool_eval m b2)).
    * reflexivity. 
    * reflexivity.
  + simpl. destruct (and_eval (bool_eval m b2_1) (bool_eval m b2_2)).
    * reflexivity. 
    * reflexivity.
  + simpl. destruct (or_eval (bool_eval m b2_1) (bool_eval m b2_2)).
    * reflexivity.
    * reflexivity.
- unfold simp_or. destruct b2. 
  + simpl. unfold and_eval. destruct (not_eval (bool_eval m b1)). 
    * simpl. rewrite -> wrong_t2. reflexivity.
    * simpl. rewrite <- sometrue_someb_or_true. reflexivity. 
  + simpl. unfold and_eval. destruct (not_eval (bool_eval m b1)). 
    * simpl. reflexivity.
    * simpl. rewrite <- someb_someb_or_false. reflexivity. 
  + simpl. unfold and_eval. destruct (not_eval (bool_eval m b1)). 
    * reflexivity. 
    * reflexivity.
  + simpl. destruct (not_eval (bool_eval m b2)).
    * reflexivity. 
    * reflexivity.
  + simpl. destruct (and_eval (bool_eval m b2_1) (bool_eval m b2_2)).
    * reflexivity. 
    * reflexivity.
  + simpl. destruct (or_eval (bool_eval m b2_1) (bool_eval m b2_2)).
    * reflexivity.
    * reflexivity.
- unfold simp_or. destruct b2. 
  + simpl. unfold and_eval. destruct (bool_eval m b1_1). 
    * simpl. rewrite -> wrong_t2. reflexivity.
    * destruct (bool_eval m b1_2). simpl. rewrite -> wrong_t2. reflexivity. simpl. rewrite <- sometrue_someb_or_true. reflexivity. 
  + simpl. unfold and_eval. destruct (bool_eval m b1_1). 
    * simpl. reflexivity.
    * destruct (bool_eval m b1_2). simpl. reflexivity. simpl. rewrite <- someb_someb_or_false. reflexivity. 
  + simpl. unfold and_eval. destruct (bool_eval m b1_1). 
    * reflexivity. 
    * destruct (bool_eval m b1_2). reflexivity. destruct (find i m). reflexivity. reflexivity.
  + simpl. destruct (not_eval (bool_eval m b2)).
    * reflexivity. 
    * reflexivity.
  + simpl. destruct (and_eval (bool_eval m b2_1) (bool_eval m b2_2)).
    * reflexivity. 
    * reflexivity.
  + simpl. destruct (or_eval (bool_eval m b2_1) (bool_eval m b2_2)).
    * reflexivity.
    * reflexivity.
- unfold simp_or. destruct b2. 
  + simpl. unfold and_eval. destruct (bool_eval m b1_1). 
    * simpl. rewrite -> wrong_t2. reflexivity.
    * destruct (bool_eval m b1_2). simpl. rewrite -> wrong_t2. reflexivity. simpl. rewrite <- sometrue_someb_or_true. destruct (or_eval (Some (b && true)) (Some b0)). reflexivity. reflexivity.  
  + simpl. unfold and_eval. destruct (bool_eval m b1_1). 
    * simpl. reflexivity.
    * destruct (bool_eval m b1_2). simpl. reflexivity. destruct (or_eval (Some b) (Some b0)). simpl. reflexivity. simpl. rewrite <- someb_someb_or_false. reflexivity. 
  + simpl. unfold and_eval. destruct (bool_eval m b1_1). 
    * reflexivity. 
    * destruct (bool_eval m b1_2). reflexivity. destruct (find i m). reflexivity. reflexivity.
  + simpl. destruct (not_eval (bool_eval m b2)).
    * reflexivity. 
    * reflexivity.
  + simpl. destruct (and_eval (bool_eval m b2_1) (bool_eval m b2_2)).
    * reflexivity. 
    * reflexivity.
  + simpl. destruct (or_eval (bool_eval m b2_1) (bool_eval m b2_2)).
    * reflexivity.
    * reflexivity.
Qed.



(************bool_boolsimp****************)

Theorem bool_boolsimp: forall (m : partial_map) (b : bool_exp) ,
bool_eval m b = bool_eval m (simp_bool b).
Proof.
intros m b.
induction b.
- reflexivity.
- reflexivity.
- reflexivity.
- simpl. rewrite -> bool_eval_simp_not. simpl. rewrite -> IHb. reflexivity.
- simpl. rewrite -> bool_eval_simp_and. rewrite -> IHb1. rewrite -> IHb2. simpl. reflexivity.
- simpl. rewrite -> bool_eval_simp_or. rewrite -> IHb1. rewrite -> IHb2. simpl. reflexivity.
Qed.
  
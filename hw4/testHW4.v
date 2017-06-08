Require Import Coq.Bool.Bool.

Inductive bool_exp : Type :=
  | BTrue : bool_exp
  | BFalse : bool_exp
  | BNot : bool_exp -> bool_exp
  | BAnd : bool_exp -> bool_exp -> bool_exp
  | BOr : bool_exp -> bool_exp -> bool_exp.


Fixpoint bool_eval (b : bool_exp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BNot b1     => negb (bool_eval b1)
  | BAnd b1 b2  => andb (bool_eval b1) (bool_eval b2)
  | BOr b1 b2   => orb (bool_eval b1) (bool_eval b2)
  end.

Example test_bool_eval1:
  bool_eval (BOr BTrue BFalse) = true.
Proof. reflexivity. Qed.

Example test_bool_eval2:
  bool_eval (BAnd BTrue BFalse) = false.
Proof. reflexivity. Qed.

Example test_bool_eval3:
  bool_eval (BNot BFalse) = true.
Proof. reflexivity. Qed.

Fixpoint simp_not (b:bool_exp) : bool_exp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BNot b' => simp_not b'
  | BOr b1 b2 => BOr (simp_not b1) (simp_not b2)
  | BAnd b1 b2 => BAnd (simp_not b1) (simp_not b2)
  end.

Example test_simp_not1:
  bool_eval (simp_not (BOr BTrue BFalse)) = true.
Proof. simpl. reflexivity. Qed.


Example test_simp_not2:
  bool_eval (simp_not (BAnd (BNot BFalse) BFalse)) = false.
Proof. simpl. reflexivity. Qed.


Example test_simp_not3:
  bool_eval (simp_not (BNot (BNot BTrue))) = true.
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




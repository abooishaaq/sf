From Coq Require Import Unicode.Utf8.

(* booleans *)

Inductive bool : Type :=
  | true
  | false.

Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Definition nandb (b1 : bool) (b2 : bool) : bool :=
  negb (andb b1 b2).

Definition andb3 (b1 : bool) (b2 : bool) (b3 : bool) : bool :=
  andb b1 (andb b2 b3).


(* natural numbers *)

Module NatPlay.

Inductive nat : Type :=
  | O
  | S (n : nat).

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

End NatPlay.


Fixpoint even (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Example test_even1: even 1 = false.
Proof. simpl. reflexivity. Qed.
Example test_even2: even 4 = true.
Proof. simpl. reflexivity. Qed.

Fixpoint plus (n m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _ => O
  | S _ , O => n
  | S n', S m' => minus n' m'
  end.

Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Check ((0 + 1) + 1) : nat.


Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => mult n (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Example test_leb1: leb 2 2 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: leb 2 4 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: leb 4 2 = false.
Proof. simpl. reflexivity. Qed.
  
Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Example test_leb3': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.


Definition ltb (n m : nat) : bool :=
  match leb n m with
  | true => negb (eqb n m)
  | false => false
  end.

Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.


(* Proof by Simplification *)

Theorem plus_O_n : ∀ n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

(* can work with just using reflexivity *)
Theorem plus_O_n' : ∀ n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.


(* Proof by Rewriting *)

Theorem plus_id_example : ∀ n m:nat,
  n = m ->
  n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite <- H.
  reflexivity. Qed.
(* -> specifies the direction of rewrite *)
(* -> is default and can be omitted a*)


Theorem plus_id_exercise : ∀ n m o : nat,
  n = m ->
  m = o ->
  n + m = m + o.
Proof.
  intros n m o.
  intros H.
  rewrite -> H.
  intros H'.
  rewrite -> H'.
  reflexivity. Qed.


(* Proof by Case Analysis *)

(* proof which can't be done by rewrite and simplification *)
Theorem plus_1_neq_0_firsttry : ∀ n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n.
  simpl. (* does nothing! *)
Abort.

Theorem plus_1_neq_0 : ∀ n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E. (* introduces subgoal *)
  - reflexivity. (* first subgoal *)
  - reflexivity. (* second subgoal *)
  Qed.

Theorem negb_involutive : ∀ b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity. 
  Qed.


Theorem andb_commutative : ∀ b c, andb b c = andb c b.
Proof.
    intros b c. destruct b eqn:Eb.
    - destruct c eqn:Ec.
      + reflexivity.
      + reflexivity.
    - destruct c eqn:Ec.
      + reflexivity.
      + reflexivity.
  Qed.


Theorem andb_true_elim2 : ∀ b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c.
  destruct c eqn:Ec.
  - reflexivity.
  - intros H. rewrite <- H. destruct b eqn:EqnB.
    + reflexivity.
    + reflexivity.
  Qed.

Theorem identity_fn_applied_twice :
  ∀ (f : bool → bool),
  (∀ (x : bool), f x = x) →
  ∀ (b : bool), f (f b) = b.
Proof.
  intros f H b.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
  Qed.

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c.
  destruct b.
  - simpl. intros H. rewrite -> H. reflexivity.
  - simpl. intros H. rewrite -> H. reflexivity.
Qed.

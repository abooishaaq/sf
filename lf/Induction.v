From LF Require Export Basics.
From Coq Require Import Unicode.Utf8.
Set Printing All.

Theorem add_0_r : ∀ n : nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem minus_n_n : ∀ n,
  minus n n = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) simpl. reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity. 
  Qed.

Theorem mul_0_r : ∀ n : nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity. 
  Qed.

Theorem plus_n_Sm : ∀ n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity. 
  Qed.

Theorem add_comm : ∀ n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [| n' IHn'].
  - (* n = 0 *) simpl. rewrite -> add_0_r. reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity. 
  Qed.

Theorem add_assoc : ∀ n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity. 
  Qed.

Fixpoint double (n : nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : ∀ n, double n = n + n .
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity. 
  Qed.

Theorem eqb_refl : ∀ n : nat,
  (n =? n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity. 
  Qed.

Theorem even_S : ∀ n : nat,
  even (S n) = negb (even n).
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) 
    rewrite -> IHn'.
    rewrite -> negb_involutive.
    reflexivity.
  Qed.

Theorem mult_0_plus' : ∀ n m : nat,
  (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  assert (H: n + 0 + 0 = n).
    { rewrite add_comm. simpl. rewrite add_comm. reflexivity. }
  rewrite -> H.
  reflexivity. 
  Qed.

Theorem add_shuffle3 : ∀ n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> add_assoc.
  rewrite -> add_assoc.
  assert (H: n + m = m + n).
  { rewrite -> add_comm. reflexivity. }
  rewrite -> H. reflexivity.
  Qed.

Theorem mul_comm : ∀ m n : nat,
  m * n = n * m.
Proof.
  intros m n. 
  destruct m as [| m'].
  - (* m = 0 *) simpl. rewrite -> mul_0_r. reflexivity.
  - (* m = S m' *) induction n as [| n' IHn']. 
    + (* n = 0 *) 
      simpl. rewrite -> mul_0_r. reflexivity.
    + (* n = S n' *) 
      simpl. rewrite <- IHn'. simpl. rewrite <- mult_n_Sm.
      assert (H1: m' + (n' + m' * n') = n' + (m' + m' * n')).
      { rewrite -> add_shuffle3. reflexivity. }
      assert (H2: m' * n' + m' = m' + m' * n').
      { rewrite -> add_comm. reflexivity. }
      rewrite -> H1. rewrite -> H2.
      reflexivity.
  Qed.

Theorem plus_leb_compat_l : ∀ n m p : nat,
  n <=? m = true → (p + n) <=? (p + m) = true.
Proof.
  intros n m p H. induction p as [| p' IHp'].
  - (* p = 0 *) simpl. rewrite -> H. reflexivity.
  - (* p = S p' *) simpl. rewrite -> IHp'. reflexivity.
  Qed.

Theorem leb_refl : ∀ n:nat,
  (n <=? n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity.
  Qed.

Theorem zero_nbeq_S : ∀ n : nat,
  0 =? (S n) = false.
Proof.
  intros n. reflexivity. Qed.

Theorem zero_nbeq_S' : ∀ n : nat,
  0 =? (S n) = false.
Proof.
  induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. reflexivity.
  Qed.

Theorem andb_false_r : ∀ b : bool,
  andb b false = false.
Proof.
  intros b. destruct b.
  - (* b = true *) reflexivity.
  - (* b = false *) reflexivity.
  Qed.

Theorem mult_1_l : ∀ n:nat, 1 * n = n.
Proof.
  intros n. simpl. rewrite -> add_0_r. reflexivity.
  Qed.

Theorem all3_spec : ∀ b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
  intros b c. destruct b.
  - (* b = true *) destruct c.
    + (* c = true *) reflexivity.
    + (* c = false *) reflexivity.
  - (* b = false *) destruct c.
    + (* c = true *) reflexivity.
    + (* c = false *) reflexivity.
  Qed.

Theorem mult_plus_distr_r : ∀ n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *) simpl. rewrite <- add_0_r. rewrite -> add_0_r. reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. rewrite -> add_assoc. reflexivity.
  Qed.


Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin)
.

Fixpoint incr (m:bin) : bin
  := match m with
     | Z    => B1 Z
     | B0 n => B1 n
     | B1 n => B0 (incr n)
     end.

Fixpoint bin_to_nat (m:bin) : nat
  := match m with
     | Z    => O
     | B0 n => (bin_to_nat n) + (bin_to_nat n)
     | B1 n => S ((bin_to_nat n) + (bin_to_nat n))
     end.

Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
  intros b.
  induction b as [| b' | b' ].
  - reflexivity.
  - reflexivity.
  - simpl.
    rewrite -> IHb'.
    simpl. rewrite <- plus_n_Sm.
    reflexivity.
Qed.

Fixpoint nat_to_bin (n : nat) : bin
  := match n with
     | 0    => Z
     | S n' => incr (nat_to_bin n')
     end.

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
  induction n as [|n'].
  - reflexivity.
  - simpl.
    rewrite -> bin_to_nat_pres_incr.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem bin_nat_bin_fails : ∀ b, nat_to_bin (bin_to_nat b) = b.
Abort.

Lemma double_incr : ∀ n : nat, double (S n) = S (S (double n)).
Proof.
  intros n. reflexivity.
  Qed.

Definition double_bin (b : bin) : bin :=
  match b with
  | Z => Z
  | B0 n => B0 (B0 n)
  | B1 n => B0 (B1 n)
  end.

Lemma double_incr_bin : ∀ b,
  double_bin (incr b) = incr (incr (double_bin b)).
Proof.
  intros b. induction b as [| b0' | b1' ].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  Qed.

Fixpoint normalize (b : bin) : bin :=
  match b with
  | Z     => Z
  | B0 b' => double_bin (normalize b')
  | B1 b' => incr (double_bin (normalize b'))
  end.

Lemma nat_to_bin_double : forall n : nat,
  nat_to_bin (double n) = double_bin (nat_to_bin n).
Proof.
  intros n.
  induction n.
  - reflexivity.
  - simpl. rewrite -> double_incr_bin. rewrite <- IHn.
    reflexivity.
Qed.

Theorem bin_nat_bin : forall b, nat_to_bin (bin_to_nat b) = normalize b.
Proof.
  intros b.
  induction b as [|b'|b'].
  - reflexivity.
  - simpl. rewrite <- IHb'.
    destruct (bin_to_nat b').
    + reflexivity.
    + rewrite <- double_plus. rewrite nat_to_bin_double.
      reflexivity.
  - simpl. rewrite <- IHb'.
    rewrite <- double_plus. rewrite nat_to_bin_double.
    reflexivity.
  Qed.

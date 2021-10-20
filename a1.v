(** Load required packages.  Not all of these packages are needed right away,
    but they may be useful later. **)

Require Export Setoid List Sorted Constructive_sets Utf8_core Wf_nat
        ProofIrrelevance Permutation IndefiniteDescription ChoiceFacts
        Description ssrfun ssrbool ssreflect.

(** Math symbols for cut and paste: ∀ ∃ → ↔ ∧ ∨ ¬ ≠ ≤ ≥ ∅ ℕ ℤ ∈ ∉ ⊂ ∑ ∏ λ **)

(** Axioms for the integers. **)

Parameter Z : Set.

Parameter add mult : Z → Z → Z.
Parameter neg : Z → Z.
Parameter zero one : Z.
Notation "0" := zero.
Notation "1" := one.
Infix "+" := add.
Infix "*" := mult.
Notation "- x" := (neg x).
Notation "- 0" := (neg 0).
Notation "- 1" := (neg 1).
Definition sub a b := a + -b.
Infix "-" := sub.

Axiom A1 : ∀ a b   : Z, a + b = b + a.
Axiom A2 : ∀ a b c : Z, a + (b + c) = (a + b) + c.
Axiom A3 : ∀ a     : Z, a + 0 = a.
Axiom A4 : ∀ a     : Z, a + -a = 0.
Axiom M1 : ∀ a b   : Z, a * b = b * a.
Axiom M2 : ∀ a b c : Z, a * (b * c) = (a * b) * c.
Axiom M3 : ∀ a     : Z, a * 1 = a.
Axiom D1 : ∀ a b c : Z, (a + b) * c = a * c + b * c.

(** Some useful lemmas. **)

Lemma S1 : ∀ a b c : Z, a = b → a + c = b + c.
Proof.
  intros a b c H.
  rewrite H.
  reflexivity.
Qed.

Lemma S2 : ∀ a b c : Z, a = b → a * c = b * c.
Proof.
  intros a b c H.
  rewrite H.
  reflexivity.
Qed.

(** Homework assignment problems are given below. **)

Theorem A1P1 : ∀ a : Z, 0 + a = a.
Proof.
  intros.
  rewrite A1.
  apply A3.
Qed.

Theorem A1P2 : ∀ a : Z, -a + a = 0.
Proof.
  intros.
  rewrite A1.
  apply A4.
Qed.

Theorem A1P3 : ∀ a : Z, 1 * a = a.
Proof.
  intros.
  rewrite M1.
  apply M3.
Qed.

Theorem A1P4 : ∀ a b : Z, a + b = 0 → b = -a.
Proof.
  intros.
  apply S1 with (c := -a) in H.
  rewrite A1P1 -A2 A1 -A2 A1P2 A3 in H.
  exact H.
Qed.

Theorem A1P5 : ∀ a : Z, -(-a) = a.
Proof.
  intros.
  assert (- a + a = 0).
  apply A1P2.
  apply A1P4 in H.
  symmetry.
  exact H.
Qed.

Theorem A1P6 : ∀ a : Z, 0 * a = 0.
Proof.
  intros.
  assert (0 * a + 0 * a = (0 + 0) * a).
    symmetry.
    apply D1.
  rewrite A3 in H.
  rewrite M1.
  apply S1 with (c := -(0 * a)) in H.
  rewrite -A2 in H.
  rewrite A4 in H.
  rewrite A3 in H.
  rewrite M1.
  exact H.
Qed.

Theorem A1P7 : ∀ a : Z, -1 * a = -a.
Proof.
  intros.
  assert ((1 + -1) * a = 0).
    rewrite A4.
    apply A1P6.
  rewrite D1 in H.
  rewrite M1 in H.
  rewrite M3 in H.
  apply A1P4.
  exact H.
Qed.

Theorem A1P8 : ∀ a b : Z, -a * -b = a * b.
Proof.
  intros.
  assert (∀ a0 : Z, -a0 = (-1) * a0).
    symmetry.
    apply A1P7.
  rewrite H.
  rewrite -M2.
  rewrite M1.
  rewrite -M2.
  rewrite M1.
  assert (∀ a : Z, a * -1 = -a).
    intros.
    rewrite M1.
    apply A1P7.
  rewrite H0.
  rewrite A1P5.
  apply M1.
Qed.

Theorem A1P9 : ∀ a b : Z, a + b = a → b = 0.
Proof.
  intros.
  rewrite A1 in H.
  apply S1 with (c := -a) in H.
  rewrite A4 -A2 A4 A3 in H.
  exact H.
Qed.

Theorem A1P10 : ∀ a b : Z, a * b = a → b = 1.
Proof.
(* 
  Not necessarily true because a could be zero.
  Disproof is shown below.
*)
Admitted.

(*
  The falseness of the following assumes that 0 != 1.
*)

Axiom zero_is_not_one : ¬ 0 = 1.

Theorem not_A1P10 : ¬ ∀ a b : Z, a * b = a → b = 1.
Proof.
unfold not.
  intros.
  assert (0 = 1).
  apply H with (a := 0).
  by rewrite A1P6.
  by apply zero_is_not_one.
Qed.

(* 
  For problems 10 and 11.

  The definitions above are only defined for rings and P11 is actually 
  untrue in general for rings. A simple counter example is that in Z_6,
  2 and 3 have product 0, but 2 and 3 are both non-zero. Thus, we need 
  additional constraints for this to be true. 

  I considered a few axioms for this problem such as the assertion that
  Z has an infinite number of elements, but I found that a total 
  ordering is the simplest (albeit possibly not the broadest) constraint
  required for Theorem A1P11 and a modified A1P10 to be true.

  I also need law of excluded middle (ClassicalEpsilon is imported later).
*)

Parameter greater_than : Z → Z → Prop.
Infix ">" := greater_than.
Definition lesser_than b a := a > b.
Infix "<" := lesser_than.

Theorem O1: ∀ a b, a > b ↔ b < a.
Proof.
  intros.
  unfold lesser_than.
  split; trivial.
Qed.

(* 
  The following axioms are required for a sense of order in the integers.
  The first axiom allows for order to be used to prove statements about 
  equalities while the second allows certain orders to be preserved under
  multiplication.
*)
Axiom O2: ∀ a b, (¬ a = b) ↔ (a > b ∨ a < b).
Axiom O3: ∀ a b c, a > b → ((c > 0 → a * c > b * c) ∧ (c < 0 → a * c < b * c)). 

Lemma modus_tollens : ∀ p q : Prop, (p → q) → ¬ q → ¬ p.
Proof.
  intros.
  Locate "¬".
  unfold not.
  intros.
  apply H in H1.
  contradiction.
Qed.

Require Import ClassicalEpsilon.

Lemma NNPP : ∀ p, ¬ ¬ p → p.
  Proof.
  intros.
  pose proof (classic p) as H0.
  destruct H0.
  - exact H0.
  - contradiction.
Qed.

Lemma contrapositive: ∀ p q: Prop, (¬ p → ¬ q) → (q → p).
Proof.
  intros.
  pose proof (classic p).
  destruct H1.
  - exact H1.
  - apply H in H1. contradiction.
Qed.

Lemma deMorgans: ∀ p q: Prop, ¬ (p ∨ q) → (¬ q ∧ ¬ p).
Proof.
  intros.
  pose proof (classic p).
  destruct H0.
  - assert (p ∨ q). auto. contradiction.
  - pose proof (classic q). destruct H1.
    -- assert (p ∨ q). auto. contradiction.
    -- auto.
Qed. 

(* the error was that A1P10 was applied but b could be 0. *)
Theorem A1P11 : ∀ a b : Z, a * b = 0 → a = 0 ∨ b = 0.
Proof.
  intros a b.
  apply contrapositive.
  intros.
  apply deMorgans in H.
  destruct H.
  apply O2 in H, H0.
  destruct H.
  - destruct H0.
    -- assert (a * b > 0 * b). 
      apply (O3 a 0 b). exact H0. exact H. 
      rewrite A1P6 in H1.
      apply O2. left. exact H1.
    -- assert (b * a < 0 * a).
      apply O3. exact H. exact H0.
      rewrite A1P6 M1 in H1.
      apply O2. right. exact H1.
  - destruct H0.
    -- assert (a * b < 0 * b). 
      apply O3. exact H0. exact H. 
      rewrite A1P6 in H1.
      apply O2. right. exact H1.
    -- assert (0 * b < a * b).
      apply O3. apply O1. exact H0. exact H. 
      rewrite A1P6 in H1.
      apply O2. left. apply O1. exact H1.
Qed.

Theorem A1P10_corrected : ∀ a b : Z, (a * b = a ∧ ¬ a = 0) → b = 1.
Proof.
  intros.
  rewrite M1 in H.
  destruct H.
  apply S1 with (c := -a) in H.
  rewrite A4 -A1P7 -D1 in H.
  apply A1P11 in H.
  destruct H.
  - apply S1 with (c := 1) in H.
    assert (-1 + 1 = 0).
      rewrite A1.
      apply A4.
    rewrite -A2 H1 A3 A1P1 in H.
    exact H.
  - contradiction.
Qed.

(*
  A1P12

  Firstly, order can be redefined using broader
  axioms than those stated above, and have those
  proven. These new axioms will be prepended with
  N instead of O.

  Secondly, induction is required for many proofs, 
  such as the fundamental theorem of arithmetic,
  as well as A3.
*)

Axiom N1: ∀ a b, (¬ a = b) ↔ (a > b ∨ a < b).
Axiom N2: ∀ a b c, a > b ∧ b > c → a > c.
Axiom N3: ∀ a b c, a > b → a + c > b + c.
Axiom N4: 1 > 0.

(*
  These alone with induction are sufficient
  for proving O3, for example.
*)

Axiom induction: ∀ P: Z → Prop, P 1 → (∀ k, k > 0 → P k → P (k + 1)) → (∀ k, k > 0 →  P k).

Lemma C1: ∀ a b c d, a > b ∧ c > d → a + c > b + d.
Proof.
  intros.
  destruct H.
  assert (a + c > b + c).
  apply N3. exact H.
  assert (b + d < b + c).
  rewrite A1. unfold lesser_than. rewrite A1.
  apply N3. exact H0. unfold lesser_than in H2.
  apply N2 with (b := b + c). 
  split; trivial.
Qed.

Lemma C2 : ∀ a b, a > b → -b > -a.
Proof.
  intros.
  apply N3 with (c := -a) in H.
  rewrite A4 in H.
  apply N3 with (c := -b) in H.
  rewrite A1P1 in H.
  rewrite A1 A2 A1P2 A1P1 in H. 
  exact H.
Qed.

(*
  Something that I thought was an axiom is 
  the following, which consequently shows the
  importance of N2.
*)

Lemma C3: ∀ a b, ¬ (a > b ∧ b > a).
Proof.
  intros.
  pose proof (classic (a > b ∧ b > a)).
  destruct H. destruct H.
    assert (a > a).
      apply N2 with (b := b). 
      split; trivial.
    assert (¬ a = a).
      apply N1. left. exact H1.
    contradiction H2.
    reflexivity.
  exact H.
Qed.

Axiom D2 : ∀ a b c : Z, c * (a + b) = c * a + c * b.

(* The following is a proof of the two parts of Axiom O3. *)

Theorem C4: ∀ a b c, a > b → c > 0 → a * c > b * c.
Proof.
  intros.
  assert (a * 1 > b * 1). 
    by rewrite ? M3.
  assert (∀ k: Z, a * k > b * k → a * (k + 1) > b * (k + 1)). 
    intros.
    rewrite ? D2 ? M3.
    apply C1. split; trivial.
  apply (induction (λ d, a * d > b * d)).
  trivial.
  intros.
  by apply H2 in H4.
  trivial.
Qed.

Theorem C5: ∀ a b c, a > b → c < 0 → a * c < b * c.
  intros.
  assert (∀ x, x * -1 = -x).
    intro. by rewrite M1 A1P7.
  assert (a * -1 < b * -1). 
    rewrite ? H1. by apply C2.
  assert (∀ k: Z, a * -k < b * -k → a * -(k + 1) < b * -(k + 1)).
    intros.
    rewrite ? D2 ? M3.
    unfold lesser_than.
    rewrite -A1P7.
    rewrite M1.
    assert (∀ x y z, x * (y + z) = x * y + x * z).
      intros.
      rewrite M1 D1 M1.
      assert (∀ r s t, r = s → t + r = t + s).
        intros.
        rewrite H4.
        reflexivity. 
      apply H4 with (t := x * y).
      apply M1.
    rewrite H4 H4 D1 A1P7 -M2 A1P3 A1P7 M2.
    rewrite H1 M3.
    apply C1. split.
    rewrite M1. exact H3.
    apply C2. exact H.
  remember (-c) as e.
    assert (- e = c).
      rewrite -A1P7 in Heqe.
      apply S2 with (c := -1) in Heqe.
      rewrite M1 A1P7 M1 M2 A1P8 -M2 M1 M3 M1 M3 in Heqe.
      exact Heqe.
  rewrite -H4.
  apply (induction (λ d, a * - d < b * - d)).
  exact H2.
  intros.
  by apply H3 in H6.
  rewrite -H4 in H0.
  apply N3 with (c := e) in H0.
  by rewrite A1P1 A1P2 in H0.
Qed.

(* 
  Another thing N3 shows is that there is an infinite number
  of integers, which I will not prove in coq here since it 
  takes numerous new definitions. Essentially, if integers have
  a finite number of elements, then let the greatest element be n.
  By N4, 1 > 0 and by N3, n + 1 > n, which contradicts the maximality
  of n since n + 1 is also an integer, and by N1 it's a different
  element from n. This will be important later.
*)

(*
  Regarding the completeness of these axioms, there is no
  way to directly verify. However, to falsify the completeness
  of the axioms, it would take a statement that can be 
  shown to be impossible to prove or disprove using the 
  axiomatic algebraic properties. For example, the fact
  that there exists examples of rings that satisfied P11 
  (integers for example) and examples that did not satisfy 
  P11 (Z_6) was sufficient to show that the axioms
  of rings are incomplete for dealing with integers.
  
  Consequently, not finding any such statements with a 
  certain set of axioms would suggest that these axioms 
  are likely complete. Thus, seeing that what's expected 
  to be true (such as the examples above) can be proven
  it is safe to say that these axioms are likely close to 
  complete.

  However, a step to further verify that these axioms
  describe integers is to check if these axioms 
  differentiate itself from other rings up to isomorphism 
  (credits to Christopher for this idea). For example, 
  axioms involving order distinguish the integers from 
  rings that are finite and cyclic under addition such as 
  Z_n. 

  According to Wikipedia (https://www.wikiwand.com/en/Cyclic_group),
  the only infinite cyclic group is Z, and as the axioms
  already show that Z is infinite, we only have to show that 
  Z is cyclic under addition, that is, every element can be 
  generated by 1 under addition. 
  
  In other words, every element can be written in the form 
  1 + 1 + 1 ... 1 or - 1 - 1 - 1 ... 1. We can show this
  inductively, that x is in Z if either x is 0 or one of
  x - 1 and x + 1 is in Z, which is clearly true since 
  by definition the codomain of integer addition are integers.

  Thus, these axioms show that Z is cyclic under addition,
  and thus uniquely characterizes Z as the set of integers.

  A problem with this is that this does not uniquely define
  the multiplication operator, however. Unfortunately, I 
  do not know how to prove that it does or does not.
*)

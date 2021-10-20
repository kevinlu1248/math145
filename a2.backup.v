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

(* COPY OF A1 QUESTIONS: *)

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

(* A2 Solutions begin here: *)

Parameter lt : Z → Z → Prop.
Infix "<" := lt.
(* Notation "a > b" := (b < a) (only parsing). *)
(* My code doesn't work with the above notation. *)

Definition gt a b := b < a.
Infix ">" := gt.

Lemma lt_and_gt: ∀ a b, a > b ↔ b < a.
Proof.
    intros.
    split; trivial.
Qed.

Lemma gt_to_lt: ∀ a b, a > b → b < a.
Proof.
    trivial.
Qed.

Lemma lt_to_gt: ∀ a b, a < b → b > a.
Proof.
    trivial.
Qed.

Definition divide (x y : Z) := ∃ z : Z, y = z * x.
Notation "( x | y )" := (divide x y).

Axiom N1: ∀ a b, (¬ a = b) ↔ (a > b ∨ a < b).
Axiom N2: ∀ a b c, a > b ∧ b > c → a > c.
Axiom N3: ∀ a b c, a > b → a + c > b + c.
Axiom N4: 1 > 0.

Theorem A2P1 : ∀ a m n x y : Z, (a | m) → (a | n) → (a | m * x + n * y).
Proof.
    unfold divide.
    intros.
    destruct H. destruct H0 as [y0].
    assert ((x0 * x + y0 * y) * a = m * x + n * y).
        rewrite D1 (M1 x0 x) -M2 -H.
        rewrite (M1 y0 y) -M2 -H0.
        by rewrite M1 (M1 y n).
    exists (x0 * x + y0 * y).
    by rewrite H1.
Qed.

Theorem A2P2: ∀ a b c : Z, (a | b) → (b | c) → (a | c).
Proof.
    unfold divide.
    intros.
    destruct H as [r]. destruct H0 as [s].
    rewrite H in H0.
    exists (s * r).
    by rewrite M2 in H0.
Qed.

Theorem A2P3 : ∀ a b : Z, a < b ∨ a = b ∨ b < a.
Proof.
    intros.
    pose proof (classic (a = b)).
    destruct H. 
    - right. by left.
    - apply N1 in H. destruct H.
        -- right. by right. 
        -- by left. 
Qed.

(* Need induction for P4+ *)

Axiom induction: ∀ P: Z → Prop, P 1 → (∀ k, k > 0 → P k → P (k + 1)) → (∀ k, k > 0 →  P k).

Lemma C1: ∀ a b c d, a > b ∧ c > d → a + c > b + d.
Proof.
  intros.
  destruct H.
  assert (a + c > b + c).
  apply N3. exact H.
  assert (b + d < b + c).
  rewrite A1. unfold lesser_than. rewrite (A1 b c).
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

Lemma D2 : ∀ a b c : Z, c * (a + b) = c * a + c * b.
Proof.
    intros.    
    by rewrite M1 D1 M1 (M1 c b).
Qed.

Lemma C4: ∀ a b c, a > b → c > 0 → a * c > b * c.
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

Theorem A2P4 : ∀ a b c : Z, a < b → 0 < c → a * c < b * c.
Proof.
    intros.
    apply lt_and_gt.
    apply C4.
    trivial.
    trivial.
Qed.

Lemma C5: ∀ a b c, a > b → c < 0 → a * c < b * c.
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
        rewrite M1 in H3. exact H3.
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

Theorem A2P5 : ∀ a b c : Z, a * c = b * c → c ≠ 0 → a = b.
Proof.
    intros.
    assert (¬ a = b → ¬ a * c = b * c).
      - intros.
        apply N1 in H0. destruct H0.
        -- apply N1 in H1. destruct H1.
          --- apply N1. left. by apply C4.
          --- apply N1. right. by apply C4.
        -- apply N1 in H1. destruct H1.
          --- apply N1. right. by apply C5.
          --- apply N1. left. by apply C5.
    - by apply contrapositive with (p := (a = b)) (q := (a * c = b * c)) in H1.
Qed.  

Theorem A2P6 : ∀ a b c : Z, a < b → b < c → a < c.
Proof.
    intros.
    apply gt_to_lt.
    apply N2 with (b := b).
    split; trivial.
Qed.

Theorem A2P7 : ∀ a : Z, ¬ a < a.
Proof.
    unfold not.
    intros.
    assert (¬ a = a).
    apply N1. by left. 
    by contradiction H0.
Qed.

Notation "2" := (1+1).

(* Some lemmas for A1P8 *)

Lemma consistency: ∀ a b : Z, a > b → ¬ (a < b).
Proof.
  intros.
  pose proof (classic (a < b)).
  destruct H0.
  - assert (a > a).
      apply (N2 a b a). split; trivial.
    apply gt_to_lt in H1.
    by pose proof (A2P7 a).
  - trivial.
Qed. 

Lemma one_not_two: ¬ 1 = 2.
Proof.
  intro.
  apply S1 with (c := -1) in H.
  rewrite A4 -A2 A4 A3 in H.
  assert (¬ 0 = 1).
    apply N1. right. apply N4.
  contradiction.
Qed.

(* The following is the proof of the "step_down" lemma for A1P8. *)

Definition leq a b := a < b ∨ a = b.
Definition geq a b := (a > b ∨ a = b).
Infix "≤" := leq (at level 70).
Infix "≥" := geq (at level 70).

Definition subset_of_nats (S : Z → Prop) : Prop := ∀ a, S a → a > 0.

Lemma deMorgans_generalized : ∀ A (P : A → Prop), (∀ x, P x) ↔ ¬ (∃ x, ¬ P x).
Proof.
  (* Copied from pre-assessment *)
  intros.
  split.
  - unfold not.
  intros.
  destruct H0.
  apply H0.
  apply H.
  - unfold not.
  intros.
  pose proof (classic (P x)).
  destruct H0.
  exact H0.
  contradiction H.
  exists x.
  exact H0.
Qed.

Lemma deMorgans_generalized2: ∀ A (P : A → Prop), (∃ x, P x) ↔ ¬ (∀ x, ¬ P x).
Proof.
intros. split.
- firstorder.
- apply contrapositive. firstorder.
Qed.

(* Principle of strong induction *)
Lemma POSI: ∀ P: Z → Prop, 
  P 1 → (∀ k, k > 0 → (∀ j, j > 0 → j < k → P k) → P (k + 1)) 
  → (∀ k, k > 0 → P k).
Proof.
Admitted.

(* Well-ordering Principle *)
Theorem WOP: ∀ S, subset_of_nats S → (∃ n, n > 0 → S n) → (∃ m, S m ∧ ∀ n, S n → m ≤ n).
Proof.
  (* Based on Prof. Brannon's proof in Math 147. *)
  intros.
  unfold subset_of_nats in H.
  apply deMorgans_generalized2 in H0.
  pose proof (classic (∃ m : Z, S m ∧ (∀ n : Z, S n → m ≤ n))).
  destruct H1.
  trivial.
  contradiction H0.
  assert (∀ x : Z, x > 0 → ¬ S x).
    apply (POSI (λ x, ¬ S x)).
    admit.
    admit.
  unfold not. intros.
  apply H2 in H3.
  trivial.
  apply H. 
  apply H3.
  admit.
  admit.
Admitted.
  (* contradiction H0. *)
  (* unfold not. intros. *)

Theorem zero_one_consecutive: ∀ a, ¬ (0 < a ∧ a < 1).
Proof.
  unfold not. intros.
  destruct H.
  remember ((λ n, 0 < n ∧ n < 1)) as S.
  pose proof (WOP S).
  assert (subset_of_nats S).
    unfold subset_of_nats.
    intros.
    rewrite HeqS in H2.
    by destruct H2.
  apply H1 in H2.
  pose proof (classic (∃ x : Z, S x)) as existence_hypothesis.
  destruct existence_hypothesis.
  - destruct H2 as [m].
    destruct H2.
    apply deMorgans_generalized in H4.
    contradiction H4.
    exists (m * m).
    rewrite HeqS in H2.
    destruct H2.
    assert (m > m * m).
      pose proof (C4 1 m m).
        assert (1 * m > m * m).
        by apply H6.
      rewrite M1 M3 in H6.
      by apply H6.
    assert (S (m * m)).
      rewrite HeqS.
      split.
        pose proof (C4 m 0 m).
          rewrite A1P6 in H7.
          by apply H7.  
        by apply N2 with (b := m).
    assert (¬ m ≤ m * m).
      unfold leq.
      pose proof (classic (m < m * m ∨ m = m * m)).
        destruct H8.
          (* Case 1 *)
          destruct H8.
          (* Case 1a *)
            assert (¬ m < m * m). by apply consistency.
            contradiction.
          (* Case 1b *)
            assert (¬ m = m * m).
              apply N1. by left.
              contradiction.
          (* Case 2 *)
          trivial.
    firstorder.
  - contradiction H3.
    exists a.
    by rewrite HeqS.
  - exists a.
    by rewrite HeqS.
Qed.

Theorem step_up: ∀ a, a > 0 → ¬ (a < 1).
Proof.
  apply (induction (λ n, ¬ (n < 1))).
  unfold not. 



Theorem discreteness_of_ints: ∀ a b, ¬ (b < a ∧ a < b + 1).
Proof.
  unfold not. intros.
  destruct H.
  pose proof (zero_one_consecutive (a - b)).
  contradiction H1.
  split.
  - apply N3 with (c := -b) in H.
    by rewrite A4 in H.
  - apply N3 with (c := -b) in H0. 
    by rewrite A1 A2 (A1 (-b) b) A4 A1 A3 in H0.
Qed.
  
Theorem step_down: ∀ a b, a < b → (a ≤ b + -1).
Proof.
  intros.
  pose proof (A2P3 a (b + -1)).
  destruct H0.
  - by left.
  - destruct H0.
    -- by right.
    -- pose proof (discreteness_of_ints a (b + -1)).
      contradiction H1.
      split.
      --- trivial.
      --- by rewrite -A2 (A1 (-1) 1) A4 A3.
Qed.


Theorem A2P8 : ¬ (2 | 1).
Proof.
    unfold not. unfold divide. intros.
    destruct H. 
    assert (x < 0 ∨ x = 0 ∨ 0 < x). apply A2P3.
    assert (¬ x < 0).
      pose proof (classic (x < 0)). 
      destruct H1.
        assert (x * 2 < 0 * 2). 
          apply C4. trivial.
        assert (2 > 0 + 0).
          apply (C1 1 0 1 0). split; apply N4.  
        by rewrite A3 in H2.
        rewrite -H A1P6 in H2.
        apply (consistency 1 0) in H2.
        contradiction.
        apply N4.
      trivial. 
    assert (¬ x = 0).
      pose proof (classic (x = 0)). 
      destruct H2.
        assert (¬ 1 = 0).
          apply N1. left. apply N4.
        assert (1 = 0 * 2). by rewrite -H2.
        rewrite A1P6 in H4. 
        contradiction.
      trivial.
    destruct H0.
    - contradiction.
    - destruct H0.
      -- contradiction. 
      -- pose proof (A2P3 x 1).
        destruct H3.
        --- apply step_down in H3.
          destruct H3.
          ---- by rewrite A4 in H3.
          ---- by rewrite A4 in H3. 
        --- destruct H3. 
          ---- rewrite H3 M1 M3 in H.
            by apply one_not_two.
          ---- apply C4 with (c := 2) in H3.
            ----- rewrite (M1 1 2) M3 in H3.
              rewrite -H in H3. 
              apply N3 with (c := -1) in H3.
              rewrite A4 -A2 A4 A3 in H3.
              assert (¬ 0 > 1). 
                apply consistency. apply N4.
              contradiction.
            ----- pose proof (C1 1 0 1 0).
              rewrite A3 in H4. apply H4. split; apply N4.
Qed.

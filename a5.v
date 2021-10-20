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

Axiom N1: ∀ a b, (¬ a = b) ↔ (a > b ∨ a < b).
Axiom N2: ∀ a b c, a > b ∧ b > c → a > c.
Axiom N3: ∀ a b c, a > b → a + c > b + c.
Axiom N4: 1 > 0.


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

(* Parameter lt : Z → Z → Prop.
Infix "<" := lt.

Definition gt a b := b < a.
Infix ">" := gt. *)

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
        rewrite M1 in H3. by rewrite M1 (M1 a (-k)).
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

Lemma not_less_eq_geq: ∀ a b, ¬ a < b ↔ a ≥ b.
Proof.
  intros.
  split.
  pose proof (A2P3 a b).
  - destruct H.
    -- by intros.
    -- intros.
      destruct H.
      --- by right.
      --- by left.    
  - intros. 
    destruct H.
    -- unfold not. intro.
      assert (a > a).
        apply (N2 a b a). 
        split; trivial.
      by apply (A2P7 a).
    -- unfold not. intro.
      pose proof N1.
      assert (a > b ∨ a < b).
        by right.
      by apply H1 in H2.
Qed.

Theorem step_up: ∀ a, a > 0 → ¬ (a < 1).
Proof.
  assert (2 > 1).
    pose proof N4.
    apply N3 with (c := 1) in H.
    by rewrite A1 A3 in H.
  apply (induction (λ n, ¬ (n < 1))).
  unfold not. intros.
  - by apply A2P7 in H0.
  - intros.
    apply not_less_eq_geq.
    apply not_less_eq_geq in H1.
    destruct H1.
    -- apply N3 with (c := 1) in H1.
      left.
      apply N2 with (b := 2).
      split; trivial.
    -- rewrite H1.
      by left.
Qed.  

Theorem zero_one_consecutive: ∀ a, ¬ (0 < a ∧ a < 1).
Proof.
  unfold not.
  intros.
  destruct H. 
  apply step_up in H.
  contradiction.
Qed.

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

Lemma O3: ∀ a b c, a > b → ((c > 0 → a * c > b * c) ∧ (c < 0 → a * c < b * c)). 
Proof.
  intros.
  split.
  - by apply C4.
  - by apply C5.
Qed.

Theorem A1P11 : ∀ a b : Z, a * b = 0 → a = 0 ∨ b = 0.
Proof.
  intros a b.
  apply contrapositive.
  intros.
  apply deMorgans in H.
  destruct H.
  apply N1 in H, H0.
  destruct H.
  - destruct H0.
    -- assert (a * b > 0 * b). 
      apply (O3 a 0 b). exact H0. exact H. 
      rewrite A1P6 in H1.
      apply N1. left. exact H1.
    -- assert (b * a < 0 * a).
      apply O3. exact H. exact H0.
      rewrite A1P6 M1 in H1.
      apply N1. right. exact H1.
  - destruct H0.
    -- assert (a * b < 0 * b). 
      apply O3. exact H0. exact H. 
      rewrite A1P6 in H1.
      apply N1. right. exact H1.
    -- assert (0 * b < a * b).
      apply O3. apply O1. exact H0. exact H. 
      rewrite A1P6 in H1.
      apply N1. left. apply O1. exact H1.
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


(* Notation "a ≥ b" := (b ≤ a) (at level 70, only parsing). *)
Notation "a < b < c" := (a < b ∧ b < c).
Notation "a ≤ b < c" := (a ≤ b ∧ b < c) (at level 70, b at next level).
Notation "a < b ≤ c" := (a < b ∧ b ≤ c) (at level 70, b at next level).
Notation "a ≤ b ≤ c" := (a ≤ b ∧ b ≤ c) (at level 70, b at next level).

Definition pm (a b : Z) := (a = b ∨ a = -b).
Notation "a = ± b" := (pm a b) (at level 60).
Notation "x ≠ ± y" := (¬ (x = ± y)) (at level 60).
Definition assoc (a b : Z) := (a | b) ∧ (b | a).
Infix "~" := assoc (at level 70).
Definition unit a := (a | 1).

Theorem A3P1 : 0 ≠ 1.
Proof.
  pose proof N4.
  apply N1.
  by right.
Qed.

Theorem A3P2 : ∀ a b : Z, 0 < a → (0 < b ↔ 0 < a * b).
Proof.
  intros.
  split.
  - intro. 
    pose proof (C4 a 0 b).
    apply H1 in H; trivial.
    by rewrite A1P6 in H.
  - apply contrapositive. 
    intro.
    apply not_less_eq_geq in H0.
    destruct H0.
    + pose proof (C5 a 0 b).
      rewrite A1P6 in H1.
      apply not_less_eq_geq.
      left. 
      apply H1; trivial.
    + rewrite -H0 M1 A1P6.
      apply A2P7.
Qed.

Theorem A3P3a : ∀ a b, a < b ↔ ¬ b ≤ a.
Proof.
  intros.
  pose proof (A2P3 a b).
  split.
  - destruct H as [|[|]].
    -- intro.
      unfold not. intro.
      destruct H1.
      + pose proof (A2P6 a b a). 
        apply H2 in H1; trivial.
        by apply A2P7 in H1.
      + rewrite H1 in H.
        by apply A2P7 in H.
    -- intros.
      rewrite H in H0.
      by apply A2P7 in H0.
    -- intro. 
      pose proof (A2P6 a b a).
      apply H1 in H; trivial.
      by apply A2P7 in H.
  - intros.
    destruct H as [|[|]]; trivial.
    -- contradiction H0.
      by right.
    -- contradiction H0.
      by left.
Qed.

Theorem A3P3b : ∀ a b, a ≤ b ↔ ¬ b < a.
Proof.
  intros.
  pose proof (not_less_eq_geq b a).
  firstorder.
Qed.

Lemma leq_add: ∀ a b c, a ≤ b → a + c ≤ b + c.
Proof.
  intros.
  destruct H.
  - left. by apply N3. 
  - right. by rewrite H. 
Qed.

Theorem A3P4 : ∀ a : Z, 0 < a → ¬ a < 1.
Proof.
  intros.
  pose proof (step_down 0 a).
  apply H0 in H.
  apply (leq_add _ _ 1) in H.
  rewrite A1P1 -A2 A1P2 A3 in H.
  by apply A3P3b.
Qed.

Theorem not_A3P5 : ¬ (∀ a b, (a | b) → a ≤ b).
Proof.
  unfold not. intros.
  pose proof (H 1 (-1)).
  assert (1 > (-1)).
    pose proof N4.
    apply (N3 _ _ (-1)) in H1.
    rewrite A4 A1P1 in H1.
    apply (A2P6 (-1) 0 1); trivial.
    apply N4.
  assert (1 | (-1)).
    unfold divide.
    exists (-1).
    by rewrite M3.
  apply H0 in H2.
  destruct H2.
  - pose proof (A2P6 1 (-1) 1).
    apply H3 in H1; trivial.
    by apply A2P7 in H1.
  - rewrite -H2 in H1.
    by apply A2P7 in H1.
Qed.

Theorem A3P5_corrected : ∀ a b : Z, (a | b) → 0 < b → a ≤ b.
Proof.
  intros.
  unfold divide in H.
  destruct H.
  pose proof (A2P3 x 1).
  destruct H1 as [|[|]].
  - apply step_down in H1. 
    rewrite A4 in H1.
    destruct H1.
    + pose proof (A2P3 a 0).
      destruct H2 as [|[|]].
      -- left. apply A2P6 with (b := 0); trivial.
      -- rewrite H2 M1 A1P6 in H. 
        rewrite H in H0.
        by apply A2P7 in H0.
      -- pose proof (C4 0 x a).
        apply H3 in H1; trivial.
        rewrite -H A1P6 in H1.
        pose proof (A2P6 b 0 b).
        apply H4 in H1; trivial.
        by apply A2P7 in H1.
    + rewrite H1 A1P6 in H.
      rewrite H in H0.
      by apply A2P7 in H0.
  - rewrite H1 A1P3 in H.
    by right.
  - pose proof (A2P3 a 0).
    destruct H2 as [|[|]].
    + left.
      apply (A2P6 a 0 b); trivial.
    + rewrite -H2 in H0. 
      by left.
    + pose proof (C4 x 1 a).
      apply H3 in H1; trivial.
      rewrite -H A1P3 in H1.
      by left.
Qed.

Theorem A3P6 : ∀ a, unit a ↔ a = ± 1.
Proof.
  unfold unit, pm.
  intros.
  split.
  intro.
  - destruct (A2P3 a 0) as [|[|]].
    + assert ((-a) | 1).
        destruct H.
        exists (-x).
        by rewrite A1P8.
      apply A3P5_corrected in H1; try apply N4.
      destruct H1.
      -- apply C2 in H1.
        rewrite A1P5 in H1.
        contradiction (discreteness_of_ints a (-1)).
        rewrite A1P2.
        split; trivial.
      -- right. 
        apply (S2 _ _ (-1)) in H1.
        by rewrite M1 A1P7 A1P5 A1P3 in H1.
    + destruct H.
      rewrite H0 M1 A1P6 in H.
      pose proof N4.
      rewrite H in H1.
      by apply A2P7 in H1.
    + apply A3P5_corrected in H.
      -- destruct H.
        ++ contradiction (zero_one_consecutive a); auto.
        ++ by left. 
      -- apply N4.
  - intro. destruct H. 
    + exists 1. 
      by rewrite H M3.
    + exists (-1).
      by rewrite H A1P8 M3.
Qed.

(* The following is the proof of A3P8 (WOP). 
  The proof of WOP and POSI are both
  based on proofs presented by Prof.
  Brannon in Math 147 lectures. *)

Lemma strongly_connected: ∀ a b, (a ≤ b ≤ a) → a = b.
Proof.
  intros.
  destruct H.
  destruct (A2P3 a b); try exact.
  - destruct H0; try exact.
    pose proof (A2P6 a b a).
    apply H2 in H0; try exact.
    by contradiction (A2P7 a).
  - destruct H1; try exact. 
    pose proof (A2P6 a b a).
    destruct H; try exact.
    apply H2 in H1; try exact.
    by contradiction (A2P7 a).
Qed.

(* Principle of Strong Induction *)
Theorem POSI: ∀ S : Z → Prop, 
  (S 1) → (* Base case *)
  (∀ n, 0 < n → (∀ m, (0 < m < n) → S m) → S n) → (* Inductive step *)
  (∀ x, 0 < x → S x). (* final goal*)
Proof.
  intros.
  remember (λ n, 0 < n ∧ (∀ m, 0 < m ≤ n → S m)) as P.
  assert (P x).
    apply induction; try exact.
    - rewrite HeqP.
      split; try apply N4.
      intros.
      assert (m = 1).
        destruct H2.
        apply step_down, (leq_add _ _ 1) in H2.
        rewrite A1P1 -A2 A1P2 A3 in H2.
        by apply strongly_connected.
      by rewrite H3.
    - intros.
      rewrite HeqP in H3.
      rewrite HeqP.
      destruct H3.
      split.
      + assert (k < k + 1).
          pose proof N4.
          pose proof (N3 1 0 k).
          apply H6 in H5.
          by rewrite A1 A1P1 in H5.
        by apply (A2P6 _ k _).
      + intros.
        destruct (classic (m ≤ k)).
        * apply H4.
          split; firstorder.
        * apply A3P3a in H6.
          assert (m = k + 1).
            destruct H5.
            apply step_down in H6.
            apply (leq_add _ _ 1) in H6.
            rewrite -A2 A1P2 A3 in H6.
            by apply strongly_connected.
          rewrite H7.
          apply H0.
          -- assert (k < k + 1).
              pose proof N4.
              pose proof (N3 1 0 k).
              apply H9 in H8.
              by rewrite A1 A1P1 in H8.
            by apply (A2P6 _ k _).
          -- intros. 
            apply H4. 
            split.
            ++ firstorder.
            ++ destruct H8.
              apply step_down in H9.
              by rewrite -A2 A4 A3 in H9.
    - rewrite HeqP in H2.
      firstorder.
Qed.

Theorem DeMorgansGeneralized: ∀ P : Z → Prop, ¬ (∃ n, P n) ↔ ∀ n, ¬ P n.
Proof.
  firstorder.
Qed.

Theorem DeMorgansGeneralized1: ∀ P : Z → Prop, (∃ x, P x) ↔ ¬ (∀ x, ¬ P x).
Proof.
  split.
  - firstorder.
  - apply contrapositive.
    firstorder.
Qed.

(* Well-ordering principle *)
Theorem A3P7 : ∀ S : Z → Prop,
    (∀ x, S x → 0 < x) → (∃ x, S x) → ∃ s, S s ∧ ∀ t, S t → s ≤ t.
Proof.
  intros.
  pose proof (classic (∃ s : Z, S s ∧ (∀ t : Z, S t → s ≤ t))).
  destruct H1; trivial.
  assert (¬ (∃ x : Z, S x)); try contradiction.
    remember (λ x, ¬ S x).
    apply DeMorgansGeneralized.
    assert (∀ n, (¬ S n) = P n).
      by rewrite HeqP. 
    assert (∀ n, 0 < n → P n).
      apply POSI.
      - destruct (classic (P 1)); try exact.
        contradiction H1.
        exists 1.
        split.
        + rewrite -H2 in H3.
          by apply NNPP.
        + intros.
          apply H, step_down, (leq_add _ _ 1) in H4.
          by rewrite A1P1 -A2 A1P2 A3 in H4.
      - intros.
        destruct (classic (P n)); try exact.
        contradiction H1.
        exists n.
        split.
        + rewrite -H2 in H5.
          by apply NNPP in H5.
        + intros. 
          destruct (classic (n ≤ t)); try exact.
          apply A3P3a in H7.
          assert (P t).
            apply H4.
            split; firstorder.
          by rewrite -H2 in H8.
      - intro.
        pose proof (classic (0 < n)).
        destruct H4.
        + apply H3 in H4.
          by rewrite -H2 in H4.
        + pose proof classic (¬ S n).
          destruct H5; trivial. 
          apply NNPP in H5.
          by apply H in H5.
Qed.

Require Export Ring.
 
Add Ring Z_ring : (mk_rt _ _ _ _ _ _ _ A1P1 A1 A2 A1P3 M1 M2 D1
                         (λ a b, erefl (a - b)) A4).

(* Definition and properties of absolute value. *)

Require Export ClassicalDescription.

Section absolute_value.

  Definition abs a : Z :=
    if excluded_middle_informative (0 < a) then a else (-a).

  Notation "| a |" := (abs a) (at level 35, format "'|' a '|'").
  Notation "|- a |" := (abs (neg a)) (at level 35, format "'|-' a '|'").

  Lemma abs_pos : ∀ a : Z, 0 < a → |a| = a.
  Proof.
    intros a H.
    unfold abs.
    destruct excluded_middle_informative; simpl; auto.
    contradiction.
  Qed.

  Lemma abs_neg : ∀ a : Z, a < 0 → |a| = -a.
  Proof.
    intros a H.
    unfold abs.
    destruct excluded_middle_informative; simpl; auto.
    contradiction (A2P7 a); eauto using A2P6.
  Qed.

  Lemma abs_zero : |0| = 0.
  Proof.
    unfold abs.
    destruct excluded_middle_informative; simpl; auto.
    ring.
  Qed.

  Lemma abs_pm : ∀ a : Z, |a| = ± a.
  Proof.
    intros a.
    unfold abs, pm.
    destruct excluded_middle_informative; auto.
  Qed.

End absolute_value.

Notation "| a |" := (abs a) (at level 35, format "'|' a '|'").
Notation "|- a |" := (abs (neg a)) (at level 35, format "'|-' a '|'").

Theorem A4P1 : ∀ a : Z, |a| = |-a|.
Proof.
  intros.
  unfold abs.
  destruct excluded_middle_informative; simpl.
  - destruct excluded_middle_informative; simpl; try ring. 
    apply N3 with (c := a) in l0.
    rewrite A1P1 A1P2 in l0.
    by apply (consistency a 0) in l.
  - destruct excluded_middle_informative; simpl; trivial.
    destruct (A2P3 a 0) as [|[|]]; try contradiction.
    + apply C2 in H.
      by replace (-0) with 0 in H by ring.
    + subst; ring. 
Qed.

Theorem A4P2 : ∀ a : Z, 0 ≤ |a|.
Proof.
  intros. unfold abs.
  destruct excluded_middle_informative; simpl; try by left.
  apply A3P3b in n.
  apply leq_add with (c := (-a)) in n.
  by rewrite A4 A1P1 in n.
Qed.

Theorem A4P3 : ∀ a : Z, a ≤ |a|.
Proof.
  intros. unfold abs.
  destruct excluded_middle_informative; simpl; try by right.
  apply A3P3b in n; destruct n.
  - left. 
    assert (0 < -a).  
      apply N3 with (c := -a) in H.
      by rewrite A1P1 A4 in H.
    apply (N2 (-a) 0 a); split; try exact.
  - right; subst; ring.
Qed.

Theorem A4P4 : ∀ a b : Z, a ~ b ↔ ∃ u : Z, unit u ∧ b = a * u.
Proof.
  intros.
  split.
  - intro.
    destruct H.
    unfold divide in *.
    destruct H, H0.
    destruct (classic (b = 0)).
      exists 1. split.
      apply A3P6; firstorder. 
      rewrite H0 H1; ring.
    assert (b = x * x0 * b). 
      by rewrite -M2 -H0. 
    assert (x * x0 = 1).
      apply A1P10_corrected with (a := b).
      split; trivial.
      rewrite {2} H2; ring.
    exists x; split.
    + exists x0. rewrite -H3; ring.
    + rewrite H; ring.
  - intros.
    destruct H.
    destruct H.
    split; exists x.
    + by rewrite M1.
    + apply A3P6 in H.
      destruct H; subst; intuition ring.
Qed.

Theorem A4P5 : ∀ a b : Z, a ~ b ↔ a = ± b.
Proof.
  intros.
  split.
  - intro. 
    apply A4P4 in H.
    destruct H; destruct H.
    apply A3P6 in H; destruct H; subst.
    + left. ring.
    + right. ring. 
  - intro.
    apply A4P4.
    destruct H.
    + exists 1. split.
      * apply A3P6; by left.
      * subst; by rewrite M3. 
    + exists (-1); split.
      * apply A3P6; by right.
      * subst. ring.
Qed.

Lemma A4P6_helper: ∀ a b : Z, (a | b) → b ≠ 0 → 0 < b → a ≤ |b|.
Proof.
  intros.
  apply A3P5_corrected in H.
  - destruct H. 
    + pose proof (A4P3 b); firstorder.
      * left. by apply A2P6 with (b := b).
      * rewrite H2 in H; firstorder. 
    + rewrite H. apply A4P3.
  - apply N1 in H0. destruct H0; trivial.
Qed.

Theorem A4P6 : ∀ a b : Z, (a | b) → b ≠ 0 → a ≤ |b|.
Proof.
  intros.
  destruct (A2P3 b 0) as [|[|]]; try contradiction.
  - rewrite A4P1. apply (A4P6_helper a (-b)); trivial.
    + destruct H; exists (-x); rewrite H; ring.
    + unfold not; intros.
      apply (S1 _ _ b) in H2.
      rewrite A1P2 A1P1 in H2.
      by apply H0.
    + replace 0 with (-0) by ring.
      by apply C2.
  - apply A4P6_helper; try exact.
Qed.

(* This proof is probably very bloated *)
Theorem WOP_nonneg: ∀ S : Z → Prop,
    (∀ x, S x → 0 ≤ x) → (∃ x, S x) → ∃ s, S s ∧ ∀ t, S t → s ≤ t.
Proof.
  intros.
  remember (λ n, S (n - 1)).
  assert (∀ n, S n = P (n + 1)).
    rewrite HeqP.
    intro. by replace (n + 1 - 1) with n by ring.
  pose proof (A3P7 P).
  assert (∀ x : Z, P x → 0 < x).
  {
    intros. rewrite HeqP in H3. apply H in H3.
    apply (leq_add _ _ 1) in H3. rewrite A1P1 in H3.
    replace (x - 1 + 1) with x in H3 by ring.
    destruct H3.
    - apply N2 with (b := 1); split; trivial; apply N4.
    - rewrite -H3; apply N4. 
  }
  apply H2 in H3.
  rewrite HeqP in H3.
  destruct H3.
  destruct H3.
  exists (x - 1).
  split; try exact.
  intros.
  assert (∀ t : Z, S t → x ≤ t + 1).
    intros. apply H4.
    by replace (t0 + 1 - 1) with t0 by ring.
  apply H6 in H5.
  apply (leq_add _ _ (-1)) in H5.
  replace (t + 1 + -1) with t in H5 by ring.
  apply H5.
  rewrite HeqP.
  destruct H0.
  exists (x + 1).
  by replace (x + 1 - 1) with x by ring.
Qed.

(* Division algorithm *)
Theorem A4P7 : ∀ a b, 0 < a → 0 < b → ∃ q r : Z, a = b * q + r ∧ 0 ≤ r < b.
Proof.
  intros.
  remember (λ n, ∃ r, 0 ≤ n ∧ n = r * b + a) as S.
  assert (∃ s, S s ∧ ∀ t, S t → s ≤ t).
  {
    apply WOP_nonneg.
    - intros.
      rewrite HeqS in H1; firstorder.
    - exists a; rewrite HeqS.
      exists 0.
      split.
      + firstorder.
      + ring.
  }
  destruct H1 as [r].
  destruct H1.
  rewrite HeqS in H1.
  destruct H1.
  destruct H1.
  assert (r < b).
    destruct (classic (r < b)); try exact.
      apply A3P3b in H4.
    remember ((x - 1) * b + a) as r0.
    assert (S r0).
      rewrite HeqS.
      exists (x - 1).
      split.
      rewrite Heqr0.
      replace ((x - 1) * b + a) with (x * b + a - b) by ring.
      rewrite -H3.
      replace 0 with (b - b) by ring.
      by apply leq_add.
      exact.
    apply H2, A3P3b in H5; contradiction H5.
    rewrite Heqr0 H3.
    replace (x * b + a) with (-0 + (x * b + a)) by ring.
    replace ((x - 1) * b + a) with (-b + (x * b + a)) by ring.
    by apply N3, C2.
  exists (-x), r.
  split.
  - rewrite H3; ring.
  - split; trivial.
Qed.


(* "Relatively prime" *)
Definition rel_prime (a b : Z) := ∀ d : Z, (d | a) → (d | b) → unit d.

Theorem rel_prime_sym : ∀ a b : Z, rel_prime a b ↔ rel_prime b a.
Proof.
  firstorder.
Qed.

Theorem rel_prime_1 : ∀ a : Z, rel_prime a 1.
Proof.
  firstorder.
Qed.

Theorem A5P1 : ∀ a : Z, rel_prime a 0 ↔ unit a.
Proof.
  intro.
  split; intro.
  - unfold rel_prime in H.
    apply H.
    exists 1; ring.
    exists 0; ring.
  - unfold rel_prime.
    intros.
    apply A2P2 with (b := a); trivial.
Qed.

Theorem A5P2 : ∀ a b : Z, rel_prime a b ↔ rel_prime a (-b).
Proof.
  intros a b.
  split; intro; unfold rel_prime in *; intros; apply H; 
    trivial; destruct H1; exists (-x); 
    replace (- x * d) with (- (x * d)) by ring; rewrite -H1; ring.
Qed.

Theorem A5P3 : ∀ a b c : Z, (a | b) → rel_prime b c → rel_prime a c.
Proof.
  unfold rel_prime in *.
  intros.
  apply H0; eauto using A2P2.
Qed.

Definition WOP := A3P7.

Definition bezout a b := ∃ x y, a * x + b * y = 1.

Lemma symm_bezout : ∀ a b, bezout a b → bezout b a.
Proof.
  intros; destruct H; destruct H as [y].
  exists y, x.
  by rewrite A1.
Qed.

Lemma pm_bezout : ∀ a b, bezout a b ↔ bezout (-a) b.
Proof.
  split; intros; destruct H; 
    destruct H as [y]; exists (-x), y; 
    rewrite -H; ring.
Qed.

Lemma pm_bezout_right : ∀ a b, bezout a b ↔ bezout a (-b).
Proof.
  split; intros; apply symm_bezout, pm_bezout; 
    try rewrite A1P5; by apply symm_bezout.
Qed.

Definition division := A4P7.

(* Euclidean algorithm / Bezout's lemma *)
Theorem A5P4 : ∀ a b : Z, rel_prime a b → ∃ x y, a * x + b * y = 1.
Proof.
  intros.
  assert (∀ a b, bezout a b = ∃ x y : Z, a * x + b * y = 1) by firstorder;
  rewrite -H0; clear H0.
  (* Essentially a WLOG proof *)
  assert (∀ a b, rel_prime a b → 0 < a → 0 < b → bezout a b).
  - clear a b H; intros.
    remember (λ n, 0 < n ∧ ∃ x y, n = a * x + b * y) as S.
    assert (∃ s : Z, S s ∧ (∀ t : Z, S t → s ≤ t)). {
      apply WOP.
      - intros.
        rewrite HeqS in H2; firstorder.
      - exists a. rewrite HeqS.
        split; trivial.
        exists 1, 0; ring.
    }
    destruct H2 as [m [H2]].
    rewrite HeqS in H2.
    (* destruct H2. *)
    destruct H2 as [H2 [x [y]]].
    exists x, y; rewrite -H4.
    assert (unit m). {
      apply H.
      - destruct (division a m) as [qa [ra []]]; try exact. 
        exists qa.
        rewrite H5.
        destruct H6 as [[]].
        + apply A3P3a in H7; contradiction H7.
          apply H3.
          rewrite HeqS; split; trivial.
          exists (1 - x * qa), (- y * qa).
          replace (a * (1 - x * qa) + b * (- y * qa)) with (a - (a * x + b * y) * qa) by ring.
          rewrite -H4 H5; ring.
        + rewrite -H6; ring.
      - destruct (division b m) as [qb [rb []]]; try exact.
        exists qb.
        rewrite H5.
        destruct H6 as [[]].
        + apply A3P3a in H7; contradiction H7.
          apply H3.
          rewrite HeqS; split; trivial.
          exists (- x * qb), (1 - y * qb).
          replace (a * (- x * qb) + b * (1 - y * qb)) with (b - (a * x + b * y) * qb) by ring.
          rewrite -H4 H5; ring.
        + rewrite -H6; ring.
    }
    apply A3P6 in H5.
    destruct H5; try exact.
    (* Contradiction since -1 is positive *)
    rewrite H5 in H2.
    apply N3 with (c := 1) in H2.
    rewrite A1P2 A1P1 in H2.
    pose proof N4.
    apply (A2P6 1 0 1) in H6; try exact.
    by apply A2P7 in H6.
  - destruct (A2P3 0 a) as [|[|]]; destruct (A2P3 0 b) as [|[|]]; eauto using H0; subst;
    try apply A5P1 in H; try apply rel_prime_sym, A5P1 in H; try destruct H; 
    try exists x, x; try rewrite H; try ring.
    + apply pm_bezout_right, (H0 a (-b)); trivial. 
      by apply A5P2 in H.
      apply (N3 _ _ (-b)) in H2.
      by rewrite A1P1 A4 in H2.
    + apply pm_bezout, (H0 (-a) b); trivial.
      by apply rel_prime_sym, (A5P2 b a), rel_prime_sym.
      apply (N3 _ _ (-a)) in H1.
      by rewrite A1P1 A4 in H1.
    + apply pm_bezout, pm_bezout_right, (H0 (-a) (-b)); trivial.
      apply A5P2, rel_prime_sym, A5P2, rel_prime_sym.
      by rewrite ? A1P5.
      apply (N3 _ _ (-a)) in H1.
      by rewrite A1P1 A4 in H1.
      apply (N3 _ _ (-b)) in H2.
      by rewrite A1P1 A4 in H2.
Qed.

Definition bezout_lemma := A5P4.

(* Gauss's lemma *)
Theorem A5P5 : ∀ a b c : Z, rel_prime a b → (a | b * c) → (a | c).
Proof.
  intros.
  apply bezout_lemma in H.
  destruct H as [x [y]].
  destruct H0 as [k].
  apply (S2 _ _ c) in H.
  rewrite D1 A1P3 in H.
  replace (b * y * c) with (b * c * y) in H by ring.
  rewrite H0 in H.
  exists (x * c + k * y).
  by replace ((x * c + k * y) * a) with (a * x * c + k * a * y ) by ring.
Qed.

Theorem A5P6 : ∀ a b c : Z, rel_prime a b → (a | c) → (b | c) → (a * b | c).
Proof.
  intros.
  destruct (bezout_lemma a b) as [x [y]]; try exact.
  apply (S2 _ _ c) in H2.
  destruct H0 as [k]. 
  destruct H1 as [j].
  rewrite D1 {1} H1 {1} H0 A1P3 in H2.
  exists (x * j + y * k).
  rewrite -H2; ring.
Qed.

Lemma converse_bezout: ∀ a b, bezout a b → rel_prime a b.
Proof.
  unfold rel_prime, unit; intros.
  destruct H as [x [y]].
  rewrite -H.
  apply (A2P1 d a b x y); try exact.
Qed.

Theorem A5P7 : ∀ a b c : Z, rel_prime a c → rel_prime b c → rel_prime (a*b) c.
Proof.
  intros.
  apply converse_bezout.
  unfold bezout.
  apply bezout_lemma in H, H0.
  destruct H as [x1 [y1]].
  destruct H0 as [x2 [y2]].
  exists (x1 * x2), (a * x1 * y2 + y1 * b * x2 + c * y1 * y2).
  apply (S2 _ _ 1) in H.
  symmetry in H0; rewrite {1} H0 M3 in H.
  rewrite -H; ring.
Qed.

(* PM stuff *)

Theorem pm_refl : ∀ a, a = ± a.
Proof.
  by left.
Qed.

Theorem pm_sym : ∀ a b, a = ± b → b = ± a.
Proof.
  firstorder.
  subst.
  unfold pm.
  intuition ring.
Qed.

Theorem pm_trans : ∀ a b c, a = ± b → b = ± c → a = ± c.
Proof.
  firstorder; subst; unfold pm; intuition ring.
Qed.

Add Parametric Relation : Z pm
    reflexivity proved by pm_refl
    symmetry proved by pm_sym
    transitivity proved by pm_trans as Z_pm.
                             
Theorem pm_trans' : ∀ a b c, a = ± b → b = ± c → a = ± c.
Proof.
  intros.
    by rewrite H.
Qed.

Theorem sign : ∀ b, -b = ± b.
Proof.
  firstorder.
Qed.
                             
Add Morphism mult with signature pm ==> pm ==> pm as Z_pm_mult.
Proof.
  unfold pm.
  intros.
  intuition subst; ring.
Qed.

Goal ∀ a b c, a * b = ± c → a * (-b) = ± c.
Proof.
  intros a b c H.
    by rewrite (sign b).
Qed.

Add Morphism divide with signature pm ==> pm ==> iff as Z_pm_div.
Proof.
  intros x y H x0 y0 H0.
  firstorder; subst.
  - exists x1; ring.
  - exists (-x1); ring [H0].
  - exists (-x1); ring.
  - exists x1; ring [H0].
  - exists x1; ring.
  - exists (-x1); ring.
  - exists (-x1); ring.
  - exists x1; ring.
Qed.
      
(* End of pm stuff *)

Definition prime (p : Z) := ¬ unit p ∧ ∀ d : Z, (d | p) → unit d ∨ d ~ p.

Lemma weak_de_morgans : ∀ p q, ¬ (p ∧ q) ↔ (¬ p ∨ ¬ q).
Proof.
  intros.
  pose proof (classic p).
  firstorder.
Qed.

Lemma one_not_zero : ¬ 0 = 1.
Proof.
  apply N1.
  right.
  apply N4.
Qed.

Lemma neg_one_not_zero : ¬ 0 = -1.
Proof.
  apply N1.
  left.
  pose proof N4.
  apply (N3 _ _ (-1)) in H.
  by rewrite A4 A1P1 in H.
Qed.

Lemma two_gt_zero: 0 < 2.
Proof.
  apply (N2 2 1 0).
  split.
  - pose proof N4.
    apply N3 with (c := 1) in H.
    by rewrite A1P1 in H.
  - apply N4.
Qed.

Lemma two_not_zero : ¬ 2 = 0.
Proof.
  apply N1.
  left.
  apply two_gt_zero.
Qed.

Theorem A6P1 : ¬ prime 0.
Proof.
  unfold prime.
  apply weak_de_morgans.
  right.
  unfold not; intros.
  assert (unit 2 ∨ 2 ~ 0).
  apply H.
  exists 0; ring.
  destruct H0.
  - by apply A2P8 in H0.
  - apply A4P5 in H0.
    assert (¬ 2 = 0) by apply two_not_zero. 
    destruct H0; rewrite H0 in H1; try contradiction.
    apply H1; ring.
Qed.

Lemma flip_sign: ∀ a, 0 < a ↔ -a < 0.
Proof.
  firstorder.
  - apply (N3 _ _ (-a)) in H.
    by rewrite A4 A1P1 in H.
  - apply (N3 _ _ a) in H.
    by rewrite A1P2 A1P1 in H.
Qed.

Theorem A6P2 : prime 2.
Proof.
  unfold prime.
  split.
  - apply A2P8.
  - intros. 
    assert (∀ d, (d | 2) → 0 < d → (unit d ∨ d ~ 2)). {
      intros.
      apply A3P5_corrected in H0; try apply two_gt_zero.
      apply A3P4, A3P3b in H1.
      destruct (classic (d0 = 1)).
      + left. apply A3P6. by left.
      + destruct H1; try by contradiction H2.
        apply step_down, (leq_add _ _ 1) in H1.
        replace (d0 + -1 + 1) with d0 in H1 by ring.
        assert (2 ≤ d0 ≤ 2) by firstorder.
        apply strongly_connected in H3.
        right.
        apply A4P5.
        by left.
    }
    destruct (A2P3 d 0) as [|[|]].
    + pose proof (H0 (-d)).
      assert (- d | 2).
        destruct H as [x]. 
        exists (-x).
        rewrite H; ring.
      apply H2 in H3; try apply flip_sign; try by rewrite A1P5.
      destruct H3.
      * left.
        destruct H3.
        exists (-x).
        rewrite H3; ring.
      * right. 
        apply A4P5 in H3; apply A4P5.
        destruct H3.
        -- right. rewrite -H3; ring.
        -- left. replace d with (--d) by ring. 
          rewrite H3; ring.
    + destruct H.
      subst.
      rewrite M1 A1P6 in H.
      by apply two_not_zero in H.
    + apply H0; try exact.
Qed.

Theorem A6P3 : ∀ p q : Z, prime p → prime q → rel_prime p q ∨ p ~ q.
Proof.
  intros.
  destruct (classic (p ~ q)); auto; left.
  unfold rel_prime; intros.
  unfold prime in *.
  destruct H, H0.
  apply H4 in H2.
  apply H5 in H3.
  destruct H2; destruct H3; try exact.
  apply A4P5 in H2, H3.
  contradiction H1.
  apply A4P5.
  apply (pm_trans _ d _); eauto using pm_sym.
Qed.

Theorem A6P4 : ∀ p a : Z, prime p → (p | a) ∨ rel_prime p a.
Proof.
  intros.
  destruct (classic (p | a)); auto; right.
  unfold rel_prime; intros.
  unfold prime in H.
  destruct H.
  apply H3 in H1.
  destruct H1; try exact.
  contradiction H0.
  apply A4P5 in H1.
  destruct H1; subst; trivial.
  destruct H2.
  exists (-x).
  rewrite H1; ring.
Qed.


Theorem not_A6P5 : ¬ (∀ p : Z, ¬ prime p → ∃ n, 1 < n < p ∧ (n | p)).
Proof.
  assert (¬ prime 1).
    unfold prime.
    apply weak_de_morgans.
    left.
    assert (unit 1).
      exists 1; ring.
    firstorder.
  unfold not; intros.
  apply H0 in H.
  destruct H as [x [[]]].
  apply (A2P6 _ _ 1) in H; try exact.
  by apply A2P7 in H.
Qed.

(* In general it's only true for positives *)

Lemma reverse_NNPP: ∀ p : Prop, p → ¬ ¬ p.
Proof.
  firstorder.
Qed.

Lemma DeMorgansGeneralized2 : ∀ P : Z → Prop, (∃ x : Z, ¬ P x) ↔ ¬ (∀ x : Z, P x).
Proof.
  intros.
  split.
  - intros. 
    destruct H.
    unfold not; intros.
    contradiction H.
    apply (H0 x).
  - apply contrapositive; intros.
    apply reverse_NNPP; intros.
    destruct (classic (P x)); try exact.
    contradiction H.
    exists x; try exact.
Qed.

Lemma zero_division : ∀ a, 0 < a → ¬ (0 | a).
Proof.
  intros.
  destruct (classic (0 | a)); try exact.
  destruct H0.
  rewrite M1 A1P6 in H0.
  subst; by apply A2P7 in H.
Qed.

Lemma step_down1: ∀ a b, a < b → a + 1 ≤ b.
Proof.
  intros.
  apply step_down, (leq_add _ _ 1) in H.
  by replace (b + -1 + 1) with b in H by ring.
Qed.

(* Lemma pos_neg_conversion: ∀ a, 0 < a ↔ -a < 0. *)
Lemma neg_pos_conversion: ∀ a, 0 < -a ↔ a < 0.
Proof.
  intros.
  split; intros.
  - apply (N3 _ _ a) in H.
    by rewrite A1P1 A1P2 in H.
  - apply (N3 _ _ (-a)) in H.
    by rewrite A4 A1P1 in H.
Qed.
    
Theorem A6P5_fixed : ∀ p : Z, ¬ prime p → 1 < p → ∃ n, 1 < n < p ∧ (n | p).
Proof.
  intros.
  unfold prime in H.
  apply weak_de_morgans in H.
  destruct H.
  - apply NNPP in H.
    apply A3P6 in H.
    destruct H.
    + rewrite H in H0; by apply A2P7 in H0.
    + rewrite H in H0.
      apply (N3 _ _ 1) in H0.
      rewrite A1P2 in H0.
      contradiction (A2P7 0).
      apply (A2P6 0 2 0); eauto using two_gt_zero.
  - apply DeMorgansGeneralized1.
    unfold not; intros.
    contradiction H; intros.
    assert (∀ d0, 0 < d0 → (d0 | p) → unit d0 ∨ d0 ~ p). {
      intros.
      apply step_down1 in H3; rewrite A1P1 in H3.
      destruct H3.
      * assert (d0 ≤ p).
          apply A3P5_corrected; trivial.
          apply (A2P6 0 1 p); try apply N4; trivial.
        destruct H5.
        -- contradiction (H1 d0).
          split; auto.
        -- right. split; exists 1; ring [H5].
      * left. exists 1; rewrite -H3; ring. }
    destruct (A2P3 d 0) as [|[|]].
    + { apply neg_pos_conversion in H4.
      apply (H3 (-d)) in H4.
      destruct H4.
      * destruct H4; left; exists (-x); rewrite H4; ring.
      * apply A4P5 in H4.
        right.
        split; trivial.
        destruct H4; (exists (-1); ring[H4]) || (exists 1; ring [H4]).
      * destruct H2; exists (-x); ring [H2]. }
    + subst. 
      contradiction (zero_division p).
      apply (A2P6 _ 1 _); try exact; try apply N4.
    + apply H3; trivial.
Qed.

Theorem A6P6 : ∀ p x : Z, prime p → 0 < p → 0 < x → (p | x) →
                          ∃ k, k * p = x ∧ 0 < k < x.
Proof.
  intros.
  destruct H2 as [k].
  exists k.
  split; auto.
  assert (0 < k). {
    destruct (A2P3 k 0) as [|[|]]; auto.
    + apply (C5 p 0 k) in H0; auto; rewrite A1P6 M1 -H2 in H0.
      by apply consistency in H0.
    + subst. by rewrite A1P6 in H1.
  }
  split; auto.
  rewrite H2; replace k with (1 * k) by ring.
  replace (1 * k * p) with (p * k) by ring.
  apply (C4 p 1 k); auto.
  apply step_down1 in H0; destruct H0; rewrite A1P1 in H0; auto. 
  destruct H.
  subst.
  contradiction H.
  exists 1; ring.
Qed.

Definition trichotomy := A2P3.
Definition trans_order := A2P6.

Lemma one_not_prime: ¬ prime 1.
Proof.
  unfold not, prime; intros.
  destruct H.
  contradiction H.
  exists 1; ring.
Qed.

Theorem not_A6P7 : ¬ (∀ n : Z, ∃ p : Z, 0 < p ∧ prime p ∧ (p | n)).
Proof.
  unfold not; intros.
  pose proof (H 1).
  destruct H0 as [x[H1[]]].
  apply A3P5_corrected in H2; try apply N4.
  destruct H2.
  - by apply A3P4 in H1. 
  - subst; by apply one_not_prime.
Qed.

Theorem A6P7_fixed : ∀ n : Z, n ≠ ± 1 → ∃ p : Z, 0 < p ∧ prime p ∧ (p | n).
Proof.
  intro.
  wlog: n / n > 0. 
  - intros.
    destruct (trichotomy 0 n) as [|[|]].
    + by apply x.
    + exists 2. 
      repeat split; try apply two_gt_zero; try apply A6P2.
      exists 0; subst; ring.
    + apply C2 in H0. replace (-0) with 0 in H0 by ring.
      apply x in H0.
      destruct H0 as [p].
      exists p.
      destruct H0 as [H0[H1[k]]].
      split; try split; auto.
      exists (-k); ring [H2].
      unfold not; intro.
      contradiction H.
      rewrite -H1.
      right; ring.
  - intros.
    remember (λ k, 1 < k ∧ (k | n)) as S.
    assert (∃ m, S m ∧ ∀ t, S t → m ≤ t). {
      apply WOP.
      + intros; rewrite HeqS in H1; destruct H1.
        apply (trans_order _ 1 _); auto; try apply N4.
      + exists n. rewrite HeqS.
        split.
        - apply step_down1 in H; rewrite A1P1 in H.
          destruct H; firstorder.
          by contradiction H0.
        - exists 1; ring. }
    destruct H1 as [m[]].
    exists m.
    rewrite HeqS in H1; destruct H1.
    split; try split; trivial. {apply (trans_order _ 1 _); try apply N4; auto. }
    destruct (classic (prime m)); try exact.
    apply A6P5_fixed in H4; try exact.
    destruct H4 as [k[[]]].
    apply A3P3a in H5.
    contradiction H5.
    apply H2.
    rewrite HeqS.
    split; trivial.
    by apply (A2P2 _ m _).
Qed.

(* Euclid's lemma *)
Theorem A6P8 : ∀ p a b : Z, prime p → (p | a * b) → (p | a) ∨ (p | b).
Proof.
  intros.
  apply (A6P4 _ a) in H.
  destruct H; auto.
  eauto using A5P5.
Qed.
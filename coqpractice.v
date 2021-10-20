Require Export Utf8 IndefiniteDescription ClassicalEpsilon
        ssreflect ssrbool ssrfun.

(* Modus ponens:
   https://en.wikipedia.org/wiki/Modus_ponens *)

Theorem modus_ponens : ∀ p q : Prop, p → (p → q) → q.
Proof.
intros.
apply H0 in H.
exact H.
Qed.

(* Modus tollens:
   https://en.wikipedia.org/wiki/Modus_tollens *)

Theorem modus_tollens : ∀ p q : Prop, (p → q) → ¬ q → ¬ p.
Proof.
intros.
Locate "¬".
unfold not.
intros.
apply H in H1.
contradiction.
Qed.

(* Hypothetical syllogism:
   https://en.wikipedia.org/wiki/Hypothetical_syllogism *)

Theorem hypothetical_syllogism : ∀ p q r : Prop, (p → q) → (q → r) → (p → r).
Proof.
intros.
apply H0.
apply H.
exact H1.
Qed.

(* Disjunctive syllogism:
   https://en.wikipedia.org/wiki/Disjunctive_syllogism *)

Theorem disjunctive_syllogism : ∀ p q : Prop, (p ∨ q) → ¬ p → q.
Proof.
intros.
destruct H.
contradiction.
exact H.
Qed.

(* Constructive dilemma:
   https://en.wikipedia.org/wiki/Constructive_dilemma *)

Theorem constructive_dilemma :
  ∀ p q r s : Prop, (p → q) → (r → s) → (p ∨ r) → q ∨ s.
Proof.
intros.
destruct H1.
left.
apply H.
exact H1.
right.
apply H0.
exact H1.
Qed.

(* Destructive dilemma:
   https://en.wikipedia.org/wiki/Destructive_dilemma *)

Theorem destructive_dilemma :
  ∀ p q r s : Prop, (p → q) → (r → s) → (¬ q ∨ ¬ s) → ¬ p ∨ ¬ r.
Proof.
intros.
destruct H1.
- 
left. 
apply modus_tollens in H. 
exact H. 
exact H1.
- 
right. 
apply modus_tollens in H0. 
exact H0. 
exact H1.
Qed.

(* Conjunction elimination:
   https://en.wikipedia.org/wiki/Conjunction_elimination *)

Theorem conjunction_elimination_left : ∀ p q : Prop, p ∧ q → p.
Proof.
intros.
destruct H.
exact H.
Qed.

Theorem conjunction_elimination_right : ∀ p q : Prop, p ∧ q → q.
Proof.
intros.
destruct H.
exact H0.
Qed.

(* Disjunction introduction:
   https://en.wikipedia.org/wiki/Disjunction_introduction *)

Theorem disjunction_introduction_left : ∀ p q : Prop, p → p ∨ q.
Proof.
intros.
left.
exact H.
Qed.

Theorem disjunction_introduction_right : ∀ p q : Prop, q → p ∨ q.
Proof.
intros.
right.
exact H.
Qed.

Theorem NNPP : ∀ p, ¬ ¬ p → p.
Proof.
intros.
pose proof (classic p) as H0.
destruct H0.
- exact H0.
- contradiction.
Qed.

(* Exercises. For each N = 1,2,3,4,5, prove either QNa or QNb,
   but not both. *)

Theorem Q1a : ∀ p q : Prop, (p → q) → (q → p).
Proof.
Admitted.

Theorem Q1b : ¬ (∀ p q : Prop, (p → q) → (q → p)).
Proof.
unfold not.
intros.
pose proof (H False True).
apply H0.
contradiction.
exact I.
Qed.

Theorem Q2a : ∀ p q : Prop, (¬ p → ¬ q) → (q → p).
Proof.
intros.
pose proof (classic p).
destruct H1.
exact H1.
apply H in H1.
unfold not in H1.
apply H1 in H0.
contradiction.
Qed.

Theorem Q2b : ¬ (∀ p q : Prop, (¬ p → ¬ q) → (q → p)).
Proof.
Admitted.

Theorem Q3a : ∀ p q : Prop, (¬ p → ¬ q) → (p → q).
Proof.
Admitted.

Theorem Q3b : ¬ (∀ p q : Prop, (¬ p → ¬ q) → (p → q)).
Proof.
unfold not.
intros.
pose proof (H True False).
apply H0.
contradiction.
exact I.
Qed.

Theorem Q4a : ∀ p q : Prop, ¬ (¬ p ∧ ¬ q) → p ∨ q.
Proof.
intros.
pose proof (classic p).
destruct H0.
left.
exact H0.
right.
unfold not in H.
unfold not in H0.
pose proof (classic q).
destruct H1.
- exact H1. 
- unfold not in H1.
contradiction H. 
split.
exact H0.
exact H1.
Qed. 

Theorem Q4b : ¬ (∀ p q : Prop, ¬ (¬ p ∧ ¬ q) → p ∨ q).
Proof.
Admitted.

Theorem Q5a : ∀ p q : Prop, (p → q) → (¬ p ∨ ¬ q).
Proof.
Admitted.

Theorem Q5b : ¬ (∀ p q : Prop, (p → q) → (¬ p ∨ ¬ q)).
Proof.
unfold not.
intro.
pose proof (H True True).
destruct H0.
- reflexivity. 
- contradiction.
- contradiction.
Qed.

(* De Morgan's laws:
   https://en.wikipedia.org/wiki/De_Morgan%27s_laws#Extension_to_predicate_and_modal_logic *)

Theorem Q6 : ∀ A (P : A → Prop), (∀ x, P x) ↔ ¬ (∃ x, ¬ P x).
Proof.
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

Lemma contrapositive: ∀ p q: Prop, (¬ p → ¬ q) → (q → p).
Proof.
intros.
pose proof (classic p).
destruct H1.
- exact H1.
- apply H in H1. contradiction.
Qed.

Lemma reverse_NNPP: ∀ p: Prop, p → ¬ ¬ p.
Proof.
intros.
pose proof (classic (¬ p)).
destruct H0.
- contradiction.
- exact H0.
Qed.

Theorem Q7 : ∀ A (P : A → Prop), (∃ x, P x) ↔ ¬ (∀ x, ¬ P x).
Proof.
intros.
split.
- unfold not. 
intros. 
destruct H. 
apply H0 in H.
exact H.
- apply contrapositive.
intros.
apply reverse_NNPP.
apply Q6.
unfold not.
intros.
contradiction H.
destruct H0.
apply NNPP in H0.
exists x.
exact H0.
Qed.

Section definitions.

  (* Let A and B be sets, and let f be a function from A to B. *)

  Context {A B : Set}.
  Variable f : A → B.

  (* Definition: We define f to be injective if, 
     for all a1 a2 ∈ A, f(a1) = f(a2) implies a1 = a2. *)

  Definition injective := ∀ a1 a2 : A, f a1 = f a2 → a1 = a2.

  (* Definition: We define f to be surjective if,
     for all b ∈ B, there exists a ∈ A such that f(a) = b. *)

  Definition surjective := ∀ b : B, ∃ a : A, f a = b.

  (* Definition: We define f to be bijective
     if f is both injective and surjective. *)

  Definition bijective := injective ∧ surjective.

  (* Definition: We define f to have a left inverse if there exists a function
     g from B to A such that, for all a ∈ A, g(f(a)) = a. *)

  Definition has_left_inverse := ∃ g : B → A, ∀ a : A, g (f a) = a.

  (* Definition: We define f to have a right inverse if there exists a function
     g from B to A such that, for all b ∈ B, f(g(b)) = b. *)

  Definition has_right_inverse := ∃ g : B → A, ∀ b : B, f (g b) = b.

  (* Definition: We define f to have a two-sided inverse if there exists
     a function g from B to A such that:
     (for all a ∈ A, g(f(a)) = a) and (for all b ∈ B, f(g(b)) = b). *)

  Definition has_two_sided_inverse :=
    ∃ g : B → A, (∀ a : A, g (f a) = a) ∧ (∀ b : B, f (g b) = b).

End definitions.

Section theorems.

  (* Let A and B be sets, and let f be a function from A to B. *)

  Variable A B : Set.
  Variable f : A → B.

  (* Which of the following six "theorems" are true? Which of them are false?
     Write T for True and F for False.

     injective_left_inverse: T
     left_inverse_injective: T
     surjective_right_inverse: F
     right_inverse_surjective: T
     bijective_two_sided_inverse: T
     two_sided_inverse_bijective: T

     You do NOT NEED to prove these theorems in Coq, although you are welcome
     to try if you wish. Some of these proofs are beyond the scope of what
     we have covered so far. All you need to do is determine whether the
     statements are true or false.

     If you want, you can add some (optional) explanations of your reasoning
     in the blank space below. Use as many lines as you need.

  1. injective_left_inverse:
  Assuming B is non-empty, for every element b in B must be either in the range 
  of f or not. If b is in the range of f, then by definition there exists a such 
  that f(a) = b. Further, by the injectivity of f, a must be unique, so define 
  g(b) to be a. If b is out of the range of f, then simply define g(b) = c for 
  some arbitrary element c of B, which must exist since B is non-empty. Thus,
  g is the unique left inverse of f.

  2. left_inverse_injective:
  If f(a1) = f(a2), then g(f(a1) = a1 = g(f(a2)) = a2, so a1 = a2, as required.

  3. surjective_right_inverse:
  
  Original "proof":
  Define g as the following: for every b in B define g(b) to be any element a 
  that satisfies f(a) = b, which must exist by the surjectivity of f. Thus,
  g is a right inverse of f.

  However, I later realize that this "proof" is flawed, as detailed under *.

  4. right_inverse_surjective:
  There exists g such that f(g(b)) = b for all b in B, so for every b in B, 
  setting a = g(b) allows f(a) = b for all b in B. Thus, f must be surjective.
  
  5. bijective_two_sided_inverse:
  This may seem as a consequence of injective_left_inverse and 
  surjective_right_inverse but it is still requred to verify that the left
  and right inverses are the same. Let g be the left inverse as constructed in
  injective_left_inverse, which must exist since f is injective. It suffices to
  show that f(g(b)) = b for all b in B, that is, g is also the right inverse of
  f. Let a be arbitrary elment of A, and let b = f(a). Then f(g(f(a))) = f(a) = b
  since g is the left inverse of f, but also f(g(f(a))) = f(g(b)), so f(g(b)) = b, 
  as required.

  6. two_sided_inverse_bijective:
  Consequence of left_inverse_injective and right_inverse_surjective.

  * Disproof of surjective_right_inverse:
  However, as hinted in the Youtube video, not all the statements are true, 
  which by De Morgan's law implies there exists a false proposition. 
  As I have proven via Coq the propositions #2, #4, and #6, one of #1,
  #3, and #5 must be false. After a bit of consideration, I came to the 
  conlusion that #3 surjective_right_inverse is the only proposition to have 
  an incorrect assumption, specifically, the axiom of choice. This is because 
  for each b, there could exists multiple choices of a for which f(a) = b, and 
  the choice for a specific a could be non-trivial.
   *)

  Theorem injective_left_inverse : injective f → has_left_inverse f.
  Proof.
  Admitted.

  Theorem left_inverse_injective : has_left_inverse f → injective f.
  Proof.
  unfold has_left_inverse, injective.
  intros.
  destruct H as [g].
  rewrite <- H.
  rewrite <- H0.
  rewrite H.
  reflexivity.
  Qed.

  Theorem surjective_right_inverse : surjective f → has_right_inverse f.
  Proof.
  Admitted.

  Theorem right_inverse_surjective : has_right_inverse f → surjective f.
  Proof.
  unfold has_right_inverse, surjective.
  intros.
  destruct H as [g].
  exists (g b).
  apply H.
  Qed.

  Theorem bijective_two_sided_inverse : bijective f → has_two_sided_inverse f.
  Proof.
  Admitted.

  Theorem two_sided_inverse_bijective : has_two_sided_inverse f → bijective f.
  Proof.
  unfold has_two_sided_inverse, bijective.
  intros.
  split.
  - apply left_inverse_injective. 
  destruct H. 
  destruct H. 
  unfold has_left_inverse. 
  exists x. 
  exact H.
  - apply right_inverse_surjective. 
  destruct H.
  destruct H.
  unfold has_right_inverse.
  exists x.
  exact H0.
  Qed.

End theorems.

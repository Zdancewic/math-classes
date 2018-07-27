Require Import
  MathClasses.interfaces.abstract_algebra MathClasses.theory.products.

Lemma ext_equiv_refl `{Setoid_Morphism A B f} : f = f.
Proof. intros ?? E. now apply sm_proper. Qed.

Lemma ext_pequiv_refl `{PartialSetoid_Morphism A B f} : f = f.
Proof. intros ?? E. now apply psm_proper. Qed.

(*
Instance ext_equiv_trans `{Equiv A} `{Equiv B} `{Reflexive (A:=A) (=)} `{Transitive (A:=B) (=)} : Transitive (_ : Equiv (A → B)).
Proof. intros ? y ???? w ?. transitivity (y w). apply H3.  assumption. apply H4. firstorder. Qed.
*)

Instance ext_equiv_trans `{Equiv A} `{Equiv B} `{Symmetric (A:=A) (=)} `{Transitive (A:=A) (=)} `{Transitive (A:=B) (=)} : Transitive (_ : Equiv (A → B)).
Proof.
  repeat red. intros x y z H4 H5 x0 y0 H6.
  transitivity (y y0). apply H4. assumption. apply H5.
  eapply transitivity. symmetry. apply H6. assumption.
Qed.


Instance ext_equiv_sym `{Equiv A} `{Equiv B} `{Symmetric (A:=A) (=)} `{Symmetric (A:=B) (=)}: Symmetric (A:=A→B) (=).
Proof. firstorder. Qed.

Lemma ext_equiv_applied `{Setoid A} `{Equiv B} {f g : A → B} :
  f = g → ∀ x, f x = g x.
Proof. intros E x. now apply E. Qed.

Lemma ext_pequiv_applied `{@PartialSetoid A eqA} `{Equiv B} {f g : A → B} :
  f = g → ∀ (x:A), Proper eqA x -> f x = g x.
Proof. intros E x Hp. now apply E. Qed.

Lemma ext_equiv_applied_iff `{Equiv A} `{Equiv B} `{!Setoid_Morphism (f : A → B)}
  `{!Setoid_Morphism (g : A → B)} : f = g ↔ ∀ x, f x = g x.
Proof.
  pose proof (setoidmor_a f). pose proof (setoidmor_b f).
  split; intros E1.
   now apply ext_equiv_applied.
  intros x y E2. now rewrite E2.
Qed.

Lemma ext_pequiv_applied_iff `{eqA:Equiv A} `{Equiv B} `{!PartialSetoid_Morphism (f : A → B)}
  `{!PartialSetoid_Morphism (g : A → B)} : f = g ↔ ∀ x, Proper eqA x -> f x = g x.
Proof.
  destruct PartialSetoid_Morphism0.
  destruct PartialSetoid_Morphism1.
  split; intros E1.
  - now apply ext_pequiv_applied.
  - intros x y Heq.
    assert (y = y).
    eapply transitivity. apply (@PER_Symmetric A eqA). constructor. apply psetoidmor_a. apply psetoidmor_a. eassumption.
    assumption.
    assert (f x = f y).
    apply psm_proper. assumption.
    eapply transitivity. apply H1. apply E1. assumption.
Qed.

Lemma morphism_ne `{Equiv A} `{Equiv B} (f : A → B) `{!Setoid_Morphism f} x y :
  f x ≠ f y → x ≠ y.
Proof. intros E1 E2. apply E1. now apply sm_proper. Qed.


Lemma psetoid_morphism_ne `{Equiv A} `{Equiv B} (f : A → B) `{!PartialSetoid_Morphism f} x y :
  f x ≠ f y → x ≠ y.
Proof. intros E1 E2. apply E1. now apply psm_proper. Qed.

Instance: Equiv Prop := iff.
Instance: Setoid Prop := {}.

Lemma projected_setoid `{Setoid B} `{Equiv A} (f : A → B)
  (eq_correct : ∀ x y, x = y ↔ f x = f y) : Setoid A.
Proof.
 constructor; repeat intro; apply eq_correct.
 reflexivity.
 symmetry; now apply eq_correct.
 transitivity (f y); now apply eq_correct.
Qed.

Lemma projected_psetoid `{PartialSetoid B} `{Equiv A} (f : A → B)
  (eq_correct : ∀ x y, x = y ↔ f x = f y) : PartialSetoid A.
Proof.
 constructor; repeat intro; apply eq_correct.
 symmetry; now apply eq_correct.
 transitivity (f y); now apply eq_correct.
Qed.


Instance sig_psetoid `{PartialSetoid A} (P : A → Prop) : PartialSetoid (sig P).
Proof. now apply (projected_psetoid (@proj1_sig _ P)). Qed.

Instance sigT_psetoid `{PartialSetoid A} (P : A → Type) : PartialSetoid (sigT P).
Proof. now apply (projected_psetoid (@projT1 _ P)). Qed.

Instance sig_setoid `{Setoid A} (P : A → Prop) : Setoid (sig P).
Proof. now apply (projected_setoid (@proj1_sig _ P)). Qed.

Instance sigT_setoid `{Setoid A} (P : A → Type) : Setoid (sigT P).
Proof. now apply (projected_setoid (@projT1 _ P)). Qed.


Global Instance id_morphism `{Setoid A} : Setoid_Morphism (@id A) := {}.
Proof. firstorder. Qed.

Global Instance id_pmorphism `{PartialSetoid A} : PartialSetoid_Morphism (@id A) := {}.
Proof. firstorder. Qed.


Lemma compose_psetoid_morphism `{Equiv A} `{Equiv B} `{Equiv C} (f : A → B) (g : B → C) :
  PartialSetoid_Morphism f → PartialSetoid_Morphism g → PartialSetoid_Morphism (g ∘ f).
Proof. firstorder. Qed.
Hint Extern 4 (PartialSetoid_Morphism (_ ∘ _)) => class_apply @compose_psetoid_morphism : typeclass_instances.

Lemma compose_setoid_morphism `{Equiv A} `{Equiv B} `{Equiv C} (f : A → B) (g : B → C) :
  Setoid_Morphism f → Setoid_Morphism g → Setoid_Morphism (g ∘ f).
Proof. firstorder. Qed.
Hint Extern 4 (Setoid_Morphism (_ ∘ _)) => class_apply @compose_setoid_morphism : typeclass_instances.


Lemma psetoid_morphism_equiv: forall `{eqA:Equiv A} `{eqB:Equiv B} (f g : A → B),
    f = g → PartialSetoid_Morphism f → PartialSetoid_Morphism g.
Proof.
  intros A eqA B eqB f g Hfg Hf.
  destruct Hf.
  constructor; try assumption.
  intros x y Hxy.
  assert (f x = g x). { apply ext_pequiv_applied. assumption. red. eapply transitivity. apply Hxy. apply symmetry. apply Hxy. }
  assert (f y = g y). { apply ext_pequiv_applied. assumption. red. eapply transitivity. apply symmetry. apply Hxy. apply Hxy. }   
  eapply transitivity. eapply symmetry. apply H.                      
  eapply symmetry. eapply transitivity. eapply symmetry. apply H0.
  eapply symmetry. apply psm_proper. assumption.
Qed.  
   
Instance psetoid_morphism_proper `{Equiv A} `{Equiv B}: Proper ((=) ==> iff) (@PartialSetoid_Morphism A B _ _).
Proof.
  intros f g; split; intros ?. eapply psetoid_morphism_equiv; eauto.
  pose proof (psetoidmor_a g). pose proof (psetoidmor_b g).
  eapply psetoid_morphism_equiv. eapply symmetry. apply H1. eauto.
Qed.

Instance setoid_morphism_proper `{Equiv A} `{Equiv B}: Proper ((=) ==> iff) (@Setoid_Morphism A B _ _).
Proof.
  assert (∀ f g : A → B, f = g → Setoid_Morphism f → Setoid_Morphism g) as aux.
   intros f g E1 ?. pose proof (setoidmor_a f). pose proof (setoidmor_b f).
   split; try apply _. intros x y E2.
   now rewrite <-!(ext_equiv_applied E1 _), E2.
  intros f g; split; intros ?; eapply aux; eauto.
  pose proof (setoidmor_a g). pose proof (setoidmor_b g). now symmetry.
Qed.


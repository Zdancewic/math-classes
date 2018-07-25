Require Import
  MathClasses.interfaces.abstract_algebra MathClasses.interfaces.monads MathClasses.theory.functors.

Instance default_mon_join `{MonadBind M} `{eqM:∀ A, Equiv A → Equiv (M A)} : MonadJoin M | 20 := λ A eqA, bind _ _ id.

Instance default_mon_map `{MonadReturn M} `{MonadBind M} : SFmap M | 20 := λ A B eqA eqB f, bind eqA eqB (ret eqB ∘ f).

(* SAZ: It looks like it is not possible to define bind in terms of join without 
     - eqB : Equiv B    (the equivalence on B)
     - eqM : forall A, Equiv A -> Equiv (M A)   (the fuction that lifts equivalences
             through the monad)
     The reason is that we'd like to join at the type B
*)
Instance default_mon_bind `{SFmap M} `{MonadJoin M} `{eqM:∀ A, Equiv A → Equiv (M A)}
  : MonadBind M | 20 := λ A B eqA eqB (f : A -> M B), (@join _ _ B eqB) ∘ (sfmap f).

Hint Extern 0 (ProperProxy (@respectful _ _ _ _) _) =>
  class_apply @proper_proper_proxy : typeclass_instances.

Instance equiv_ext_equiv `{Equiv A} `{Equiv B} :
  PartialSetoid A -> PartialSetoid B ->
  Proper ((equiv ==> equiv) ==> (equiv ==> equiv) ==> flip impl)
         (@equiv _ (@ext_equiv A _ B _)).
Proof.
  unfold ext_equiv.
  intros PA PB.
  repeat red.
  intros f g Efg f' g' Ef'g' E x y Exy.
  assert (g x = f x). { symmetry. apply Efg. eapply transitivity. apply Exy. symmetry. apply Exy. }
  assert (f' y = g' y). { apply Ef'g'. eapply transitivity. eapply symmetry. apply Exy. apply Exy. }
  eapply transitivity. apply symmetry. apply H1. apply symmetry. eapply transitivity. apply H2.
  apply symmetry.
  apply E. assumption.
Qed.

Instance equiv_ext_equiv_partial `{Equiv A} `{Equiv B} (f : A -> B) :
  PartialSetoid A -> PartialSetoid B ->
  Proper (equiv ==> equiv) f ->
  Proper ((equiv ==> equiv) ==> flip impl)
         (@equiv _ (@ext_equiv A _ B _) f).
Proof. intros. partial_application_tactic; eauto. apply equiv_ext_equiv; eauto. Qed.

(* When equiv is just a PER, not an Equivalence, we need to
   pick out the proper elements of the relation, which are those
   related to themselves. *)

Section monad.
  Context `{Monad M}.

  Lemma bind_lunit_applied `{eqA:Equiv A} `{@PartialSetoid B eqB} `{!PartialSetoid_Morphism (f : A → M B)} (x : A) `{!Proper eqA x}: 
    ret _ x ≫= f = f x.
  Proof. pose proof (psetoidmor_a f). now apply bind_lunit. Qed.

  Lemma bind_runit_applied `{@Setoid A eqA} (m : M A) `{!Proper (eqM _ eqA) m}: 
    m ≫= ret _ = m.
  Proof. now apply bind_runit. Qed.

  Lemma bind_assoc_applied `{eqA:Equiv A} `{eqB:Equiv B} `{@Setoid C eqC} 
       `{!PartialSetoid_Morphism (f : A → M B)} `{!PartialSetoid_Morphism (g : B → M C)} (m : M A) `{!Proper (eqM _ eqA) m}:
    (m ≫= f) ≫= g = x ← m ; f x ≫= g.
  Proof. pose proof (psetoidmor_a f). now apply bind_assoc. Qed.

  Global Instance ret_mor `{@PartialSetoid A eqA} : PartialSetoid_Morphism (@ret _ _ A _) := {}.
  Global Instance bind_mor `{eqA:Equiv A} `{@PartialSetoid B eqB} `{!PartialSetoid_Morphism (f : A → M B)} :
    PartialSetoid_Morphism (bind _ _ f).
  Proof. pose proof (psetoidmor_a f). split; try apply _. Qed.

  Definition liftM2  `{eqA:Equiv A} `{eqB:Equiv B} `{eqC:Equiv C} `(f: A → B → C) (m : M A) (n : M B) : M C :=
    x ← m ; y ← n ; ret _ (f x y).

  Section to_strong_monad.
  Context `{MonadJoin M} `{SFmap M}
    (map_proper : ∀ `{@PartialSetoid A eqA} `{@PartialSetoid B eqB}, Proper (((=) ==> (=)) ==> ((=) ==> (=))) (@sfmap M _ A B eqA eqB))
    (map_correct : ∀ `{eqA:Equiv A} `{eqB:Equiv B} `{!PartialSetoid_Morphism (f : A → B)}, sfmap f = bind _ _ (ret _ ∘ f))
    (join_correct : ∀ `{eqA:PartialSetoid A}, join = bind _ _ id).
  Existing Instance map_proper.

  Let bind_correct `{eqA:Equiv A} `{@PartialSetoid B eqB} `{!PartialSetoid_Morphism (f : A → M B)} : 
    bind _ _ f = (@join _ _ B eqB) ∘ sfmap f.
  Proof.
    pose proof (psetoidmor_a f). pose proof (psetoidmor_b f).
    rewrite join_correct by apply _. rewrite map_correct.
    rewrite bind_assoc.
    change (bind _ _ f = bind _ _ ((bind _ _ id ∘ ret _) ∘ f)).
    rewrite bind_lunit.
    now apply setoids.ext_pequiv_refl.
    assumption.
  Qed.

  Instance: SFunctor M.
  Proof.
    split; try apply _.
     intros A ? ?.
     red. rewrite map_correct by apply _. 
     now apply bind_runit.
    intros A ? B ? C ? f ? g ?.
    pose proof (psetoidmor_a g). pose proof (psetoidmor_b g). pose proof (psetoidmor_b f).
    rewrite !map_correct by apply _.
    rewrite bind_assoc.
    change (bind _ _ (ret _ ∘ (f ∘ g)) = bind _ _ ((bind _ _ (ret _ ∘ f) ∘ (ret _ )) ∘ g)).
    rewrite bind_lunit.
    now apply setoids.ext_pequiv_refl.
  Qed.

  Instance: ∀ `{@PartialSetoid A eqA}, PartialSetoid_Morphism (@join _ _ A _).
  Proof.
    split; try apply _. intros x y E1. 
    assert (∀ z, Proper (eqM _ (eqM A eqA)) z -> join z = bind _ _ id z) as E2.
    { intros. apply join_correct. assumption. assumption. }
    rewrite !E2, E1.
    apply mon_bind_proper. eauto.
    symmetry; eapply transitivity; [symmetry; eauto | eauto].
    red. symmetry; eapply transitivity; [symmetry; eauto | eauto].
    red. eapply transitivity; [ eauto | symmetry; eauto ].
  Qed.

  Instance monad_strong_monad: StrongMonad M.
  Proof.
    split; try apply _.
        intros A ? B ? f ?. pose proof (psetoidmor_a f). pose proof (psetoidmor_b f).
        rewrite map_correct by apply _.
        rewrite bind_lunit.
        now apply setoids.ext_pequiv_refl.
       intros A ? B ? f ?. pose proof (psetoidmor_a f). pose proof (psetoidmor_b f).
       rewrite <-bind_correct.
       rewrite !join_correct by apply _.
       rewrite map_correct by apply _.
       rewrite bind_assoc.
       now apply setoids.ext_pequiv_refl.
      intros A ??. rewrite join_correct by apply _. 
      rewrite bind_lunit.
      now apply setoids.ext_pequiv_refl.
     intros A ??.
     rewrite <-bind_correct.
     rewrite bind_runit.
     now apply setoids.ext_pequiv_refl.
    intros A ??. rewrite <-bind_correct.
    rewrite !join_correct by apply _.
    rewrite bind_assoc.
    now apply setoids.ext_pequiv_refl.
  Qed.

  Instance monad_full_monad: FullMonad M.
  Proof. split; try apply _; auto. Qed.
  End to_strong_monad.

  Instance monad_default_full_monad: FullMonad M.
  Proof.
    apply monad_full_monad; unfold sfmap, default_mon_map.
    - intros A eqA H4 B eqB H5 f g E1 m n E2.
      apply mon_bind_proper.
       intros x y E3. now apply mon_ret_proper, E1.
      easy.

    - intros A ? B ? f ??? E. pose proof (psetoidmor_a f). pose proof (psetoidmor_b f).
      rewrite E. apply mon_bind_proper. eauto.
      symmetry; eapply transitivity; [symmetry; eauto | eauto].      
    - intros A ?? ?? E. unfold join, default_mon_join.
      apply mon_bind_proper. eauto.
      assumption.
  Qed.
End monad.

Section strong_monad.
  Context `{eqM :forall A, Equiv A -> Equiv (M A)}.
  Context `{sm:@StrongMonad M eqM H H1 H2}.
  
  Global Instance sret_mor `{PartialSetoid A} : PartialSetoid_Morphism (@ret _ _ A _) := {}.
  Global Instance join_mor `{PartialSetoid A} : PartialSetoid_Morphism (@join _ _ A _) := {}.

  Hint Immediate psetoidmor_a : typeclass_instances.
  Hint Immediate psetoidmor_b : typeclass_instances.

  Lemma sfmap_ret_applied `{eqA:Equiv A} `{Equiv B} `{!PartialSetoid_Morphism (f : A → B)} (x : A)
        `{!Proper eqA x}
    : 
    sfmap f (ret _ x) = ret _ (f x).
  Proof. now apply sfmap_ret. Qed.

  Lemma sfmap_join_applied `{eqA:Equiv A} `{Equiv B} `{!PartialSetoid_Morphism (f : A → B)} (m : M (M A))
        `{Proper (M(M A)) (eqM (M A) (eqM A eqA))  m}
    : 
    sfmap f (join m) = join (sfmap (sfmap f) m).
  Proof. now apply sfmap_join. Qed.

  Lemma join_ret_applied `{@PartialSetoid A eqA} (m : M A)
        `{Proper (M A) (eqM A eqA) m}
    :
    join (ret _ m) = m.
  Proof. now apply join_ret. Qed.

  Lemma join_sfmap_ret_applied `{@PartialSetoid A eqA} (m : M A)
        `{Proper (M A) (eqM A eqA) m}
    :
    join (sfmap (ret _) m) = m.
  Proof. now apply join_sfmap_ret. Qed.

  Lemma join_sfmap_join_applied `{@PartialSetoid A eqA} (m : M (M (M A)))
        `{Proper (M (M (M A))) (eqM _ (eqM _ (eqM A eqA))) m}

    : 
    join (sfmap join m) = join (join m).
  Proof. now apply join_sfmap_join. Qed.

  Section to_monad.
  Context `{MonadBind M}
    (bind_proper : ∀ `{PartialSetoid A} `{PartialSetoid B}, Proper (((=) ==> (=)) ==> ((=) ==> (=))) (@bind M _ A B _ _))
    (bind_correct : ∀ `{Equiv A} `{PartialSetoid B} `{!PartialSetoid_Morphism (f : A → M B)}, bind _ _ f = join ∘ sfmap f).

  Instance: ∀ `{Equiv A} `{PartialSetoid B} `{!PartialSetoid_Morphism (f : A → M B)},
    PartialSetoid_Morphism (bind _ _ f).
  Proof. intros. split; try apply _. Qed.

  Let bind_correct_applied `{eqA:Equiv A} `{PartialSetoid B} `{!PartialSetoid_Morphism (f : A → M B)} m
      `{Proper (M A) (eqM _ eqA) m}
    :
    bind _ _ f m = join (sfmap f m).
  Proof. now eapply bind_correct. Qed.

  Instance strong_monad_monad: Monad M.
  Proof.
    split; try apply _.
      intros A ? B ?? f ?. pose proof (psetoidmor_a f). pose proof (psetoidmor_b f).
      rewrite bind_correct by apply _.
      rewrite compose_assoc, sfmap_ret.
      rewrite <-compose_assoc, join_ret.
      now apply setoids.ext_pequiv_refl.
     intros A ? ?.
     rewrite bind_correct by apply _.
     now apply join_sfmap_ret.
     intros A ? B ? C ?? f ? g ? m n E. pose proof (psetoidmor_a f). pose proof (psetoidmor_a g).
     pose proof (@sfunctor_setoid _ eqM H1 _ _ _ H5).
     assert (Proper (eqM _ eqA) m). { red. eapply transitivity. apply E. eapply symmetry. apply E. }
     assert (Proper (eqM _ eqA) n). { red. eapply symmetry. eapply transitivity. eapply symmetry. apply E. apply E. }      
    unfold compose at 1. rewrite !bind_correct_applied; auto.
    rewrite !bind_correct.
    rewrite sfmap_join_applied.
    rewrite !sfmap_comp_applied.
    rewrite join_sfmap_join_applied.
    rewrite E.
    apply smon_join_proper.
    apply smon_join_proper.
    apply sfmap_proper. auto.
    apply sfmap_proper. auto. apply H8.
    apply sfmap_proper. auto.
    apply sfmap_proper. auto. apply H8.
    apply sfmap_proper. auto. apply H8.
    apply H8.
    apply sfmap_proper. auto. apply H7. assumption. assumption.
    apply bind_proper; eauto.
   Qed.

  Instance strong_monad_full_monad: FullMonad M.
  Proof. split; try apply _; auto. Qed.
  End to_monad.

  Instance strong_monad_default_full_monad: FullMonad M.
  Proof.
    apply strong_monad_full_monad; unfold bind, default_mon_bind.
     intros A ?? B ?? f g E1 m n E2.
     apply smon_join_proper. apply sfmap_proper; intuition.
     intros A ? B ?? f ? ?? E.
     pose proof (@sfunctor_setoid _ eqM H1 _ _ _ H4).     
     assert (Proper ((eqM _ H3) ==> (eqM _ Ae)) (join ∘ sfmap f)).
     typeclasses eauto.
     apply H5. apply E.
  Qed.
End strong_monad.

(*
Section full_monad.
  Context `{FullMonad M}.

  Lemma bind_as_join_sfmap_applied `{Equiv A} `{PartialSetoid B} `{!PartialSetoid_Morphism (f : A → M B)} (m : M A) : 
    m ≫= f = join (sfmap f m).
  Proof. pose proof (setoidmor_a f). now  apply bind_as_join_sfmap. Qed.

  Lemma sfmap_as_bind_ret `{Equiv A} `{Equiv B} `{!PartialSetoid_Morphism (f : A → B)} : 
     sfmap f = bind _ _ (ret _ ∘ f).
  Proof.
    pose proof (setoidmor_a f). pose proof (setoidmor_b f).
    rewrite bind_as_join_sfmap.
    rewrite sfmap_comp.
    rewrite <-compose_assoc.
    rewrite join_sfmap_ret.
    now apply setoids.ext_equiv_refl.
  Qed.

  Lemma sfmap_as_bind_ret_applied `{Equiv A} `{Equiv B} `{!PartialSetoid_Morphism (f : A → B)} (m : M A) : 
    sfmap f m = x ← m ; ret _ (f x).
  Proof. pose proof (setoidmor_a f). now apply sfmap_as_bind_ret. Qed.

  Lemma join_as_bind `{PartialSetoid A} : 
    join = bind _ _ id.
  Proof.
    rewrite bind_as_join_sfmap.
    rewrite sfmap_id.
    now apply setoids.ext_equiv_refl.
  Qed.

  Lemma join_as_bind_applied `{PartialSetoid A} (m : M (M A)) : 
    join m = m ≫= id.
  Proof. now apply join_as_bind. Qed.

  Lemma join_spec_applied_alt `{PartialSetoid A} (m : M (M A)) : 
    join m = x ← m ; x.
  Proof. now apply join_as_bind. Qed.

  Lemma bind_twice `{Equiv A} `{Equiv B} `{PartialSetoid C} 
       `{!PartialSetoid_Morphism (f : B → M C)} `{!PartialSetoid_Morphism (g : A → M B)} :
    bind _ _ (bind _ _ f) = bind _ _ f ∘ join.
  Proof.
    pose proof (setoidmor_a f). pose proof (setoidmor_b f).
    pose proof (setoidmor_b g).
    rewrite join_as_bind.
    rewrite bind_assoc.
    now apply setoids.ext_equiv_refl.
  Qed.

  Lemma bind_twice_applied `{Equiv A} `{Equiv B} `{PartialSetoid C} 
       `{!PartialSetoid_Morphism (f : B → M C)} `{!PartialSetoid_Morphism (g : A → M B)} (m : M (M B)) :
    m ≫= bind _ _ f = join m ≫= f.
  Proof. pose proof (setoidmor_a f). now apply bind_twice. Qed. 

  Lemma bind_join `{PartialSetoid A} : 
    bind _ _ join = join ∘ join.
  Proof.
    rewrite !join_as_bind.
    rewrite bind_assoc.
    now apply setoids.ext_equiv_refl.
  Qed.

  Lemma bind_join_applied `{PartialSetoid A} (m : M (M (M A))) : 
    m ≫= join = join (join m).
  Proof. now apply bind_join. Qed.
End full_monad.
*)
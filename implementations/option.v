Require Import
  MathClasses.interfaces.abstract_algebra MathClasses.interfaces.monads MathClasses.theory.jections MathClasses.theory.monads.

Inductive option_equiv A `{Equiv A} : Equiv (option A) :=
  | option_equiv_Some : Proper ((=) ==> (=)) Some
  | option_equiv_None : None = None.

Existing Instance option_equiv.
Hint Constructors option_equiv.


Section contents.
  Context `{PartialSetoid A}.

  Lemma Some_ne_None x : Some x ≠ None.
  Proof. intros E. inversion E. Qed.

  Lemma None_ne_Some x : None ≠ Some x.
  Proof. intros E. inversion E. Qed.
  
  Global Instance: PartialSetoid (option A).
  Proof.
    split.
      (* intros [x|]. now apply option_equiv_Some. now apply option_equiv_None. *)
     red. induction 1. now apply option_equiv_Some. now apply option_equiv_None.
    intros x y z E. revert z. induction E.
     intros z E2. inversion_clear E2.
     apply option_equiv_Some. etransitivity; eassumption.
    easy.
  Qed.

  Global Instance: PartialSetoid_Morphism Some.
  Proof. split; try apply _. now apply option_equiv_Some. Qed.

  Global Instance option_zero: MonUnit (option A) := None.

  Global Instance option_op: SgOp (option A) := λ mx my,
    match mx with
    | Some x => Some x
    | None => my
    end.

  Instance: Proper ((=) ==> (=) ==> (=)) option_op.
  Proof. intros [?|] [?|] ? ???; simpl; try setoid_discriminate; auto. Qed.


  
  Lemma option_equiv_alt x y :
    x = y -> (∀ n, x = Some n ↔ y = Some n).
  Proof.
    intros E1 n.
    split. intros. now rewrite <- E1. intros. now rewrite E1.
  Qed.
  (*
    destruct x, y.
       apply E1. 
      symmetry. now apply E1.
     now apply E1.
    easy.
  Qed. *)

End contents.

Hint Extern 10 (Equiv (option _)) => apply @option_equiv : typeclass_instances.

Section mcontents.
  Context `{Setoid A}.

  Global Instance: Setoid (option A).
  Proof.
    split.
     intros [x|]. now apply option_equiv_Some. now apply option_equiv_None.
     red. induction 1. now apply option_equiv_Some. now apply option_equiv_None.
    intros x y z E. revert z. induction E.
     intros z E2. inversion_clear E2.
     apply option_equiv_Some. etransitivity; eassumption.
    easy.
  Qed.

  Global Instance: Setoid_Morphism Some.
  Proof. split; try apply _. Qed.

  Instance: Proper ((=) ==> (=) ==> (=)) option_op.
  Proof. intros [?|] [?|] ? ???; simpl; try setoid_discriminate; auto. Qed.

  
  Global Instance: Monoid (option A).
  Proof. repeat (split; try apply _); now repeat intros [?|].
  Qed.

  Global Instance: Setoid_Morphism Some.
  Proof. split; try apply _. Qed.

  Global Instance: Injective Some.
  Proof. split; try apply _. intros ? ? E. now inversion E. Qed.

  
  Global Program Instance option_dec `(A_dec : ∀ x y : A, Decision (x = y))
     : ∀ x y : option A, Decision (x = y) := λ x y,
    match x with
    | Some r =>
      match y with
      | Some s => match A_dec r s with left _ => left _ | right _ => right _ end
      | None => right _
      end
    | None =>
      match y with
      | Some s => right _
      | None => left _
      end
    end.
  Next Obligation. now apply (injective_ne Some). Qed.
  Next Obligation. setoid_discriminate. Qed.
  Next Obligation. setoid_discriminate. Qed.
End mcontents.


Lemma option_equiv_eq {A} (x y : option A) : 
  @option_equiv A (≡) x y ↔ x ≡ y.
Proof.
  split.
   induction 1. now f_equal. reflexivity.
  intros. subst.
  now assert (@Setoid A (@eq A)) by (split; apply _).
Qed.

Instance option_ret: MonadReturn option := λ A eqA x, Some x.
Instance option_bind: MonadBind option := λ A B eqA eqB f x,
  match x with
  | Some a => f a
  | None => None
  end.

Instance option_ret_proper `{eqA:Equiv A} : Proper ((=) ==> (=)) (option_ret A eqA).
Proof. intros x y E. now apply option_equiv_Some. Qed.

Instance option_bind_proper `{@PartialSetoid A eqA} `{@PartialSetoid B eqB}: Proper (=) (option_bind A B eqA eqB).
Proof.
  intros f₁ f₂ E1 x₁ x₂ [?|].
   unfold option_bind. simpl. now apply E1.
   simpl. econstructor.
Qed.

Instance: Monad option.
Proof.
  repeat (split; try apply _); unfold bind, ret, option_bind, option_ret, compose.
    intros. now apply setoids.ext_pequiv_refl.
   now intros ? ? ? [?|].
   intros A ? B ? C ? ? f [???] g [???] [x|] [y|] E; try solve [inversion_clear E].
   inversion E.
   assert (g x = g y). { apply psm_proper0. assumption. }
   case (g x), (g y).
   inversion H3. apply psm_proper. assumption. easy. easy. easy. easy.
Qed.

Instance option_map: SFmap option := fun A B eqA eqB => @option_map A B.

Instance: FullMonad option.
Proof. apply @monad_default_full_monad. apply _. Qed.

Section map.
  Context `{Setoid A} `{Setoid B} `{!Injective (f : A → B)}.

  Global Instance: Injective (sfmap f).
  Proof.
    pose proof (injective_mor f).
    repeat (split; try apply _).
    intros [x|] [y|] E; try solve [inversion E | easy].
    apply sm_proper. apply (injective f). now apply (injective Some).
  Qed.
End map.

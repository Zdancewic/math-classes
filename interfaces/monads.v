Require Import
  MathClasses.interfaces.abstract_algebra MathClasses.interfaces.canonical_names.
Require Export
  MathClasses.interfaces.functors.


(* SAZ: If the monad operations can depend on the equivalence used
   for [A], they need to be parameterized by eqA.  It doesn't
   seem likely that they would need to use equivalences on B or (M B)
   so I've omitted those.

   Without this added generality, it doesn't seem possible to prove
   that, for instance, the ret of the PM monad is proper.

   However, adding these additional parameters 
 *)

Section ops.
  Context (M : Type -> Type).

  Global Class MonadReturn := ret: forall {A} {eqA:Equiv A}, A → M A.
  Global Class MonadBind := bind: ∀ {A B} {eqA:Equiv A} {eqB:Equiv B}, (A → M B) → M A → M B.
  Global Class MonadJoin := join: forall {A} {eqA:Equiv A}, M (M A) → M A.
End ops.

Arguments ret {M MonadReturn A} _.
Arguments bind {M MonadBind A B } _ _ _.
Arguments join {M MonadJoin A _} _.

Notation "m ≫= f" := (bind _ _ f m) (at level 60, right associativity) : mc_scope.
Notation "x ← y ; z" := (y ≫= (λ x : _, z)) (at level 65, (*next at level 35, *) right associativity, only parsing) : mc_scope.
(* Notation "x ≫ y" := (_ ← x ; y) (at level 33, right associativity, only parsing) : mc_scope. *)

Class Monad (M : Type → Type) `{eqM:∀ A, Equiv A → Equiv (M A)} 
     `{MonadReturn M} `{MonadBind M} : Prop :=
  { mon_ret_proper `{@PartialSetoid A eqA} :> Proper ((=) ==> (=)) (@ret _ _ A _) 
  ; mon_bind_proper `{@PartialSetoid A eqA} `{@PartialSetoid B eqB} :>
    Proper (((=) ==> (=)) ==> (=) ==> (=)) (@bind _ _ A B _ _)
  ; mon_psetoid `{@PartialSetoid A eqA} :> PartialSetoid (M A)
  ; bind_lunit `{eqA:Equiv A} `{@PartialSetoid B eqB} `{!PartialSetoid_Morphism (f : A → M B)} : (bind _ _ f ∘ ret _) = f 
  ; bind_runit `{stA:PartialSetoid A} : bind _ _ (ret _) = id 
  ; bind_assoc `{eqA:Equiv A} `{eqB:Equiv B} `{@PartialSetoid C eqC} 
         `{!PartialSetoid_Morphism (f : B → M C)} `{!PartialSetoid_Morphism (g : A → M B)} :
      bind _ _ f ∘ bind _ _ g = bind _ _ (bind _ _ f ∘ g) }.

Class StrongMonad (M : Type → Type) `{eqM:∀ A, Equiv A → Equiv (M A)}
     `{MonadReturn M} `{SFmap M} `{MonadJoin M} : Prop :=
  { smon_ret_proper `{@PartialSetoid A eqA} :> Proper ((=) ==> (=)) (@ret _ _ A _)
  ; smon_join_proper `{@PartialSetoid A eqA} :> Proper ((=) ==> (=)) (@join _ _ A _)
  ; smon_sfunctor :> SFunctor M
  ; sfmap_ret `{eqA:Equiv A} `{eqB:Equiv B} `{!PartialSetoid_Morphism (f : A → B)} :
      sfmap f ∘ (ret _) = (ret _) ∘ f
  ; sfmap_join `{eqA:Equiv A} `{eqB:Equiv B} `{!PartialSetoid_Morphism (f : A → B)} : 
      sfmap f ∘ (@join _ _ A _) = (@join _ _ B _) ∘ sfmap (sfmap f)
  ; join_ret `{@PartialSetoid A eqA} :
      (@join _ _ A _) ∘ (@ret _ _ (M A) _) = id
  ; join_sfmap_ret `{@PartialSetoid A eqA} :
      (@join _ _ A _ ) ∘ sfmap (@ret _ _ A _) = id
  ; join_sfmap_join `{PartialSetoid A} :
      join ∘ sfmap join = join ∘ join }.

Class FullMonad (M : Type → Type) `{∀ A, Equiv A → Equiv (M A)} 
     `{MonadReturn M} `{MonadBind M} `{SFmap M} `{MonadJoin M} : Prop := 
  { full_mon_mon :> Monad M
  ; full_smon :> StrongMonad M
  ; bind_as_join_sfmap `{eqA:Equiv A} `{@PartialSetoid B eqB} `{!PartialSetoid_Morphism (f : A → M B)} :
      (@bind _ _ A B _ _ f) = (@join _ _ B _) ∘ (sfmap f) }.



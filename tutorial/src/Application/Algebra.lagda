% Abstract Algebra in Agda

\begin{code}
module Application.Algebra where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; setoid ; sym)

import Relation.Binary.EqReasoning as EqR
\end{code}


Semigroup property
=====================

Let `A` be a type and let `_∙_` be a binary operation on `A`.
`A` with `_∙_` forms a semigroup iff `_∙_` is associative.

We can model the semigroup proposition as follows:

\begin{code}
record IsSemigroup {A : Set} (_∙_ : A → A → A) : Set where
  field
    assoc         : ∀ x y z →  (x ∙ y) ∙ z  ≡  x ∙ (y ∙ z)
    ∙-cong  :   ∀ {x y u v} → x ≡ y → u ≡ v → (x ∙ u ) ≡ (y ∙ v) 
\end{code}


Exercise
========

Prove that `ℕ` with `_+_` forms a semigroup!

\begin{code}
ℕ+-isSemigroup : IsSemigroup _+_
\end{code}

<!--
\begin{code}
ℕ+-isSemigroup = record
  { assoc = +-assoc;
   ∙-cong = +-cong
  }
 where
  +-assoc : ∀ x y z →  (x + y) + z  ≡  x + (y + z)
  +-assoc zero    _ _ = refl
  +-assoc (suc m) n o = cong suc (+-assoc m n o)
  +-cong :  ∀ {x y u v} → x ≡ y → u ≡ v → (x + u ) ≡ (y + v)
  +-cong refl refl = refl
\end{code}
-->


Usage
=====

Usage example:

\begin{code}
module Usage₁ where
  open IsSemigroup

  ex : ∀ n → (n + 1) + 1 ≡ n + 2
  ex n = assoc ℕ+-isSemigroup n 1 1
\end{code}

With applied module opening:

\begin{code}
module Usage₂ where
  open IsSemigroup ℕ+-isSemigroup

  ex : ∀ n → (n + 1) + 1 ≡ n + 2
  ex n = assoc n 1 1
\end{code}

With local module opening:

\begin{code}
module Usage₃ where
  ex : ∀ n → (n + 1) + 1 ≡ n + 2
  ex n = assoc n 1 1  where
    open IsSemigroup ℕ+-isSemigroup
\end{code}


Monoid property
==================

`IsMonoid {A} _∙_ ε` represents the proposition that
(`A`, `_∙_`, `ε`) is a monoid:

\begin{code}
record IsMonoid {A : Set} (_∙_ : A → A → A) (ε : A) : Set where
  field
    isSemigroup : IsSemigroup _∙_
    identity    : (∀ x → ε ∙ x ≡ x)  ×  (∀ x → x ∙ ε ≡ x)

  open IsSemigroup isSemigroup public
\end{code}

Public opening at the end makes usage of `IsMonoid` easier.


Exercise
========

Prove that (`ℕ`, `_+_`, `0`) forms a monoid!

\begin{code}
ℕ+0-isMonoid : IsMonoid _+_ 0
\end{code}

<!--
\begin{code}
ℕ+0-isMonoid = record
  { isSemigroup = ℕ+-isSemigroup
  ; identity = left-identity , right-identity
  }
 where
  left-identity : ∀ n → 0 + n ≡ n
  left-identity _ = refl

  right-identity : ∀ n → n + 0 ≡ n
  right-identity zero = refl
  right-identity (suc n) = cong suc (right-identity n)
\end{code}
-->


Usage
=====

Usage example:

\begin{code}
module Usage₄ where
  ex : ∀ n → (n + 0) + n ≡ n + n
  ex n = cong (λ x → x + n) (proj₂ identity n)  where
    open IsMonoid ℕ+0-isMonoid

  ex′ : ∀ n → (n + 0) + n ≡ n + n
  ex′ n = assoc n 0 n  where
    open IsMonoid ℕ+0-isMonoid   -- we opened IsMonoid, not IsSemigroup 
\end{code}


Named binary operations
=======================

Instead of `A → A → A` we can write `Op₂ A` if we define

\begin{code}
Op₂ : Set → Set
Op₂ A = A → A → A
\end{code}

Thus we can write

\begin{code}
record IsSemigroup′ {A : Set} (_∙_ : Op₂ A) : Set where
  field
    assoc         : ∀ x y z →  (x ∙ y) ∙ z  ≡  x ∙ (y ∙ z)
\end{code}


Exercise
========

Define the type of unary operations as `Op₁`!

<!--
\begin{code}
Op₁ : Set → Set
Op₁ A = A → A
\end{code}
-->


Named function properties
=========================

We can name functions properties like

\begin{code}
Associative : {A : Set} → Op₂ A → Set
Associative _∙_ = ∀ x y z →  (x ∙ y) ∙ z  ≡  x ∙ (y ∙ z)
\end{code}

After this definition we can write

\begin{code}
record IsSemigroup″ {A : Set} (_∙_ : Op₂ A) : Set where
  field
    assoc         : Associative _∙_
\end{code}


Exercises
=========

Define the following function properties!

\begin{code}
Commutative : {A : Set} → Op₂ A → Set _
\end{code}

<!--
\begin{code}
Commutative _∙_ = ∀ x y →  x ∙ y  ≡  y ∙ x
\end{code}
-->

The first parameter of `LeftIdentity` is the neutral element.

\begin{code}
LeftIdentity : {A : Set} → A → Op₂ A → Set _
\end{code}

<!--
\begin{code}
LeftIdentity e _∙_ = ∀ x →  e ∙ x  ≡  x
\end{code}
-->

\begin{code}
RightIdentity : {A : Set} → A → Op₂ A → Set _
\end{code}

<!--
\begin{code}
RightIdentity e _∙_ = ∀ x →  x ∙ e  ≡  x
\end{code}
-->

\begin{code}
Identity : {A : Set} → A → Op₂ A → Set _
\end{code}

<!--
\begin{code}
Identity e ∙ = LeftIdentity e ∙ × RightIdentity e ∙
\end{code}
-->


Commutative monoid property
==============================

Consider the following definition of the commutative monoid proposition:

\begin{code}
record IsCommutativeMonoid′ {A : Set} (_∙_ : A → A → A) (ε : A) : Set where
  field
    isMonoid : IsMonoid _∙_ ε
    comm     : Commutative _∙_
\end{code}

This definition is correct, but redundant because
commutativity and left identity properties entail the right identity
property.

A non-redundant and still easy-to-use definition is the following:

\begin{code}
record IsCommutativeMonoid {A : Set} (_∙_ : A → A → A) (ε : A) : Set where
  field
    isSemigroup : IsSemigroup _∙_
    identityˡ   : LeftIdentity ε _∙_
    comm        : Commutative _∙_

  open IsSemigroup isSemigroup public

  identity : Identity ε _∙_
  identity = (identityˡ , identityʳ)
    where
    open EqR (setoid A)

    identityʳ : RightIdentity ε _∙_
    identityʳ = λ x → begin
      (x ∙ ε)  ≈⟨ comm x ε ⟩
      (ε ∙ x)  ≈⟨ identityˡ x ⟩
      x        
      ∎

  isMonoid : IsMonoid _∙_ ε
  isMonoid = record
    { isSemigroup = isSemigroup
    ; identity    = identity
    }
\end{code}

-   When constructing `IsCommutativeMonoid`, we should
    provide the semigroup, left identity and commutativity properties.
-   When using `IsCommutativeMonoid`, we have
    semigroup, associativity, monoid, identity and commutativity properties.


Exercises
=========


A) Define the group property!
\begin{code}
LeftInverse : {A : Set } → A → Op₂ A →  Op₁ A → Set _
LeftInverse ε _∙_ inv = ∀ x →  inv x ∙ x ≡ ε

RightInverse : {A : Set } → A → Op₂ A →  Op₁ A → Set _
RightInverse ε _∙_ inv = ∀ x →  x ∙ ( inv x ) ≡ ε

Inverse  : {A : Set } → A → Op₂ A →  Op₁ A → Set _
Inverse ε _∙_ inv = LeftInverse ε _∙_ inv × RightInverse ε _∙_ inv

LeftInverseOf' :{A : Set } → A → Op₂ A → A -> Set _
LeftInverseOf' ε _∙_ x = ∀ y -> y ∙ x ≡ ε -- wrong : veut dire que x annule tout y

LeftInverseOf :{A : Set } → A → Op₂ A → A -> A -> Set _
LeftInverseOf ε _∙_ x y =  y ∙ x ≡ ε


record IsGroup (A : Set) (_∙_ : Op₂ A) (li : Op₁ A) (ε : A) : Set where
  field
    isSemigroup : IsSemigroup  _∙_
    identity   :   Identity ε _∙_
    leftInverse  : LeftInverse ε _∙_ li
  
  open IsSemigroup isSemigroup
  open import Function
  open EqR ( setoid A)

  identityˡ   : LeftIdentity ε _∙_
  identityˡ  = proj₁ identity

  -- we dont need a right inverse given a left id and a left inverse 
  isInverse : Inverse ε _∙_ li
  isInverse = (leftInverse , rightInverse)
    where
      --open EqR ( setoid A) - 2014-12-14
      rightInverse : RightInverse ε _∙_ li
      rightInverse = λ x → begin
                       x ∙ (li x)                        ≈⟨ sym ( identityˡ _) ⟩
                       ε ∙ (x ∙ li x )                   ≈⟨ sym (leftInverse _) ⟨ ∙-cong ⟩ refl ⟩
                       (li(li x) ∙ li x) ∙ (x ∙ li x)    ≈⟨ assoc _ _ _ ⟩
                       li (li x) ∙ (li x ∙ (x ∙ li x))   ≈⟨ refl ⟨ ∙-cong ⟩ (sym (assoc _ _ _ ) ) ⟩
                       li (li x) ∙ ((li x ∙ x) ∙ (li x)) ≈⟨ refl ⟨ ∙-cong ⟩ (leftInverse _  ⟨ ∙-cong ⟩ refl) ⟩
                       li(li x) ∙ ((ε ∙ (li x) ) )       ≈⟨ refl ⟨ ∙-cong ⟩ (identityˡ _)    ⟩
                       li(li x) ∙ (li x)                 ≈⟨ leftInverse _  ⟩
                       ε
                       ∎


  rightHelper : ∀ {x y} -> y ≡ li x ∙ ( x ∙ y)
  rightHelper {x} {y} = begin
                          y   ≈⟨ sym (identityˡ _) ⟩
                          ε ∙ y ≈⟨ (sym (leftInverse _))  ⟨ ∙-cong  ⟩    refl ⟩
                          (li x ∙ x) ∙ y   ≈⟨ assoc _ _ _ ⟩
                          li x ∙ (x ∙ y) ∎

  -- this needs rightIdentity of ε !
  rightUniqueness : ∀  {g  h }  ->  g ∙ h ≡ ε  ->  h  ≡ li g 
  rightUniqueness  {g} {h} ph  = begin
                                  h   ≈⟨ sym (identityˡ _) ⟩
                                  ε ∙ h ≈⟨ sym (leftInverse g)  ⟨ ∙-cong  ⟩    refl ⟩
                                  (li g ∙ g) ∙ h   ≈⟨ assoc _ _ _ ⟩
                                  li g ∙ (g ∙ h)  ≈⟨ refl  ⟨ ∙-cong  ⟩  ph ⟩
                                  li g ∙ ε   ≈⟨ proj₂ identity _ ⟩
                                  li g ∎
                                
  liEps≡Eps : li ε ≡ ε
  liEps≡Eps = begin   --needs rightIdentity
                li ε         ≈⟨ sym (proj₂ identity _) ⟩
                li ε ∙ ε     ≈⟨ leftInverse _ ⟩
                ε ∎

  liInvolutive : ∀ { x} -> li (li x) ≡ x
  liInvolutive {x} = begin
                      li (li x)  ≈⟨ sym (proj₂ identity _) ⟩
                      li (li x) ∙ ε  ≈⟨ refl ⟨ ∙-cong ⟩ (sym (leftInverse x)) ⟩
                      li (li x) ∙ (li x ∙ x)  ≈⟨ sym $ assoc _ _ _ ⟩
                      (li (li x) ∙ li x) ∙ x  ≈⟨ leftInverse _ ⟨ ∙-cong ⟩ refl ⟩
                      ε ∙ x  ≈⟨ proj₁ identity _  ⟩
                      x ∎


  module Nowhere where
    isInverse' : Inverse ε _∙_ li
    isInverse' = (leftInverse , rightInverse)
     where
       --open EqR ( setoid A) -- 2014-12-13
       rightInverse : RightInverse ε _∙_ li
       rightInverse = λ x → begin
                        (x ∙ (li x))                     ≈⟨ sym ( identityˡ (x ∙ li x)) ⟩
                        ε ∙ (x ∙ li x )                  ≈⟨ sym (cong (λ a -> a ∙(x ∙ li x)) (leftInverse (li x) )) ⟩
                        (li(li x) ∙ li x) ∙ (x ∙ li x)   ≈⟨ assoc (li (li x)) (li x) ( x ∙ ( li x) ) ⟩
                        li (li x) ∙ (li x ∙ (x ∙ li x))  ≈⟨ cong (λ a -> li(li x) ∙ a) (sym (assoc (li x) x (li x)))  ⟩
                        li(li x) ∙ ((li x ∙ x) ∙ (li x)) ≈⟨ cong (λ a -> (li (li x)) ∙ (a ∙ li x)) (leftInverse x)  ⟩
                        li(li x) ∙ ((ε ∙ (li x) ) )      ≈⟨ cong (λ a -> li (li x) ∙ a)(identityˡ (li x))    ⟩
                        li(li x) ∙ (li x)                ≈⟨ leftInverse (li x)  ⟩
                        ε ∎

  
   
    linv =  LeftInverseOf ε _∙_ 
    inverseCompound : ∀  a lia b lib  ->  lia ∙ a ≡ ε  -> lib ∙ b ≡ ε  ->  (lib ∙ lia) ∙  (a ∙ b) ≡ ε 
    inverseCompound  a  lia   b  lib plia plib =  begin
                                               ((lib ∙ lia) ∙ (a ∙ b)) ≈⟨ sym ( assoc  (lib ∙ lia) a b )  ⟩
                                               (((lib ∙ lia) ∙ a) ∙ b) ≈⟨ cong  (λ x -> x ∙ b )  ( assoc  lib  lia a )  ⟩
                                               ((lib ∙ (lia ∙ a)) ∙ b) ≈⟨ cong  (λ x -> (lib ∙ x) ∙ b )  ( plia )  ⟩
                                               ((lib ∙ ε) ∙ b)         ≈⟨ assoc lib ε b  ⟩
                                               (lib ∙ (ε ∙ b))         ≈⟨  cong  (λ x -> lib ∙ x )  (identityˡ b ) ⟩
                                               (lib ∙ b)               ≈⟨  plib ⟩
                                               ε ∎

    lia1 : li ε ∙ ε ≡ ε
    lia1 = leftInverse ε

    lia2 : ((li ε) ∙ (li ε)) ∙ (ε ∙ ε)  ≡ ε
    lia2 = inverseCompound ε (li ε) ε (li ε) lia1 lia1

    lia4 : ((li (li ε)) ∙  (li ε)) ∙  (ε ∙ (li ε)) ≡ ε --
    lia4 = inverseCompound ε (li ε) (li ε) (li (li ε)) lia1 (leftInverse (li ε))

    lia5 :  ((li ε)  ∙ ε) ∙  (ε ∙ ε) ≡ ε --  (li ε) ∙ ε  ≡ ε 
    lia5 = inverseCompound ε ε ε (li ε) (identityˡ ε) lia1

    lia3 : ((li ε) ∙ (li ε)) ∙ (ε ∙ ε)  ≡ ε
    lia3 = begin
            (li ε ∙ li ε) ∙ (ε ∙ ε) ≈⟨ cong ( (λ a ->  ((li ε) ∙ (li ε)) ∙ a )) (identityˡ ε) ⟩
            (li ε ∙ li ε) ∙ ε       ≈⟨ assoc  (li ε) (li ε) ε ⟩
            li ε ∙ ( li ε ∙ ε )     ≈⟨ cong (λ a -> li ε ∙ a) (leftInverse ε) ⟩
            li ε ∙ ε                ≈⟨ leftInverse ε ⟩
            ε ∎
  

    rev :  ∀  {g  h }  ->  h ∙ g ≡ ε  -> g ∙ h ≡ ε
    rev {g} {h} p = begin
                         (g ∙ h)                     ≈⟨ sym ( identityˡ (g ∙ h)) ⟩
                         ε ∙ (g ∙ h )                  ≈⟨ sym (cong (λ a -> a ∙(g ∙ h)) (leftInverse (li g ))) ⟩
                         (li(li g) ∙ li g) ∙ (g ∙ h)   ≈⟨ assoc (li (li g)) (li g) ( g ∙ h ) ⟩
                         li (li g) ∙ (li g ∙ (g ∙ h))  ≈⟨ cong (λ a -> li(li g) ∙ a) (sym (assoc (li g) g h))  ⟩
                         li(li g) ∙ ((li g ∙ g) ∙ h) ≈⟨ cong (λ a -> (li (li g)) ∙ (a ∙ h)) (leftInverse g)  ⟩
                         li(li g) ∙ ((ε ∙ h ) )      ≈⟨ cong (λ a -> li (li g) ∙ a)(identityˡ h)    ⟩
                         li(li g) ∙ h                ≈⟨ refl  ⟩
                         {!!}


  
\end{code}
B) Define the abelian group property!


The type of all semigroups
==========================

We can define the type of semigroups as

\begin{code}
record Semigroup : Set₁ where
  infixl 7 _∙_
  field
    Carrier     : Set
    _∙_         : Op₂ Carrier
    isSemigroup : IsSemigroup _∙_

  open IsSemigroup isSemigroup public
\end{code}


Exercises
=========

A) Prove that (ℕ, +) is a semigroup (by proving that there is
a corresponding element of `Semigroup`)!

B) Define the types of all monoids as a record with fields `Carrier`, `_∙_`, `ε` and `isMonoid`!
<!--
\begin{code}
record Monoid : Set₁ where
  infixl 7 _∙_
  field
    Carrier  : Set
    _∙_      : Op₂ Carrier
    ε        : Carrier
    isMonoid : IsMonoid _∙_ ε

  open IsMonoid isMonoid public

  semigroup : Semigroup
  semigroup = record { isSemigroup = isSemigroup }
\end{code}
-->


Some defined operations
=======================

We can define the multiplication by a natural number in any monoid:

\begin{code}
module MonoidOperations (m : Monoid) where

  open Monoid m

  infixr 7 _×′_

  _×′_ : ℕ → Carrier → Carrier
  0     ×′ x = ε
  suc n ×′ x = x ∙ n ×′ x
\end{code}



Standard Library definitions
================

You can find the given definitions in the following Standard Library modules:

\begin{code}
import Algebra.FunctionProperties using (Op₁; Op₂)
import Algebra.FunctionProperties using (Associative; Commutative; LeftIdentity; RightIdentity; Identity) -- and more function properties
import Algebra.Structures using (IsSemigroup; IsMonoid; IsCommutativeMonoid) -- and more
import Algebra using (Semigroup; Monoid; CommutativeMonoid) -- and more
import Algebra.Operations -- some defined operations

import Data.Nat.Properties using (isCommutativeSemiring) -- this contains definitions like ℕ+0-isMonoid
\end{code}

Notable differences

-   The definitions are generalized from `_≡_` to an arbitrary equivalence relation.
-   The definitions are universe polymorphic (see later).

Example usage

\begin{code}
module StdLibUsage where
  open import Algebra.Structures as A using (IsCommutativeMonoid)
  open import Data.Nat.Properties using (isCommutativeSemiring)

  open A.IsCommutativeSemiring
  open A.IsCommutativeMonoid (+-isCommutativeMonoid isCommutativeSemiring)

  ex : ∀ n → (n + 1) + 1 ≡ n + 2
  ex n = assoc n 1 1
\end{code}

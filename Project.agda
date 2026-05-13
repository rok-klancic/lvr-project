{-# OPTIONS --prop #-}

module Project where

open import Data.Empty           using (⊥; ⊥-elim)
open import Data.Fin             using (Fin; zero; suc)
open import Data.List            using (List; []; _∷_; _++_; length; map)
open import Data.List.Properties using (map-id; map-∘)
open import Data.Maybe           using (Maybe; nothing; just)
open import Data.Product         using (Σ; _,_; proj₁; proj₂; Σ-syntax; _×_)
open import Data.Sum             using (_⊎_; inj₁; inj₂)
open import Data.Vec             using (Vec; []; _∷_)

open import Function             using (id; _∘_)

open import Relation.Nullary     using (¬_)

import Relation.Binary.PropositionalEquality as Eq
open Eq                          using (_≡_; refl; sym; trans; cong; subst; _≢_)

open import Axiom.Extensionality.Propositional using (Extensionality)
postulate fun-ext : ∀ {a b} → Extensionality a b

open import Data.Nat             using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _<_)
open import Data.Bool using (Bool; true; false)

---------------
-- Problem 1 --
---------------

data Formula : Set where
    Varᶠ : ℕ → Formula
    Negᶠ : Formula → Formula
    Andᶠ : Formula → Formula → Formula
    Orᶠ : Formula → Formula → Formula


---------------
-- Problem 2 --
---------------

data Literal : Set where
    Varᴸ : ℕ → Literal
    NegVarᴸ : ℕ → Literal

data NNF : Set where
    Litᴺ : Literal → NNF
    Andᴺ : NNF → NNF → NNF
    Orᴺ : NNF → NNF → NNF


---------------
-- Problem 3 --
---------------

to-nnf : (f : Formula) → NNF
to-nnf (Varᶠ x) = Litᴺ (Varᴸ x)
to-nnf (Negᶠ (Varᶠ x)) = Litᴺ (NegVarᴸ x)
to-nnf (Negᶠ (Negᶠ f)) = to-nnf f
to-nnf (Negᶠ (Andᶠ f f₁)) = Orᴺ (to-nnf (Negᶠ f)) (to-nnf (Negᶠ f₁))
to-nnf (Negᶠ (Orᶠ f f₁)) = Andᴺ (to-nnf (Negᶠ f)) (to-nnf (Negᶠ f₁))
to-nnf (Andᶠ f f₁) = Andᴺ (to-nnf f) (to-nnf f₁)
to-nnf (Orᶠ f f₁) = Orᴺ (to-nnf f) (to-nnf f₁)


---------------
-- Problem 4 --
---------------
data Dec (A : Set) : Set where
  yes :    A  → Dec A
  no  : (¬ A) → Dec A

record DecType : Set₁ where
  field
    carr   : Set
    test-≡ : (x y : carr) → Dec (x ≡ y)

open DecType



module Assoc (K : DecType) (V : Set) where

  Assoc : Set
  Assoc = List (carr K × V)

  infix 4 _∈_
  data _∈_ : carr K → Assoc → Set where
    ∈-here  : {k : carr K} {v : V} {kvs : Assoc} → k ∈ ((k , v) ∷ kvs)
    ∈-there : {k k' : carr K} {v : V} {kvs : Assoc} → k ∈ kvs → k ∈ ((k' , v) ∷ kvs)

  data NoDup : Assoc → Set where
    nodup-[]  : NoDup []
    nodup-cons : {k : carr K} {v : V} {kvs : Assoc}
               → (¬ (k ∈ kvs))
               → NoDup kvs
               → NoDup ((k , v) ∷ kvs)

  lookup : {k : carr K} {kvs : Assoc} → k ∈ kvs → V
  lookup {k} {(k , v) ∷ kvs} (∈-here {k} {v}) = v
  lookup {k} {(k' , v) ∷ kvs} (∈-there p) = lookup {k} {kvs} p

  _∈?_ : (k : carr K) → (kvs : Assoc) → Dec (k ∈ kvs)
  k ∈? [] = no λ ()
  k ∈? ((k' , v) ∷ kvs) with test-≡ K k k'
  ... | yes p = yes (subst (λ x → x ∈ ((k' , v) ∷ kvs)) (sym p) (∈-here {k = k'} {v}))
  ... | no np with k ∈? kvs
  ... | yes q = yes (∈-there q)
  ... | no nq = no helper where
        helper : k ∈ ((k' , v) ∷ kvs) → ⊥
        helper (∈-here {k = k'}) = np refl
        helper (∈-there q) = nq q

  _‼_ : (kvs : Assoc) → (k : carr K) → Maybe V
  [] ‼ k = nothing
  ((k' , v) ∷ kvs) ‼ k with test-≡ K k k'
  ... | yes _ = just v
  ... | no _ = kvs ‼ k

  _[_]≔_ : Assoc → carr K → V → Assoc
  [] [ k ]≔ v = (k , v) ∷ []
  ((k' , v') ∷ kvs) [ k ]≔ v with test-≡ K k k'
  ... | yes _ = ((k' , v) ∷ kvs)
  ... | no _ = (k' , v') ∷ (kvs [ k ]≔ v)

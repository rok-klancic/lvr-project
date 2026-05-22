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


-- DecType instance for ℕ
ℕ-DecType : DecType
ℕ-DecType = record
  { carr = ℕ
  ; test-≡ = test-≡-ℕ
  }
  where
    test-≡-ℕ : (x y : ℕ) → Dec (x ≡ y)
    test-≡-ℕ zero zero = yes refl
    test-≡-ℕ zero (suc y) = no λ ()
    test-≡-ℕ (suc x) zero = no λ ()
    test-≡-ℕ (suc x) (suc y) with test-≡-ℕ x y
    ... | yes p = yes (cong suc p)
    ... | no np = no λ { refl → np refl }

-- Open Assoc module for ℕ and Bool
open Assoc ℕ-DecType Bool public

-- Assignment type
Assignment : Set
Assignment = Assoc


---------------
-- Problem 5 --
---------------

-- Helper functions for Maybe Bool operations
not-maybe : Maybe Bool → Maybe Bool
not-maybe nothing = nothing
not-maybe (just true) = just false
not-maybe (just false) = just true

and-maybe : Maybe Bool → Maybe Bool → Maybe Bool
and-maybe (just true) (just true) = just true
and-maybe (just true) (just false) = just false
and-maybe (just false) _ = just false
and-maybe _ (just false) = just false
and-maybe nothing _ = nothing
and-maybe _ nothing = nothing

or-maybe : Maybe Bool → Maybe Bool → Maybe Bool
or-maybe (just true) _ = just true
or-maybe _ (just true) = just true
or-maybe (just false) (just false) = just false
or-maybe nothing _ = nothing
or-maybe _ nothing = nothing

-- Evaluation function
eval : Assignment → Formula → Maybe Bool
eval assn (Varᶠ x) = assn ‼ x
eval assn (Negᶠ f) = not-maybe (eval assn f)
eval assn (Andᶠ f₁ f₂) = and-maybe (eval assn f₁) (eval assn f₂)
eval assn (Orᶠ f₁ f₂) = or-maybe (eval assn f₁) (eval assn f₂)


---------------
-- Problem 6 --
---------------

-- Helper function to evaluate a literal
eval-literal : Assignment → Literal → Maybe Bool
eval-literal assn (Varᴸ x) = assn ‼ x
eval-literal assn (NegVarᴸ x) = not-maybe (assn ‼ x)

-- Evaluation function for NNF formulas
eval-nnf : Assignment → NNF → Maybe Bool
eval-nnf assn (Litᴺ lit) = eval-literal assn lit
eval-nnf assn (Andᴺ f₁ f₂) = and-maybe (eval-nnf assn f₁) (eval-nnf assn f₂)
eval-nnf assn (Orᴺ f₁ f₂) = or-maybe (eval-nnf assn f₁) (eval-nnf assn f₂)

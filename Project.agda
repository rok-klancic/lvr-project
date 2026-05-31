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


---------------
-- Problem 7 --
---------------

-- Disjunct represents a disjunction of literals (a clause)
data Disjunct : Set where
    Litᴰ : Literal → Disjunct
    Orᴰ : Literal → Disjunct → Disjunct

-- CNF represents a conjunction of disjuncts
data CNF : Set where
    Disjᶜ : Disjunct → CNF
    Andᶜ : Disjunct → CNF → CNF


---------------
-- Problem 8 --
---------------

-- Helper function to evaluate a disjunct (clause)
eval-disjunct : Assignment → Disjunct → Maybe Bool
eval-disjunct assn (Litᴰ lit) = eval-literal assn lit
eval-disjunct assn (Orᴰ lit d) = or-maybe (eval-literal assn lit) (eval-disjunct assn d)

-- Evaluation function for CNF formulas
eval-cnf : Assignment → CNF → Maybe Bool
eval-cnf assn (Disjᶜ d) = eval-disjunct assn d
eval-cnf assn (Andᶜ d cnf) = and-maybe (eval-disjunct assn d) (eval-cnf assn cnf)


---------------
-- Problem 9 --
---------------

-- Result type for SAT solver
data SATResult : Set where
  sat : Assignment → SATResult
  unsat : SATResult

-- Helper: Extract variable from a literal
lit-var : Literal → ℕ
lit-var (Varᴸ n) = n
lit-var (NegVarᴸ n) = n

-- Helper: Check if literal is positive
is-positive : Literal → Bool
is-positive (Varᴸ _) = true
is-positive (NegVarᴸ _) = false

-- Helper: Negate a literal
negate-lit : Literal → Literal
negate-lit (Varᴸ n) = NegVarᴸ n
negate-lit (NegVarᴸ n) = Varᴸ n

-- Helper: Check if two literals are equal
lit-eq : Literal → Literal → Bool
lit-eq (Varᴸ m) (Varᴸ n) with test-≡ ℕ-DecType m n
... | yes _ = true
... | no _ = false
lit-eq (NegVarᴸ m) (NegVarᴸ n) with test-≡ ℕ-DecType m n
... | yes _ = true
... | no _ = false
lit-eq _ _ = false

-- Helper: Convert disjunct to list of literals
disjunct-to-list : Disjunct → List Literal
disjunct-to-list (Litᴰ lit) = lit ∷ []
disjunct-to-list (Orᴰ lit d) = lit ∷ (disjunct-to-list d)

-- Helper: Convert CNF to list of clauses (where each clause is a list of literals)
cnf-to-clauses : CNF → List (List Literal)
cnf-to-clauses (Disjᶜ d) = (disjunct-to-list d) ∷ []
cnf-to-clauses (Andᶜ d cnf) = (disjunct-to-list d) ∷ (cnf-to-clauses cnf)

-- Helper: Check if a clause is empty
is-empty-clause : List Literal → Bool
is-empty-clause [] = true
is-empty-clause _ = false

-- Helper: Check if any clause is empty (means UNSAT)
has-empty-clause : List (List Literal) → Bool
has-empty-clause [] = false
has-empty-clause (c ∷ cs) with is-empty-clause c
... | true = true
... | false = has-empty-clause cs

-- Helper: Check if all clauses are satisfied (empty list = all removed = SAT)
all-satisfied : List (List Literal) → Bool
all-satisfied [] = true
all-satisfied _ = false

-- Helper: Check if literal is in a clause
lit-in-clause : Literal → List Literal → Bool
lit-in-clause lit [] = false
lit-in-clause lit (l ∷ ls) with lit-eq lit l
... | true = true
... | false = lit-in-clause lit ls

-- Helper: Remove a literal from a clause
remove-lit : Literal → List Literal → List Literal
remove-lit lit [] = []
remove-lit lit (l ∷ ls) with lit-eq lit l
... | true = remove-lit lit ls
... | false = l ∷ (remove-lit lit ls)

-- Helper: Simplify clauses given a literal assignment
-- Remove clauses containing the literal, and remove negated literal from remaining clauses
simplify-clauses : Literal → List (List Literal) → List (List Literal)
simplify-clauses lit [] = []
simplify-clauses lit (clause ∷ rest) with lit-in-clause lit clause
... | true = simplify-clauses lit rest  -- Clause is satisfied, remove it
... | false = (remove-lit (negate-lit lit) clause) ∷ (simplify-clauses lit rest)

-- Helper: Find a unit clause (clause with exactly one literal)
find-unit-clause : List (List Literal) → Maybe Literal
find-unit-clause [] = nothing
find-unit-clause ((lit ∷ []) ∷ _) = just lit
find-unit-clause (_ ∷ rest) = find-unit-clause rest

-- Helper: Choose an unassigned variable from the clauses
choose-variable : List (List Literal) → Maybe ℕ
choose-variable [] = nothing
choose-variable ((lit ∷ _) ∷ _) = just (lit-var lit)
choose-variable ([] ∷ rest) = choose-variable rest

-- Update assignment with a literal
update-assn-with-lit : Assignment → Literal → Assignment
update-assn-with-lit assn (Varᴸ n) = assn [ n ]≔ true
update-assn-with-lit assn (NegVarᴸ n) = assn [ n ]≔ false

-- Main DPLL algorithm with fuel (to ensure termination)
dpll-fuel : ℕ → Assignment → List (List Literal) → SATResult
dpll-fuel zero assn clauses = unsat  -- Out of fuel
dpll-fuel (suc n) assn clauses with all-satisfied clauses
... | true = sat assn  -- All clauses satisfied
... | false with has-empty-clause clauses
... | true = unsat  -- Empty clause means conflict
... | false with find-unit-clause clauses
... | just lit =
  let assn' = update-assn-with-lit assn lit
      clauses' = simplify-clauses lit clauses
  in dpll-fuel n assn' clauses'
... | nothing with choose-variable clauses
... | just var =
  let lit-pos = Varᴸ var
      assn-pos = update-assn-with-lit assn lit-pos
      clauses-pos = simplify-clauses lit-pos clauses
      result-pos = dpll-fuel n assn-pos clauses-pos
  in case result-pos of λ where
       (sat a) → sat a
       unsat → let lit-neg = NegVarᴸ var
                   assn-neg = update-assn-with-lit assn lit-neg
                   clauses-neg = simplify-clauses lit-neg clauses
               in dpll-fuel n assn-neg clauses-neg
... | nothing = sat assn  -- No more variables to assign

-- Main SAT solver for CNF
solve-cnf : CNF → SATResult
solve-cnf cnf =
  let clauses = cnf-to-clauses cnf
      fuel = 1000  -- Adjust as needed
  in dpll-fuel fuel [] clauses

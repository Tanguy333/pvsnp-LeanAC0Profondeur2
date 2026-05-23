/-
Copyright (c) 2026 Tanguy Le Mer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanguy Le Mer
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Basic
import Mathlib.Order.SetNotation
import Mathlib.Data.Nat.Lattice

/-!
# Définitions de base — bornes inférieures DNF sur AC⁰ profondeur 2

Ce fichier introduit les objets fondamentaux du paradigme étudié :

* `BoolFun n` — fonction booléenne sur `n` variables.
* `Monomial n` — un monôme (AND de littéraux signés).
* `DNF n` — un OR de monômes (= circuit AC⁰ profondeur 2 sous forme DNF,
  fan-in arbitraire).
* `isImplicant`, `isPrimeImplicant` — notions usuelles d'implicant.
* `dnfMin f` — taille minimale d'un DNF calculant `f`.

## Représentation choisie

* Un **monôme** est représenté comme une fonction `Fin n → Option Bool` :
  pour chaque variable, soit elle est *absente* du monôme (`none`), soit
  elle y apparaît *positivement* (`some true`), soit *négativement*
  (`some false`).
* Un **DNF** est représenté comme une `List (Monomial n)` (l'OR de tous
  les monômes). On préfère `List` à `Finset` car on n'a pas besoin de
  contraintes `DecidableEq` côté monômes, et les opérations
  syntaxiques (ajout, retrait, sélection d'un sous-DNF) sont directes.

## Note sur le scope

Ces définitions servent de socle pour les théorèmes L12 (parité), L13
(caractérisation par independent set), L14 (majorité), L15 (seuil), L16
(modulo p), L18 (inner product) et L19 (caractérisation d'essentialité),
ainsi que L20 (pôle extrême antipodal) issus du repo
`Tanguy333/pvsnp-exploration`.

-/

namespace PvsnpLeanAC0Profondeur2

variable {n : ℕ}

/-! ## Fonctions booléennes -/

/-- Une fonction booléenne sur `n` variables. -/
abbrev BoolFun (n : ℕ) : Type := (Fin n → Bool) → Bool

/-! ## Monômes -/

/-- Un monôme sur `n` variables :
* `m i = none` signifie que la variable `i` n'apparaît pas dans le monôme ;
* `m i = some true` signifie qu'elle apparaît positivement ;
* `m i = some false` signifie qu'elle apparaît négativement.

Le monôme vide (tout à `none`) représente la conjonction vide, qui est
identiquement `true`. -/
abbrev Monomial (n : ℕ) : Type := Fin n → Option Bool

namespace Monomial

/-- Le monôme `m` est satisfait par l'affectation `x` : pour chaque
variable fixée par `m`, la valeur correspond à celle de `x`. -/
def satisfies (m : Monomial n) (x : Fin n → Bool) : Prop :=
  ∀ i, ∀ b, m i = some b → x i = b

instance (m : Monomial n) (x : Fin n → Bool) : Decidable (satisfies m x) := by
  unfold satisfies
  infer_instance

/-- Nombre de littéraux du monôme (variables fixées, en `some _`). -/
def size (m : Monomial n) : ℕ :=
  (Finset.univ.filter fun i : Fin n => (m i).isSome).card

/-- Le monôme `m` *couvre* `m'` si tout ce que `m'` fixe, `m` le fixe à
la même valeur. Concrètement, `m` est *plus contraignant ou égal à* `m'`.
-/
def covers (m m' : Monomial n) : Prop :=
  ∀ i b, m' i = some b → m i = some b

/-- Le monôme `top` ne fixe aucune variable ; il est satisfait par toute
affectation et a taille `0`. -/
def top : Monomial n := fun _ => none

@[simp] lemma top_satisfies (x : Fin n → Bool) : (top : Monomial n).satisfies x := by
  intro i b h
  simp [top] at h

end Monomial

/-! ## DNF (Disjunctive Normal Form) -/

/-- Un DNF sur `n` variables : une liste de monômes (l'OR de tous). -/
abbrev DNF (n : ℕ) : Type := List (Monomial n)

namespace DNF

/-- Évaluation d'un DNF sur une affectation `x` : `true` si au moins un
monôme est satisfait. -/
def eval (d : DNF n) (x : Fin n → Bool) : Bool :=
  d.any (fun m => decide (m.satisfies x))

/-- `d` calcule la fonction booléenne `f`. -/
def computes (d : DNF n) (f : BoolFun n) : Prop :=
  ∀ x, d.eval x = f x

/-- Taille (nombre de monômes) d'un DNF. -/
def size (d : DNF n) : ℕ := d.length

end DNF

/-! ## Implicants et implicants premiers -/

/-- Le monôme `m` est un *implicant* de `f` si :
* il est non-vacuously satisfaisable (au moins un `x` le satisfait), et
* toute affectation le satisfaisant donne `f x = true`.

La condition de non-vacuité écarte le « monôme contradictoire » (qu'on
ne devrait jamais générer dans notre représentation, mais on l'écarte
par sécurité). -/
def isImplicant (f : BoolFun n) (m : Monomial n) : Prop :=
  (∃ x, m.satisfies x) ∧ (∀ x, m.satisfies x → f x = true)

/-- Le monôme `m` est un *implicant premier* de `f` : c'est un implicant
minimal au sens de `Monomial.covers` (on ne peut pas étendre `m` à un
implicant strictement plus permissif). -/
def isPrimeImplicant (f : BoolFun n) (m : Monomial n) : Prop :=
  isImplicant f m ∧
    ∀ m', isImplicant f m' → Monomial.covers m m' → m = m'

/-! ## DNF minimum

`dnfMin f` est la taille minimale d'un DNF calculant `f`. Pour que cette
définition soit utile, on doit prouver qu'il existe au moins un DNF
calculant `f` (la non-vacuité de l'ensemble considéré par `sInf`). Le
témoin canonique est le « DNF des mintermes complets » : pour chaque
`x ∈ f^{-1}(1)`, on prend le monôme qui fixe chaque variable à la valeur
de `x i`. Sa réalisation Lean est laissée en `sorry` pour une itération
ultérieure (elle nécessite un peu de combinatoire élémentaire mais
n'affecte pas les énoncés des théorèmes L12-L20). -/

/-- Le minterme complet associé à une affectation `x` : pour chaque
variable `i`, on fixe `m i = some (x i)`. -/
def mintermOf (x : Fin n → Bool) : Monomial n :=
  fun i => some (x i)

/-- DNF canonique d'une fonction `f` : OR des mintermes des `x` tels que
`f x = true`. La preuve qu'il calcule bien `f` est laissée en `sorry`. -/
def canonicalDNF (f : BoolFun n) : DNF n :=
  sorry  -- à réaliser : énumérer les `x : Fin n → Bool` avec `f x = true`,
         -- puis prendre la liste des `mintermOf x`.

/-- Le DNF canonique calcule `f`. -/
theorem canonicalDNF_computes (f : BoolFun n) :
    (canonicalDNF f).computes f := by
  sorry

/-- Taille minimale d'un DNF calculant `f`.

Définie comme l'infimum des tailles des DNF calculant `f`. Marquée
`noncomputable` car `sInf` sur des ensembles d'entiers est non-décidable
sans hypothèse de finitude visible au type-checker. -/
noncomputable def dnfMin (f : BoolFun n) : ℕ :=
  sInf {k | ∃ d : DNF n, d.computes f ∧ d.size = k}

end PvsnpLeanAC0Profondeur2

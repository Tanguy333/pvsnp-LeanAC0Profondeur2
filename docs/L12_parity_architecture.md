# Architecture de preuve — L12 : `dnfMin parity_n = 2^(n-1)`

Document de conception **rédigé avant tout code Lean**. Objectif : décomposer
la preuve mathématique du Tour 12 (parent) en lemmes Lean atomiques,
identifier les dépendances Mathlib, anticiper les obstacles techniques, et
fixer l'ordre de formalisation.

---

## 1. Énoncé cible

```lean
theorem dnfMin_parity (n : ℕ) (hn : 0 < n) :
    dnfMin (parity n) = 2 ^ (n - 1)
```

où `parity n : BoolFun n` est la fonction « somme des bits mod 2 ».

**Convention** : on suit la convention `parity_n(x) = 1` ssi le nombre de
1-bits dans `x` est *impair* (= sum mod 2). Cohérent avec le Tour 12 du
parent et la convention standard FSS 1981.

**Cas n = 0** : `parity 0` est la fonction constante `false` (somme vide
= 0 = pair). Le DNF minimal calculant `false` est `[]` (taille 0). Convention
`2 ^ (0 - 1) = 2^0 = 1` (à cause de la soustraction naturelle dans `ℕ`)
serait incorrect. D'où l'hypothèse `0 < n`.

---

## 2. Décomposition en lemmes intermédiaires

La preuve du parent (Tour 12) est en 4 pas L12.1 → L12.4. On la traduit
en Lean comme suit.

### 2.1 Lemme `monomial_freeVar_flip` (préliminaire technique)

**Énoncé.** Soit `m : Monomial n` un monôme avec `m.size < n`. Alors il
existe `i : Fin n` tel que `m i = none` (variable libre).

```lean
lemma monomial_freeVar_of_small (m : Monomial n) (h : m.size < n) :
    ∃ i, m i = none
```

**Idée preuve.** Par contraposition : si `∀ i, m i ≠ none`, alors `m.size = n`
(tous les bits sont fixés). Comptage trivial via `Finset.filter`.

**Dépendances Mathlib.** `Mathlib.Data.Finset.Card`, lemme du type
`Finset.filter_card_eq_card_iff` ou équivalent.

**Obstacle anticipé.** Aucun majeur. Le lemme de cardinalité existe en
Mathlib sous une forme proche.

---

### 2.2 Lemme L12.1 : `notImplicant_of_small`

**Énoncé.** Tout monôme de taille `< n` n'est pas un implicant de `parity_n`
(condition implicit : pour `n ≥ 1`, sinon `parity` est constant).

```lean
lemma notImplicant_of_small (n : ℕ) (hn : 0 < n)
    (m : Monomial n) (h : m.size < n) :
    ¬ isImplicant (parity n) m
```

**Idée preuve (parent Tour 12 L12.1).**
1. Par 2.1, soit `i` une variable libre de `m`.
2. Si `m` n'a aucun satisfaisant : alors la première composante de
   `isImplicant` (`∃ x, m.satisfies x`) est fausse, donc `¬ isImplicant`.
   *Vérification* : la représentation `Fin n → Option Bool` ne contient
   pas de contradiction par construction (chaque variable a un unique
   état dans `Option Bool`), donc `m.satisfies` est toujours satisfaisable.
   En pratique, l'affectation `fun j => (m j).getD true` satisfait `m`.
3. Soit donc `x` un satisfaisant de `m` (par 2). Considérer `x'` = `x` avec
   `x' i = !x i` (flipper le bit `i`). Comme `m i = none`, `m.satisfies x'`
   tient encore.
4. `parity n x ≠ parity n x'` (un seul bit a changé, parité bascule).
5. Donc l'un des deux est `false`, contradiction avec
   `m.satisfies x' → parity n x' = true`.

**Sous-lemmes nécessaires.**

* `parity_flip` :
  ```lean
  lemma parity_flip (n : ℕ) (x : Fin n → Bool) (i : Fin n) :
      parity n (Function.update x i (!x i)) = !(parity n x)
  ```
  *Preuve* : par calcul direct, `parity` est `Fin.sum mod 2` ; flipper un
  bit change la somme de ±1, donc bascule la parité.

* `satisfies_freeVar` :
  ```lean
  lemma satisfies_freeVar (m : Monomial n) (x : Fin n → Bool) (i : Fin n)
      (hm : m i = none) (hx : m.satisfies x) :
      m.satisfies (Function.update x i (!x i))
  ```
  *Preuve* : déroulage de `satisfies` ; comme `m i = none`, la condition
  sur le bit `i` est vacuément vraie.

**Obstacle anticipé.** Le calcul de `parity` après `Function.update`
demande un peu de manipulation `Finset.sum_update_of_mem` ou équivalent.
À vérifier que Mathlib fournit ces lemmes.

---

### 2.3 Lemme L12.2 : caractérisation des implicants premiers

**Énoncé.** Les implicants premiers de `parity_n` sont exactement les
mintermes complets associés aux affectations impaires.

```lean
lemma primeImplicants_parity_eq (n : ℕ) (hn : 0 < n) (m : Monomial n) :
    isPrimeImplicant (parity n) m ↔
      ∃ x : Fin n → Bool, parity n x = true ∧ m = mintermOf x
```

**Idée preuve.**

* **(⇐)** Si `m = mintermOf x` avec `parity x = true` :
  - C'est un implicant : `mintermOf x` n'est satisfait que par `x`
    (sous-lemme), et `parity x = true` par hypothèse.
  - C'est premier : tout implicant `m'` couvrant `m` (au sens
    `Monomial.covers m m'`) a la même structure. Si `m'` est strictement
    plus permissif, par L12.1 il aurait taille `< n` et ne serait pas
    implicant — contradiction. Donc `m' = m`.

* **(⇒)** Si `m` est un implicant premier de `parity_n` :
  - Par L12.1, `m.size = n` (sinon `m` n'est pas implicant).
  - Donc `m` fixe toutes les variables → `m = mintermOf x` pour `x` défini
    par `x i := (m i).get!` ou similaire.
  - `m` étant implicant et `m.satisfies x` (l'unique satisfaisant),
    `parity n x = true`.

**Sous-lemmes nécessaires.**

* `mintermOf_satisfies_iff` :
  ```lean
  lemma mintermOf_satisfies_iff (x y : Fin n → Bool) :
      (mintermOf x).satisfies y ↔ y = x
  ```

* `mintermOf_size` :
  ```lean
  lemma mintermOf_size (x : Fin n → Bool) : (mintermOf x).size = n
  ```

* `monomial_size_eq_n_iff_minterm` :
  ```lean
  lemma monomial_size_eq_n_iff_minterm (m : Monomial n) :
      m.size = n ↔ ∃ x, m = mintermOf x
  ```

**Obstacle anticipé.** Le passage de « `m` fixe toutes les variables » à
« `m = mintermOf x` pour un certain `x` » demande un argument
extensionnel sur des fonctions `Fin n → Option Bool` (avec `Option.some`).
Probablement `funext` + `Option.some_inj`.

---

### 2.4 Lemme L12.3 : non-redondance / nécessité des mintermes

**Énoncé.** Si `d : DNF n` calcule `parity_n`, alors pour toute affectation
impaire `x`, le DNF `d` contient le minterme `mintermOf x` (ou plus
précisément : l'un des monômes de `d` est `mintermOf x`).

```lean
lemma minterm_mem_of_computes (n : ℕ) (hn : 0 < n) (d : DNF n)
    (hd : d.computes (parity n))
    (x : Fin n → Bool) (hx : parity n x = true) :
    mintermOf x ∈ d
```

**Idée preuve.**

1. Comme `parity x = true`, `d.eval x = true`, donc un monôme `m ∈ d`
   satisfait `x`.
2. `m` est un implicant de `parity` (toute affectation `y` satisfaisant
   `m` est telle que `d.eval y = true`, donc `parity y = true` — utilise
   `hd`).
3. Par L12.1, `m.size = n`, donc `m = mintermOf y` pour un certain `y`.
4. Comme `m.satisfies x`, on a `x = y` (par `mintermOf_satisfies_iff`).
5. Donc `m = mintermOf x`, et `mintermOf x ∈ d`.

**Sous-lemme nécessaire.**

* `monomial_implicant_of_mem` :
  ```lean
  lemma monomial_implicant_of_mem (d : DNF n) (f : BoolFun n)
      (hd : d.computes f) (m : Monomial n) (hm : m ∈ d) :
      ∀ x, m.satisfies x → f x = true
  ```

  *Note* : il manque la condition « ∃ x, m.satisfies x » (non-vacuité) ;
  on l'a par construction puisque la représentation `Option Bool` ne
  permet pas de contradictions.

**Obstacle anticipé.** Aucun majeur, mais le pas 2 (l'implication
`d.eval y = true → parity y = true`) utilise `hd.computes` symétriquement.
Bien gérer le `decide` et l'évaluation booléenne vs propositionnelle.

---

### 2.5 Lemme `parity_truth_card` (combinatoire)

**Énoncé.** Le nombre d'affectations impaires sur `n` bits est `2^(n-1)`.

```lean
lemma parity_truth_card (n : ℕ) (hn : 0 < n) :
    (Finset.univ.filter fun x : Fin n → Bool => parity n x = true).card =
      2 ^ (n - 1)
```

**Idée preuve.** Classique : il y a `2^n` affectations totales, et la
bijection `x ↦ Function.update x 0 (!x 0)` (flipper le premier bit) est
une involution sans point fixe qui échange affectations paires et
impaires (cas particulier de bijection bit-flipping). Donc chaque classe
a `2^n / 2 = 2^(n-1)` éléments.

**Alternative** : preuve par récurrence sur `n`, avec décomposition
`parity (Fin (n+1)) x = parity (Fin n) (x ∘ Fin.succ) XOR x 0`.

**Dépendances Mathlib.** `Mathlib.Data.Finset.Card`, `Mathlib.Algebra.BigOperators`,
probablement `Mathlib.Combinatorics.Pigeonhole` ou récurrence.

**Obstacle anticipé.** Mathlib a probablement déjà `Bool.parity_card`
ou un lemme équivalent (`Fintype.card_subtype_filter` + bijection). À
vérifier. Sinon, preuve par récurrence pas trop longue.

---

### 2.6 Lemme L12.4 (théorème final) : `dnfMin parity_n = 2^(n-1)`

**Énoncé.** *(répété de §1)*

```lean
theorem dnfMin_parity (n : ℕ) (hn : 0 < n) :
    dnfMin (parity n) = 2 ^ (n - 1)
```

**Idée preuve.**

* **Borne inférieure (`≥`)** : par L12.3, tout DNF `d` calculant `parity_n`
  contient `mintermOf x` pour chaque `x` avec `parity x = true`. Ces
  mintermes sont distincts (par `mintermOf_satisfies_iff`, ils ont des
  satisfaisants distincts). Donc `d.size ≥ |{x | parity x = true}| =
  2^(n-1)` (par 2.5).

* **Borne supérieure (`≤`)** : le DNF des mintermes impairs a taille
  `2^(n-1)` et calcule `parity_n` (vérification directe).

**Sous-construction.**

```lean
def parity_canonicalDNF (n : ℕ) : DNF n :=
  (Finset.univ.filter (fun x : Fin n → Bool => parity n x = true)).toList.map mintermOf
```

avec lemmes :
* `parity_canonicalDNF_size : (parity_canonicalDNF n).size = 2^(n-1)`
* `parity_canonicalDNF_computes : (parity_canonicalDNF n).computes (parity n)`

**Obstacle anticipé.** La transition `Finset.filter → List.map` peut être
fastidieuse. Alternative : passer par `Finset.image mintermOf` puis
`Finset.toList`, ou définir `parity_canonicalDNF` directement comme `List`
via `List.range (2^n) |>.filterMap ...`. À calibrer.

---

## 3. Ordre de formalisation

```
Étape 1 : Définition de `parity n` (1 ligne).
Étape 2 : Lemme `parity_flip` (calcul direct, ~5-10 lignes).
Étape 3 : Lemme `parity_truth_card` (récurrence ou Mathlib, ~10-30 lignes).
Étape 4 : Lemmes Monomial / mintermOf (techniques, ~30 lignes).
          - mintermOf_satisfies_iff
          - mintermOf_size
          - monomial_size_eq_n_iff_minterm
          - satisfies_freeVar
          - monomial_freeVar_of_small
Étape 5 : Lemme L12.1 `notImplicant_of_small` (~15 lignes).
Étape 6 : Lemme L12.2 caractérisation implicants premiers (~25 lignes).
Étape 7 : Lemme L12.3 nécessité des mintermes (~15 lignes).
Étape 8 : Construction `parity_canonicalDNF` + ses propriétés (~30 lignes).
Étape 9 : Théorème final `dnfMin_parity` (~10 lignes, combinant 7 et 8).
```

**Total estimé** : ~150-200 lignes Lean pour Parity.lean.

**Ordre rationnel** : tous les lemmes techniques (3, 4) sont indépendants
de L12.1-L12.3 ; on les fait en premier. Puis L12.1 → L12.2 → L12.3 → L12.4.

---

## 4. Dépendances Mathlib anticipées

* `Mathlib.Data.Fin.Basic` : `Fin n`, `Function.update`.
* `Mathlib.Data.Finset.Card` : `Finset.filter`, `Finset.card`.
* `Mathlib.Data.Finset.Image` : `Finset.image`.
* `Mathlib.Data.Bool.Basic` : `Bool.xor`, `!`, `Bool.not_not`.
* `Mathlib.Algebra.BigOperators.Basic` : `Finset.sum`.
* `Mathlib.Data.Nat.Parity` : `Nat.parity` ou équivalent.
* `Mathlib.Tactic.FinCases` ou `Mathlib.Tactic.Decide` : pour les cas
  finis dans certaines preuves.
* `Mathlib.Tactic.Linarith` : arithmétique linéaire.

**À vérifier dès le premier build** :

* La définition de `parity` standard mathlib. Probablement utilise
  `Finset.sum` sur `Fin n` avec coefficients booléens convertis en `ℕ`,
  puis `mod 2`. Mathlib a `Nat.parity` mais pour `ℕ`, pas pour des
  fonctions `Fin n → Bool`. À encoder manuellement :
  ```lean
  def parity (n : ℕ) : BoolFun n :=
    fun x => decide ((Finset.univ.filter (fun i => x i = true)).card % 2 = 1)
  ```
  ou plus simplement via `Finset.sum` avec `Bool → ℕ` :
  ```lean
  def parity (n : ℕ) : BoolFun n :=
    fun x => decide ((∑ i, (if x i then 1 else 0 : ℕ)) % 2 = 1)
  ```
  ou via `xor` itéré :
  ```lean
  def parity (n : ℕ) : BoolFun n :=
    fun x => (Finset.univ : Finset (Fin n)).fold xor false x
  ```
  *La définition par `xor` itéré* semble la plus simple à manipuler car
  `xor` a des lois algébriques nettes et le flip d'un bit donne
  exactement `xor true` (= négation).

---

## 5. Obstacles techniques anticipés

### 5.1 `dnfMin` via `sInf` (Basic.lean)

`dnfMin f = sInf {k | ∃ d : DNF n, d.computes f ∧ d.size = k}`.

Pour utiliser `sInf` utilement, il faut montrer que l'ensemble argument
est non-vide. C'est `canonicalDNF_computes` (actuellement en `sorry` dans
Basic.lean).

**Action préalable** : avant L12, remplir le `sorry` de `canonicalDNF`
dans Basic.lean. Le `canonicalDNF` pour une fonction quelconque est l'OR
des mintermes complets des affectations à 1 :

```lean
def canonicalDNF (f : BoolFun n) : DNF n :=
  (Finset.univ.filter (fun x : Fin n → Bool => f x = true)).toList.map mintermOf
```

Cette construction est réutilisée dans `parity_canonicalDNF` (qui en est
un cas particulier pour `f = parity n`).

### 5.2 Décidabilité de `dnfMin`

`dnfMin` est `noncomputable` à cause de `sInf`. Pour des preuves d'égalité
`dnfMin f = k`, on devra utiliser :

* `Nat.sInf_eq_zero` ou
* `Nat.sInf_mem` quand l'ensemble est non-vide, ou
* `csInf_le` / `le_csInf` (les variantes conditionnellement).

À vérifier que Mathlib fournit les bons lemmes pour `sInf` sur `Set ℕ` ;
sinon, passer par `Nat.find`.

### 5.3 Définition de `parity` et `parity_flip`

Le pivot de tout L12 est `parity_flip` : flipper un bit bascule la parité.
Selon la définition de `parity` choisie (somme mod 2, fold xor, etc.), la
preuve diffère :

* Si `parity = fold xor false` : `parity_flip` se prouve via la
  commutativité de `xor` + `xor x x = false`.
* Si `parity = sum mod 2` : il faut `Finset.sum_update_of_mem` puis
  manipulation arithmétique.

**Recommandation** : commencer avec la définition `fold xor`, qui est plus
algébrique et adaptée aux preuves Lean.

### 5.4 Mismatch entre `m.satisfies x` (Prop) et `d.eval x = true` (Bool)

`m.satisfies x : Prop` est décidable, mais doit être converti en `Bool`
via `decide` pour entrer dans `d.eval`. Les preuves manipuleront souvent
`decide_eq_true_iff` ou `Bool.coe_iff`.

---

## 6. Plan de fichier `Parity.lean`

```lean
-- Imports
import PvsnpLeanAC0Profondeur2.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic.Linarith

namespace PvsnpLeanAC0Profondeur2

variable {n : ℕ}

-- §1. Définition de parity
def parity (n : ℕ) : BoolFun n := ...

-- §2. Lemmes techniques sur parity
lemma parity_flip ...
lemma parity_truth_card ...

-- §3. Lemmes techniques sur Monomial / mintermOf
lemma mintermOf_satisfies_iff ...
lemma mintermOf_size ...
lemma monomial_size_eq_n_iff_minterm ...
lemma monomial_freeVar_of_small ...
lemma satisfies_freeVar ...

-- §4. L12.1
lemma notImplicant_of_small ...

-- §5. L12.2
lemma primeImplicants_parity_eq ...

-- §6. L12.3
lemma minterm_mem_of_computes ...

-- §7. Construction du DNF canonique de parity
def parity_canonicalDNF ...
lemma parity_canonicalDNF_size ...
lemma parity_canonicalDNF_computes ...

-- §8. Théorème final
theorem dnfMin_parity ...

end PvsnpLeanAC0Profondeur2
```

---

## 7. Décisions à figer dès le premier build

1. **Définition de `parity`** : `fold xor` recommandé.
2. **Définition de `canonicalDNF` générique** (Basic.lean) : remplir le `sorry`
   avant L12. Choix de représentation : `List.map mintermOf` sur la liste
   triée des `x : Fin n → Bool` tels que `f x = true`.
3. **Manipulation `sInf` vs `Nat.find`** : préférer `Nat.find` si Mathlib
   ne fournit pas de lemme simple `sInf_eq` pour `Set ℕ` non-vide.

---

## 8. Risques et alternatives

* **Risque #1** : la définition `Monomial n := Fin n → Option Bool` peut
  s'avérer lourde pour certaines preuves (manipulations `Option.get!`,
  pattern matching). *Alternative* : représenter un monôme comme `Finset
  (Fin n × Bool)` (ensemble de littéraux). À évaluer après quelques
  lemmes : si Basic.lean devient pénible, refactoriser.

* **Risque #2** : `dnfMin` via `sInf` peut être difficile à manipuler.
  *Alternative* : `dnfMin f := Nat.find ⟨_, ...⟩` avec preuve d'existence
  inline. Plus simple en pratique.

* **Risque #3** : Les imports Mathlib peuvent être trop lents au build
  initial. *Alternative* : importer ponctuellement `Mathlib.Data.Bool.Basic`,
  `Mathlib.Data.Finset.Card`, etc., plutôt qu'un `import Mathlib` global.

---

## 9. Prochaine étape

Cette architecture validée, l'étape suivante est :

1. **Remplir `canonicalDNF` dans Basic.lean** (les 2 sorries actuels).
2. **Créer `Parity.lean` selon le plan §6**.
3. **Lancer `lake update && lake build` après §1** pour valider la définition
   de `canonicalDNF` avant d'attaquer L12.

Estimation : 1-2 sessions Lean intensives (avec build itératif).

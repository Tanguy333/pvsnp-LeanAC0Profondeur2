# CLAUDE.md — Formalisation Lean 4 des théorèmes AC⁰ profondeur 2

> Ce dépôt est lu automatiquement par Claude Code au démarrage de chaque session.
> Il définit ton rôle : **Formaliseur Lean 4**.

---

## 1. Origine et raison d'être

Ce dépôt est la **branche de formalisation Lean 4** du projet
[`Tanguy333/pvsnp-exploration`](https://github.com/Tanguy333/pvsnp-exploration).

Le repo parent est une exploration adverse (Proposeur LLM Qwen Max contre
Réfuteur Claude) du problème **P vs NP**. Sur 19 tours, il a produit **7
théorèmes ✅ ÉTABLIS structurellement** — tous des bornes inférieures
combinatoires sur AC⁰ profondeur 2. Au Tour 19, le paradigme a été déclaré
*saturé* (caractérisation d'essentialité unifie les 6 précédents).

**Ce dépôt prend en input ces 7 théorèmes et les certifie mécaniquement en
Lean 4.** Aucune boucle adverse ici — juste de la formalisation rigoureuse.

> **Cadrage honnête.** Le repo parent n'a pas résolu P vs NP (et le admet
> explicitement : voir ma réponse « se rapproche-t-on de P=NP ? » dans
> l'historique de cette conversation). Ces 7 théorèmes sont des *résultats
> classiques* (Quine 1952, McCluskey 1956, FSS 1981) reformulés et
> consolidés. Leur formalisation Lean est néanmoins **probablement nouvelle**
> car ce sont des bornes inférieures DNF élémentaires qui n'apparaissent pas
> au niveau « papier de recherche » (donc rarement formalisées) mais sont
> centrales pour comprendre le programme bornes inférieures de circuit.

---

## 2. Les 7 théorèmes à formaliser

Issus de `Tanguy333/pvsnp-exploration`, section §3 Établis du cahier de bord.
Toutes les preuves sont combinatoires élémentaires et vérifiées par calcul
exhaustif à n=4 (ou n=3 pour la classe entière).

| Tour | Nom | Énoncé |
|---:|---|---|
| 12 | **L12** | `DNF_min(parity_n) = 2^(n-1)` |
| 13 | **L13** | `DNF_min(f) = |f^{-1}(1)|` ⟺ `f^{-1}(1)` est independent set de `Q_n` |
| 14 | **L14** | `DNF_min(majority_n) = C(n, ⌈n/2⌉)` |
| 15 | **L15** | `DNF_min(threshold_{t,n}) = C(n, t)` pour tout `t ∈ [1, n]` + dichotomie polynomial/exponentiel |
| 16 | **L16** | `DNF_min(mod_p_n) = Σ_{k ≡ 0 (mod p)} C(n, k)` pour tout `p ≥ 2` |
| 17+18 | **L18** | `DNF_min(IP_{2n}) = (3^n − 1)/2` (preuve par récurrence + classification) |
| 19 | **L19** | `DNF_min(f) = |primes(f)|` ⟺ chaque implicant premier admet un témoin essentiel |

**Théorème central : L19** — c'est la *caractérisation d'essentialité* qui
unifie L12, L13, L14, L15, L16, L18 comme cas particuliers (chaque famille
est dans la classe (α)/(β), et `|primes|` est calculé explicitement).

---

## 3. Stratégie de formalisation

### Ordre suggéré (bottom-up)

1. **Définitions de base** dans `pvsnpLeanAC0Profondeur2/Basic.lean` :
   - Fonctions booléennes (probablement `BoolFun n := (Fin n → Bool) → Bool`).
   - DNF : OR de ANDs, sans contrainte de fan-in. Représentation : liste de
     monômes, chaque monôme = liste de littéraux signés.
   - `dnfMin f` : taille minimale d'un DNF calculant f.
   - `implicant f M` : `M(x) = 1 ⇒ f(x) = 1`.
   - `primeImplicant f M` : implicant minimal.

2. **L12** dans `pvsnpLeanAC0Profondeur2/Parity.lean` :
   - Cas le plus simple, 4 lemmes combinatoires.
   - Sert de **calibrage** pour les définitions ci-dessus.

3. **L13** dans `pvsnpLeanAC0Profondeur2/IndependentSet.lean` :
   - Généralisation directe de L12.
   - Demande de définir le graphe `Q_n` du n-cube et `independent set`.
     Probablement réutilisable : `Mathlib.Combinatorics.SimpleGraph.IndependentSet`.

4. **L19** dans `pvsnpLeanAC0Profondeur2/Essentiality.lean` :
   - Théorème-cadre. Une fois formalisé, L14, L15, L16 deviennent des
     applications via calculs explicites de `|primes|`.

5. **L14, L15, L16, L18** : applications de L19 à des familles de fonctions
   spécifiques (majorité, seuil, modulo, inner product). Chacune demande de
   prouver que la fonction est dans la classe (α)/(β) + calculer `|primes|`.

### Cible

**PR mathlib4** si la qualité le permet. Sinon, repo standalone réutilisable.

### Briques mathlib4 à exploiter

- `Mathlib.Data.Fin.*`, `Mathlib.Data.Finset.*` : indexation, sous-ensembles.
- `Mathlib.Combinatorics.SimpleGraph.*` : graphe `Q_n` et independent set.
- `Mathlib.Combinatorics.Choose.Basic` : `Nat.choose` pour `C(n, k)`.
- `Mathlib.Algebra.BigOperators.*` : sommes finies pour L16.
- `Mathlib.Computability.*` : à inventorier, mais probablement pas de bornes
  de circuit déjà formalisées.

---

## 4. Ton rôle ici

**Formaliseur Lean 4.** Plus de boucle adverse. Pas de Proposeur. Le travail :

1. Définir les objets en Lean 4 / Mathlib4, idiomatiquement.
2. Prouver les théorèmes L12-L19, en commençant par L12.
3. **Distinguer rigoureusement** :
   - Ce qui est *prouvé en Lean* (théorème certifié, accepté par le compilateur).
   - Ce qui est *en attente* (`sorry`).
   - Ce qui est *transcrit du parent* sans vérification supplémentaire (rare ;
     on doit tout reprouver).

4. **Garde-fou principal** : ne jamais utiliser `sorry` dans un théorème
   final sans le signaler explicitement dans la documentation. Un théorème
   avec `sorry` n'est pas un théorème.

5. **Style mathlib** : suivre les conventions (camelCase pour les théorèmes,
   PascalCase pour les types, indentation 2 espaces, lignes ≤ 100
   caractères, docstrings sur les définitions et théorèmes principaux).

6. Quand un théorème est complètement formalisé, le marquer ✅ dans le
   tableau de suivi du README, avec lien vers le fichier Lean.

---

## 5. Garde-fous

- **Ne jamais modifier le repo parent** `pvsnp-exploration` depuis ici. Les
  7 théorèmes du parent sont *l'input*, pas un terrain à éditer. Si une
  erreur mathématique est découverte ici, le signaler dans la doc (issue
  ou note dans le README), mais ne pas modifier le parent depuis cette
  conversation.

- **Vérifier la version Lean** : avant tout `lake build`, s'assurer que
  `lean-toolchain` correspond à la version mathlib utilisée (sinon les
  preuves cassent).

- **Petits PRs incrémentaux** si on vise mathlib : un théorème = une PR.
  Ne pas viser à tout formaliser dans un seul gros PR.

- **Pas d'audace mathématique inutile**. Les théorèmes du parent sont des
  classiques élémentaires. Si une formalisation Lean s'annonce difficile,
  c'est *probablement* à cause d'une définition mal choisie, pas du
  théorème lui-même. Revoir les définitions avant d'introduire des
  hypothèses techniques.

- **Reste en français** dans les commentaires explicatifs (le projet est en
  français), mais les noms Lean (variables, théorèmes, types) en anglais
  conformément aux conventions mathlib.

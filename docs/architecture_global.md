# Architecture globale — formalisation Lean des 8 théorèmes

Vue d'ensemble du plan de formalisation. Pour le détail de chaque
théorème, voir les fichiers `Lxx_*_architecture.md`.

---

## 1. Graphe de dépendances logiques

```
                   Basic.lean (definitions, mintermOf, canonicalDNF, dnfMin)
                                       │
                                       ▼
              ┌────────────────────────┴───────────────────────┐
              │                                                │
              ▼                                                ▼
         L12 (Parity)                                 (L19 prouvée séparément,
              │                                       indépendamment de L12)
              │ (L12 = cas particulier de L19 mais
              │  on le formalise d'abord comme calibrage)
              ▼
         L13 (Independent Set / Q_n)
              │
              │ (L13 = cas où f^{-1}(1) ⊆ Q_n est independent)
              ▼
         L19 (Essentialité — théorème-cadre)
              │
              ├─── L14 (Majority)        ┐
              ├─── L15 (Threshold_t)     │ Applications de L19 à
              ├─── L16 (Mod_p)           │ des familles spécifiques
              └─── L18 (Inner Product)   ┘

         L20 (Antipodal)
              │
              │ (Indépendant de L19 — pôle opposé)
              ▼
              (preuve directe en 4 sous-lemmes)
```

**Note importante** : L13 et L19 sont *en gros* indépendants l'un de
l'autre côté Lean, mais conceptuellement L19 généralise L13. L'ordre
recommandé est L12 → L13 → L19 → applications, car L13 sert de calibrage
pour les notions de graphe `Q_n` et independent set, et L19 réutilise les
notions « témoin essentiel » qui apparaissent naturellement dans L12 et
L13.

---

## 2. Ordre de formalisation recommandé

| Phase | Cible | Estimation |
|---|---|---|
| **0a** | Finaliser Basic.lean : `canonicalDNF` + son théorème (sorries actuels). | ~30 lignes, ~1h |
| **0b** | Premier `lake build` pour valider la base. | variable, ~5-30 min |
| **1** | **L12 (Parity)** — calibrage des techniques. | ~150-200 lignes |
| **2** | **L13 (Independent Set)** — généralisation de L12. | ~100-150 lignes |
| **3** | **L19 (Essentialité)** — théorème-cadre. | ~200-250 lignes |
| **4a** | **L14 (Majority)** — application de L19. | ~80-100 lignes |
| **4b** | **L15 (Threshold_t)** — généralise L14. | ~60 lignes (réutilise L14) |
| **4c** | **L16 (Mod_p)** — application de L19. | ~80 lignes |
| **4d** | **L18 (Inner Product)** — méthode plus dure (récurrence, classification). | ~250-300 lignes |
| **5** | **L20 (Antipodal)** — pôle opposé, indépendant. | ~150 lignes |

**Total estimé** : ~1500 lignes Lean, sur ~5-10 sessions Lean intensives.

---

## 3. Stratégie de validation par étapes

Après chaque phase, **valider mécaniquement** :

1. `lake build` doit passer sans erreur (sorries acceptables aux endroits
   identifiés).
2. **Aucun théorème final** ne doit dépendre d'un `sorry` (les `sorry`
   restent uniquement dans les sous-lemmes auxiliaires en cours).
3. Mettre à jour le tableau de suivi du `README.md` (☐ → ✅).

**Hygiène git** : un commit par phase, avec message indiquant clairement
le statut (ex. `feat(L12): parity formalisé sans sorry (sauf canonicalDNF)`).

---

## 4. Décisions techniques globales

Ces décisions s'appliquent à **tous** les fichiers de formalisation. Les
fixer dès maintenant évite des refactorisations coûteuses plus tard.

### 4.1 Représentation des monômes

`Monomial n := Fin n → Option Bool`.

* `m i = none` : variable `i` absente du monôme (libre).
* `m i = some true` : `i` apparaît positivement.
* `m i = some false` : `i` apparaît négativement.

*Alternative écartée pour l'instant* : `Finset (Fin n × Bool)` (ensemble
de littéraux). Avantage : plus proche de la représentation informelle.
Désavantage : nécessite de gérer les contradictions (`(i, true)` et
`(i, false)` simultanément) et de tracker l'unicité par variable. La
représentation `Fin n → Option Bool` est plus contrainte par
construction.

### 4.2 Représentation des DNF

`DNF n := List (Monomial n)`.

*Alternative écartée* : `Finset (Monomial n)`. Avantage : pas de
doublons. Désavantage : exige `DecidableEq (Monomial n)` (qui existe via
`Fintype` mais alourdit les preuves).

**Convention** : un DNF peut contenir des doublons (sa taille = `List.length`,
pas le cardinal unique). En pratique, les DNF minimaux n'ont pas de
doublons, donc cette convention ne pose pas de problème.

### 4.3 Définition de `dnfMin`

`noncomputable def dnfMin (f : BoolFun n) : ℕ := sInf {k | ∃ d, d.computes f ∧ d.size = k}`.

*Alternative à envisager si trop lourd* : `Nat.find ⟨...⟩` avec preuve
d'existence inline. À évaluer après L12.

### 4.4 Convention `parity`

`parity n x = 1` ssi nombre impair de bits à 1. Cohérent FSS 1981 / Tour
12 du parent.

*Définition recommandée* : `fold xor false` (cf. `L12_parity_architecture.md` §5.3).

### 4.5 Style

* **Noms** : `camelCase` pour les théorèmes (mathlib4), `PascalCase` pour
  les types.
* **Indentation** : 2 espaces.
* **Lignes** : ≤ 100 caractères.
* **Docstrings** : sur toutes les définitions et tous les théorèmes
  principaux (Mathlib convention).
* **Imports** : ciblés plutôt que `import Mathlib` global, pour éviter
  les temps de build excessifs.

### 4.6 Politique sur les `sorry`

* **Acceptable** : dans des sous-lemmes auxiliaires en cours de
  développement, *avec un commentaire indiquant ce qui doit être prouvé*.
* **Inacceptable** : dans les théorèmes finaux `Lxx`. Avant de pousser
  un commit étiqueté ✅, vérifier `lake build --warning sorry` pour
  s'assurer qu'aucun théorème principal ne contient `sorry`.

---

## 5. Liens entre les théorèmes (récapitulatif mathématique)

* **L12** : `dnfMin parity_n = 2^(n−1)`. Tous les implicants premiers
  sont des mintermes complets impairs. Cas particulier de L13 (parity =
  fonction où f^{-1}(1) est une classe de la bipartition de Q_n).

* **L13** : `dnfMin f = |f^{-1}(1)|` ⟺ `f^{-1}(1)` est independent set
  de `Q_n`. Caractérisation par voisinage Hamming-1.

* **L14** : `dnfMin majority_n = C(n, ⌈n/2⌉)`. Implicants premiers =
  monômes positifs de taille ⌈n/2⌉.

* **L15** : `dnfMin threshold_{t,n} = C(n, t)` pour tout `t ∈ [1, n]`.
  Généralise L14 (où `t = ⌈n/2⌉`).

* **L16** : `dnfMin mod_{p,n} = Σ_{k ≡ 0 mod p} C(n, k)` pour tout
  `p ≥ 2`. Cas particulier de L13 car `mod_p^{-1}(1)` est independent
  dans `Q_n` pour `p ≥ 2`.

* **L18** : `dnfMin IP_{2n} = (3^n − 1)/2`. **Hors classe L13** —
  preuve directe par classification des implicants premiers en 3
  classes + récurrence + non-redondance par construction explicite du
  témoin.

* **L19** : *théorème-cadre*. `dnfMin f = |primes(f)|` ⟺ chaque
  implicant premier admet un témoin essentiel. **Unifie L12, L13, L14,
  L15, L16, L18** comme cas particuliers.

* **L20** : *pôle opposé*. Pour `f_α(x) = 1 ⟺ x ∉ {α, ¬α}` (n ≥ 3) :
  `|primes| = n(n−1)`, `dnfMin = n`, défaut maximal `n(n−2)`.
  **Hors classe L19** (essentialité ne tient pas — beaucoup d'implicants
  premiers redondants). Indépendant de L19 mathématiquement.

---

## 6. Risques et alternatives stratégiques

### 6.1 Risque : Mathlib n'a pas de bornes inférieures DNF formalisées

C'est la motivation principale du projet (l'utilisateur l'a noté :
*« il n'y a pas de littérature scientifique à ce sujet à ma connaissance »*).
**Avantage** : terrain vierge, contribution potentielle. **Désavantage** :
on construit la fondation, ce qui ralentit.

### 6.2 Risque : choix de représentation sous-optimal

Si après quelques lemmes (par exemple L12.1 ou L13), la représentation
`Fin n → Option Bool` se révèle lourde, **on refactorise immédiatement
vers `Finset (Fin n × Bool)`**. Ne pas s'accrocher à un mauvais choix.
Mais refactoriser une seule fois — pas de yo-yo.

### 6.3 Risque : `sInf` pénible

Si la preuve `dnfMin f = k` via `sInf` devient pénible (lemmes
`Nat.sInf_eq_zero`, `Nat.sInf_mem`, `csInf_le`, etc.), **basculer sur
`Nat.find`** dès la version 2 de Basic.lean.

### 6.4 Alternative : viser uniquement L12 + L13 + L19 + L20 (4 théorèmes)

Si la formalisation s'avère plus lourde que prévue, on peut viser
seulement les **4 théorèmes-clés** :
- L12 (cas le plus simple, calibrage).
- L13 (caractérisation par independent set, premier théorème de classe).
- L19 (théorème-cadre).
- L20 (pôle opposé).

Et **laisser L14, L15, L16, L18** pour une seconde phase (ou une PR
mathlib ultérieure).

Cette stratégie « 4 piliers » donne déjà une **contribution majeure**
sans noyer le projet dans les applications.

---

## 7. Index des documents d'architecture

| Document | Statut |
|---|---|
| `architecture_global.md` (ce fichier) | ✅ rédigé |
| `L12_parity_architecture.md` | ✅ rédigé |
| `L13_independentset_architecture.md` | ☐ à rédiger |
| `L14_majority_architecture.md` | ☐ à rédiger |
| `L15_threshold_architecture.md` | ☐ à rédiger |
| `L16_modp_architecture.md` | ☐ à rédiger |
| `L18_innerproduct_architecture.md` | ☐ à rédiger |
| `L19_essentiality_architecture.md` | ☐ à rédiger |
| `L20_antipodal_architecture.md` | ☐ à rédiger |

**Politique** : avant de coder un théorème `Lxx`, rédiger son fichier
d'architecture (décomposition en lemmes, dépendances, obstacles
anticipés). Cela évite de coder à l'aveugle et permet d'identifier les
problèmes structurels avant qu'ils n'apparaissent dans les preuves Lean.

---

## 8. Prochaine étape

Architecture L12 rédigée (voir `L12_parity_architecture.md`).
**Action immédiate** : remplir les sorries de Basic.lean (`canonicalDNF`
et son théorème de correction), puis démarrer Parity.lean selon l'ordre
de §3 du fichier L12.

Avant de coder Parity.lean : `lake update && lake build` initial pour
valider que Basic.lean (avec canonicalDNF rempli) compile.

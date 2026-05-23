# pvsnp-LeanAC0Profondeur2

Formalisation Lean 4 de **7 théorèmes de borne inférieure sur AC⁰ profondeur 2**
(circuits DNF/CNF sans contrainte de fan-in), issus du projet d'exploration
adverse [Tanguy333/pvsnp-exploration](https://github.com/Tanguy333/pvsnp-exploration)
sur la question P vs NP.

## Contexte

Le repo parent a produit 7 théorèmes ✅ Établis structurellement après 19 tours
de boucle adverse Proposeur (LLM) / Réfuteur (Claude). Tous sont des résultats
classiques de logique booléenne (Quine 1952, McCluskey 1956, FSS 1981) qui
**n'apparaissent à ma connaissance dans aucune bibliothèque formelle** : trop
élémentaires pour faire l'objet d'un paper, mais trop techniques pour être
formalisés en passant.

Ce dépôt vise à combler ce trou, avec pour cible une PR mathlib4 si la qualité
le permet.

## Théorèmes ciblés

| ID | Énoncé | Statut Lean |
|---|---|---|
| L12 | `dnfMin parityₙ = 2^(n−1)` | ☐ à faire |
| L13 | `dnfMin f = |f⁻¹(1)|` ⟺ `f⁻¹(1)` est independent set de `Qₙ` | ☐ à faire |
| L14 | `dnfMin majorityₙ = C(n, ⌈n/2⌉)` | ☐ à faire |
| L15 | `dnfMin threshold_{t,n} = C(n, t)` | ☐ à faire |
| L16 | `dnfMin mod_{p,n} = Σ_{k ≡ 0 mod p} C(n, k)` | ☐ à faire |
| L18 | `dnfMin IP_{2n} = (3^n − 1)/2` | ☐ à faire |
| L19 | Caractérisation d'essentialité (théorème-cadre) | ☐ à faire |

À mettre à jour au fur et à mesure des preuves complétées.

## Stratégie

Voir [`CLAUDE.md`](CLAUDE.md) pour le détail de la stratégie de formalisation
(ordre bottom-up : L12 → L13 → L19 → L14, L15, L16, L18 comme applications de
L19).

## Structure prévue

```
pvsnp-LeanAC0Profondeur2/
├── CLAUDE.md
├── README.md
├── lean-toolchain          ← à créer (version Lean 4)
├── lakefile.toml           ← à créer (config Lake + dep mathlib4)
├── pvsnpLeanAC0Profondeur2/
│   ├── Basic.lean          ← définitions DNF, implicant, primeImplicant, dnfMin
│   ├── Parity.lean         ← L12
│   ├── IndependentSet.lean ← L13
│   ├── Essentiality.lean   ← L19 (théorème-cadre)
│   ├── Majority.lean       ← L14
│   ├── Threshold.lean      ← L15
│   ├── ModP.lean           ← L16
│   └── InnerProduct.lean   ← L18
└── tests/                  ← optionnel : tests de cohérence avec calculs Python du parent
```

## Lien au projet parent

Tous les théorèmes formalisés ici sont *prouvés mathématiquement* dans
`Tanguy333/pvsnp-exploration` (preuves combinatoires + vérification empirique
exhaustive à n=4). Cette formalisation Lean les **certifie mécaniquement**
mais n'apporte pas de nouveau résultat mathématique.

Si une erreur est découverte dans une preuve du parent au cours de la
formalisation, elle sera signalée dans une issue de ce dépôt mais le parent
ne sera pas modifié depuis ici.

## Licence

À décider avant la première PR publique (probablement Apache 2.0 pour être
compatible mathlib4).

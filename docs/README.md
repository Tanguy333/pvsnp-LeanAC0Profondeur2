# `docs/` — Documents d'architecture

Ce dossier contient les **plans de preuve avant code** pour chaque
théorème à formaliser. La politique du projet (cf. `CLAUDE.md` § 4) est
de **rédiger l'architecture avant de coder** pour éviter de naviguer à
vue dans les preuves Lean.

## Index

| Document | Contenu | Statut |
|---|---|---|
| [`architecture_global.md`](architecture_global.md) | Vue d'ensemble, graphe de dépendances, ordre de formalisation, décisions techniques globales. | ✅ |
| [`L12_parity_architecture.md`](L12_parity_architecture.md) | Architecture détaillée de la preuve de `dnfMin parity_n = 2^(n−1)`. | ✅ |
| `L13_independentset_architecture.md` | Caractérisation par independent set de `Q_n`. | ☐ |
| `L14_majority_architecture.md` | `dnfMin majority_n = C(n, ⌈n/2⌉)`. | ☐ |
| `L15_threshold_architecture.md` | Généralisation L14 à threshold_t. | ☐ |
| `L16_modp_architecture.md` | `mod_p` famille (application L13). | ☐ |
| `L18_innerproduct_architecture.md` | Inner Product hors classe L13, récurrence. | ☐ |
| `L19_essentiality_architecture.md` | Théorème-cadre d'essentialité. | ☐ |
| `L20_antipodal_architecture.md` | Pôle opposé : fonctions antipodales, défaut maximal. | ☐ |

## Workflow recommandé

Pour chaque nouveau théorème `Lxx` :

1. **Rédiger** `docs/Lxx_*_architecture.md` selon le canevas de
   `L12_parity_architecture.md` :
   - §1 Énoncé Lean cible.
   - §2 Décomposition en lemmes intermédiaires (avec énoncés Lean).
   - §3 Ordre de formalisation.
   - §4 Dépendances Mathlib anticipées.
   - §5 Obstacles techniques anticipés.
   - §6 Plan du fichier Lean.
   - §7 Décisions à figer.
   - §8 Risques et alternatives.

2. **Commit** l'architecture seule, sans code Lean.

3. **Coder** le fichier Lean (`pvsnpLeanAC0Profondeur2/Xxx.lean`), en
   suivant l'architecture pas à pas.

4. **`lake build`** itératif : un lemme à la fois, valider mécaniquement.

5. **Commit** le fichier Lean une fois tous les théorèmes principaux
   prouvés (sans `sorry` dans les théorèmes finaux).

6. **Mettre à jour** le tableau de suivi du `README.md` racine
   (☐ → ✅ pour le théorème).

Cette discipline **rend la formalisation traçable** et permet à plusieurs
sessions (potentiellement plusieurs personnes/instances LLM) de
collaborer sans dérive.

/-
Copyright (c) 2026 Tanguy Le Mer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanguy Le Mer

# pvsnp-LeanAC0Profondeur2 : module racine

Bornes inférieures DNF sur AC⁰ profondeur 2, issues de
[Tanguy333/pvsnp-exploration](https://github.com/Tanguy333/pvsnp-exploration).

Ce fichier importe toutes les sous-théories. Voir `README.md` pour le
catalogue des théorèmes ciblés (L12 à L20) et `CLAUDE.md` pour la
stratégie de formalisation.

## Structure

* `Basic` — définitions de base : `Literal`, `Monomial`, `DNF`, évaluations,
  `isImplicant`, `isPrimeImplicant`, `dnfMin`.

À étoffer au fur et à mesure des fichiers : `Parity` (L12), `Antipodal`
(L20), etc.
-/

import PvsnpLeanAC0Profondeur2.Basic

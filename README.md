# TAS-Semantique

Projet universitaire de travaux pratiques autour de l'analyse statique abstraite avec LiSA.

## Auteurs

- HALFAOUI Anis
- BOUAFIA Merouane

## Conformite Au Sujet TAS 2026

Sujet impose: implementer 1 domaine non relationnel + 1 domaine relationnel + leur produit cartesien.

Choix retenu pour le rendu officiel:

- Domaine non relationnel: Extended sign domain
  - Classe: src/main/java/it/unive/lisa/tutorial/ExtendedSigns.java
  - Difficulte annoncee: 2
- Domaine relationnel: Two variables per linear inequality
  - Classe: src/main/java/it/unive/lisa/tutorial/TwoVariablesInequality.java
  - Difficulte annoncee: 4
- Produit cartesien:
  - Classe: src/main/java/it/unive/lisa/tutorial/ExtendedSignsAndLinearInequalityCartesian.java

Somme des difficultes: 2 + 4 = 6 (borne demandee respectee)

## Livrables Demandes Et Correspondance

Correspondance avec les exigences du projet:

- Classes des 2 domaines:
  - src/main/java/it/unive/lisa/tutorial/ExtendedSigns.java
  - src/main/java/it/unive/lisa/tutorial/TwoVariablesInequality.java
- Classe du produit:
  - src/main/java/it/unive/lisa/tutorial/ExtendedSignsAndLinearInequalityCartesian.java
- 3 programmes IMP (domaine 1, domaine 2, produit):
  - inputs/extendedsigns.imp
  - inputs/twovariablesinequality.imp
  - inputs/extendedsignslinearinequalitycartesian.imp
- Tests des 2 domaines en isolation + produit:
  - src/test/java/it/unive/lisa/tutorial/ExtendedSignsTest.java
  - src/test/java/it/unive/lisa/tutorial/TwoVariablesInequalityTest.java
  - src/test/java/it/unive/lisa/tutorial/ExtendedSignsAndLinearInequalityCartesianTest.java
- README de description/resultats:
  - ce fichier

Les autres domaines presents dans ce depot servent de materiel complementaire et de comparaison, mais le perimetre du rendu TAS 2026 est celui ci-dessus.

## Repartition Du Travail

Repartition declaree des contributions (a affiner avec vos commits Git):

- HALFAOUI Anis
  - Domaine non relationnel ExtendedSigns
  - Programme IMP associe (extendedsigns.imp)
  - Test unitaire associe (ExtendedSignsTest)
- BOUAFIA Merouane
  - Domaine relationnel TwoVariablesInequality
  - Programme IMP associe (twovariablesinequality.imp)
  - Test unitaire associe (TwoVariablesInequalityTest)
- Travail conjoint
  - Produit cartesien ExtendedSigns x TwoVariablesInequality
  - Programme IMP du produit (extendedsignslinearinequalitycartesian.imp)
  - Test du produit (ExtendedSignsAndLinearInequalityCartesianTest)
  - Documentation README et validation finale

## Ce Que Nous Avons Implemente

Dans le cadre de ce projet, nous avons implementé les analyses suivantes:

- Domaine des signes simple (Signs)
- Domaine des signes etendu (ExtendedSigns)
- Domaine intervalle simple (Intervalles)
- Domaine intervalle complet avec satisfiabilite/assume/widening (Interval)
- Domaine valeur concrete (ConcreteValue)
- Domaine ensemble fini de valeurs entieres (SetOfIntegerValues)
- Domaine relationnel not-equals (NotEqualsDomain)
- Domaine relationnel strict upper bounds (StrictUpperBounds)
- Domaine combine Pentagons (reduction entre intervals et strict upper bounds)
- Domaine des inegalites lineaires a deux variables (TwoVariablesInequality)
- Produit cartesien ExtendedSigns x TwoVariablesInequality
- Analyse de taint (Taint) + verification semantique des sinks (TaintCheck)

Le depot implemente plusieurs domaines abstraits numeriques, relationnels et un cas de securite (taint), puis les execute sur des programmes IMP de demonstration.

## 1) Vue d'ensemble

Ce projet contient:

- des domaines non relationnels (signes, intervalles, valeur concrete, ensemble de valeurs, taint)
- des domaines relationnels (not-equals, strict upper bounds, pentagons, inequalities a 2 variables)
- un produit cartesien entre signes et inequalities lineaires
- une suite de tests JUnit qui lance LiSA sur chaque scenario IMP
- une generation de rapports HTML dans le dossier outputs/

Objectif pedagogique: comparer la precision, les hypotheses et les limites de plusieurs abstractions sur des mini-programmes IMP.

## 2) Stack Technique

- Langage: Java
- Build: Gradle Wrapper
- Analyse statique: LiSA 0.1
- Tests: JUnit 4.12

Dependances (build.gradle):

- io.github.lisa-analyzer:lisa-sdk:0.1
- io.github.lisa-analyzer:lisa-analyses:0.1
- io.github.lisa-analyzer:lisa-imp:0.1

## 3) Prerequis

- JDK installe (le projet a ete execute localement avec JVM 24.0.1)
- Acces internet au premier lancement du wrapper Gradle (telechargement de Gradle et dependances)

## 4) Installation Et Lancement

Depuis la racine du projet:

Windows:

```bat
gradlew.bat test
```

Linux/macOS:

```bash
./gradlew test
```

Resultat attendu:

- compilation OK
- tests OK
- rapports d'analyse generes dans outputs/

## 5) Cartographie Complete Du Projet

### 5.1 Domaines non relationnels

1. Signs (src/main/java/it/unive/lisa/tutorial/Signs.java)
- Domaine a 5 elements: bottom, negative, zero, positive, top.
- Supporte +, -, *, / et negation.
- LUB des incomparables -> top.

2. ExtendedSigns (src/main/java/it/unive/lisa/tutorial/ExtendedSigns.java)
- Variante plus fine des signes: <0, <=0, 0, >0, >=0, !=0, top, bottom.
- Supporte evaluation constante, unaire, binaire, et un assume partiel sur <=.
- Utilise dans le produit cartesien avec TwoVariablesInequality.

3. Intervalles (src/main/java/it/unive/lisa/tutorial/Intervalles.java)
- Implementation simple d'intervalles entiers [min..max].
- Fournit top/bottom, lub, lessOrEqual.

4. Interval (src/main/java/it/unive/lisa/tutorial/Interval.java)
- Domaine intervalle plus complet base sur IntInterval/MathNumber de LiSA.
- Fournit lub/glb/widening, arithmetique, satisfiability, assume sur comparaisons.

5. ConcreteValue (src/main/java/it/unive/lisa/tutorial/ConcreteValue.java)
- Domaine concret single-value (exact tant qu'il n'y a pas perte d'info).
- LUB donne top si les valeurs different.

6. SetOfIntegerValues (src/main/java/it/unive/lisa/tutorial/SetOfIntegerValues.java)
- Domaine fini d'ensembles de valeurs entieres possibles.
- Addition produit cartesian des ensembles.
- Cap limite par MAX_NUMBER_OF_ELEMENTS (500), sinon top.

7. Taint (src/main/java/it/unive/lisa/tutorial/Taint.java)
- Domaine tri-valued: tainted, clean, bottom.
- Propagation sur expressions via lub.
- Respecte annotations sources/sanitizers.

### 5.2 Domaines relationnels

8. NotEqualsDomain (src/main/java/it/unive/lisa/tutorial/NotEqualsDomain.java)
- Lattice fonctionnel identifiant -> ensemble d'identifiants differents.
- Supporte assign/assume sur certains motifs (notamment ! (x == y)).
- Fermeture symetrique avec close().

9. StrictUpperBounds (src/main/java/it/unive/lisa/tutorial/StrictUpperBounds.java)
- Analyse relationnelle d'upper bounds strictes (x < y).
- Basee sur une variante InverseSetLattice.
- Gere assume/satisfies pour comparaisons entre variables.

10. Pentagons (src/main/java/it/unive/lisa/tutorial/Pentagons.java)
- Reduction entre:
  - StrictUpperBounds (relations)
  - Interval (bornes numeriques)
- combine les deux pour une meilleure precision (article Pentagons).

11. TwoVariablesInequality (src/main/java/it/unive/lisa/tutorial/TwoVariablesInequality.java)
- Domaine de contraintes lineaires de forme a*x + b*y <= c.
- Supporte assign et assume pour motifs cibles.
- Inclut closure/transitivity + gestion de redondance (lub/glb sur constantes).

### 5.3 Produit

12. ExtendedSignsAndLinearInequalityCartesian (src/main/java/it/unive/lisa/tutorial/ExtendedSignsAndLinearInequalityCartesian.java)
- Produit cartesien:
  - composante gauche: TwoVariablesInequality
  - composante droite: ValueEnvironment<ExtendedSigns>

### 5.4 Check semantique

13. TaintCheck (src/main/java/it/unive/lisa/tutorial/TaintCheck.java)
- Passe post-analyse qui detecte les flux vers parametres [lisa.taint.Sink].
- Lit les resultats analyses pour remonter des warnings interpretables.

## 6) Scenarios IMP Et Tests Associes

Chaque test lance LiSA sur un fichier dans inputs/ et ecrit le resultat dans outputs/.

| Test JUnit | Input IMP | Workdir outputs |
|---|---|---|
| SignsTest | inputs/signs.imp | outputs/sign |
| ExtendedSignsTest | inputs/extendedsigns.imp | outputs/extendedsigns |
| IntervalTest | inputs/signs.imp | outputs/interval |
| IntervallesTest | inputs/intervalles.imp | outputs/intervalles |
| ConcreteValueTest | inputs/concretevalue.imp | outputs/concretevalue |
| SetOfIntegerValuesTest | inputs/setofintegervalues.imp | outputs/setofintegervalues |
| NotEqualsTest | inputs/notequals.imp | outputs/notequals |
| StrictUpperBoundsTest | inputs/upperbounds.imp | outputs/strictupperbounds |
| PentagonsTest | inputs/pentagons.imp | outputs/penta |
| TwoVariablesInequalityTest | inputs/twovariablesinequality.imp | outputs/twovariablesinequality |
| ExtendedSignsAndLinearInequalityCartesianTest | inputs/extendedsignslinearinequalitycartesian.imp | outputs/extendedsignslinearinequalitycartesian |
| TaintTest | inputs/taint.imp | outputs/taint |

## 7) Etat Actuel Observe (Audit Technique)

L'execution globale des tests a ete relancee sur cette base de code.

- Build Gradle: SUCCESS
- Tests: SUCCESS
- TaintTest produit 2 warnings attendus (directFlow et branch)

Points forts:

- Bonne couverture pedagogique: plusieurs familles de domaines dans un meme depot.
- Pipeline LiSA clair et reproductible via JUnit.
- Cas taint complet (source/sanitizer/sink + semantic check dedie).

Limites actuelles (etat du code, pas du concept):

- Certains domaines sont partiellement implementes:
  - ExtendedSigns.lessOrEqualAux retourne toujours false.
  - TwoVariablesInequality.lessOrEqual retourne false.
  - TwoVariablesInequality.forgetIdentifier et close sont no-op.
  - NotEqualsDomain.satisfies reste UNKNOWN.
- Presence de traces System.out/System.err dans certaines analyses (debug brut).
- Deux implementations proches d'intervalles coexistent (Intervalles et Interval).

Ces limites n'empechent pas les executions, mais elles impactent la precision semantique ou la completion du domaine.

## 8) Organisation Du Depot

```text
.
|- src/main/java/it/unive/lisa/tutorial/
|  |- Domaines abstraits et checks
|- src/test/java/it/unive/lisa/tutorial/
|  |- Tests d'execution LiSA
|- inputs/
|  |- Programmes IMP de demonstration
|- outputs/
|  |- Rapports analyses (generes)
|- build.gradle
|- gradlew / gradlew.bat
|- LICENSE
```

## 9) Commandes Utiles

Executer toute la suite:

```bat
gradlew.bat test
```

Executer un seul test:

```bat
gradlew.bat test --tests it.unive.lisa.tutorial.TaintTest
```

Nettoyer puis relancer:

```bat
gradlew.bat clean test
```

## 10) Pistes D'amelioration

1. Completer lessOrEqual/satisfies/forget pour les domaines partiels.
2. Remplacer les prints de debug par un logging structure.
3. Ajouter des assertions automatiques sur les resultats analyses (pas seulement execution).
4. Factoriser la configuration commune des tests pour reduire la duplication.
5. Documenter les invariants mathematiques de closure/transitivity dans TwoVariablesInequality.

## 11) Credits Et Licence

- Projet base sur LiSA (Library for Static Analysis)
- Licence du depot: MIT (voir LICENSE)


# Articles de mathématiques

Notes et fiches de niveau agrégation externe de mathématiques, rangées par leçon d'oral. Chaque dossier `lecons/<numéro>-<intitulé>/` contient les documents rattachés à cette leçon : articles, exercices commentés, développements, et éventuellement une formalisation Lean 4.

La numérotation suit la liste des leçons de l'agrégation externe. Cette liste est publiée chaque année et peut changer : vérifiez les numéros sur la liste de la session préparée.

Ces fiches servent de matériau pour écrire les plans de leçon et préparer les développements. Elles ne remplacent pas les plans.

## Index par leçon

| Leçon | Intitulé | Documents | Sert aussi pour |
|---|---|---|---|
| 126 | Exemples d'équations en arithmétique | [entiers-quadratiques.tex](lecons/126-equations-arithmetique/entiers-quadratiques.tex) | 102, 122, 191 |
| 142 | PGCD et PPCM, algorithmes de calcul. Applications | [divisibilite-pgcd-congruences.tex](lecons/142-pgcd-ppcm/divisibilite-pgcd-congruences.tex) | 120, 121, 126 |
| 221 | Équations différentielles linéaires. Systèmes d'équations différentielles linéaires. Exemples et applications | [crochet-lie-edo.tex](lecons/221-equations-differentielles-lineaires/crochet-lie-edo.tex), [CrochetLieEDO.lean](lecons/221-equations-differentielles-lineaires/CrochetLieEDO.lean) | 156, 220 |
| 224 | Exemples de développements asymptotiques de suites et de fonctions | [autour-de-e.tex](lecons/224-developpements-asymptotiques/autour-de-e.tex) | 218, 223, 229, 230 |
| 228 | Continuité, dérivabilité des fonctions réelles d'une variable réelle | [partie-entiere-regularite.tex](lecons/228-continuite-derivabilite/partie-entiere-regularite.tex) | 229 |
| 236 | Illustrer par des exemples quelques méthodes de calcul d'intégrales | [calcul-integral.tex](lecons/236-calcul-integrales/calcul-integral.tex) | 218, 230, 235, 239, 246 |

## Site web

`npm run render` transforme chaque `.tex` en vue de lecture HTML dans `dist/`, avec l'index des leçons. C'est le moteur de grothendieck-project (`scripts/render.mjs`), adapté aux articles : feuille de style ar5iv, formules composées par KaTeX dans le navigateur avec les macros du préambule, théorèmes numérotés, renvois, table des matières et bibliographie.

Le moteur ne couvre qu'un **sous-ensemble** de LaTeX, volontairement. Un environnement ou une commande hors de ce sous-ensemble, un renvoi sans étiquette ou une formule que KaTeX refuse font échouer le rendu, avec le fichier et le passage en cause. On corrige alors le `.tex`, ou on étend le moteur.

```bash
npm install
```

```bash
npm run dev
```

`npm run dev` construit le site, le sert sur http://localhost:4173 et le reconstruit à chaque modification. `npm run pdf` compile les PDF avec [Tectonic](https://tectonic-typesetting.github.io) quand il est installé. Lancez-le avant `npm run render` pour que les pages pointent vers les PDF.

### Figures

Les figures sont écrites en TikZ dans les `.tex`, avec les réglages communs de `lecons/figures/tikz-setup.tex`. `npm run tikz` compile chacune en SVG (Tectonic et pdftocairo), dans `lecons/figures/`, sous un nom tiré d'une empreinte de sa source. Ces SVG sont versionnés : le site se construit sans TeX, et une figure modifiée sans `npm run tikz` fait échouer le rendu.

### Commenter un passage

Sur chaque vue de lecture, sélectionner un passage fait apparaître « Commenter ». Le commentaire peut rester comme note dans le navigateur, ou devenir une issue GitHub pré-remplie : le passage cité (formules en TeX), le lien vers l'endroit exact, le fichier source et le commentaire. Rien n'est publié tant que le lecteur ne valide pas l'issue sur GitHub.

## Lean

Le dossier `lean/` est un projet Lake qui ne fournit que Mathlib. Lean et Mathlib y ont les mêmes versions que dans grothendieck-project, figées par `lean/lake-manifest.json`. Les fichiers `.lean` restent rangés avec leur document, dans `lecons/<leçon>/`.

```bash
cd lean && lake exe cache get && ./check.sh
```

`check.sh` vérifie chaque fichier avec `lake env lean`. Les avertissements y sont traités comme des erreurs, et `sorry`, `native_decide` et `axiom` sont refusés.

## Intégration continue

| Workflow | Déclenchement | Rôle |
|---|---|---|
| `site.yml` | chaque push et chaque pull request sur `main` | Compile les PDF, rend les vues de lecture (échoue sur un document refusé), publie sur GitHub Pages depuis `main` |
| `latex.yml` | modification d'un `.tex` | Compile chaque document avec Tectonic (échoue si l'un ne compile pas) et garde les PDF 30 jours comme artefact |
| `lean.yml` | modification d'un `.lean` ou de `lean/` | Vérifie les formalisations contre Mathlib |

Le site est publié comme site de projet, à l'adresse `https://<utilisateur>.github.io/<dépôt>/` ; tous les liens sont relatifs. Pour un domaine personnalisé, ajoutez un fichier `public/CNAME`.

## Origine des fiches

Les fiches 126, 142, 224, 228 et 236 sont des réécritures, au niveau agrégation, de feuilles d’exercices de terminale S (2003), tirées des manuels *Hyperbole*, *Bréal*, *Terracher* et *Method'S*. Les énoncés faux de ces feuilles y sont signalés et corrigés.

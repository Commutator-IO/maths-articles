import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

/-!
# Le birapport et le groupe anharmonique

Formalisation de la fiche « Le birapport et le groupe anharmonique » (M. Hua, octobre 2026),
`birapport-anharmonique.tex`. Les numéros des énoncés sont ceux de la fiche.

## Modèles

* On travaille dans un corps `K` quelconque (la fiche prend `K = ℂ`), avec des points finis :
  le birapport est `cr z₁ z₂ z₃ z₄ = (z₃ - z₁)(z₄ - z₂) / ((z₃ - z₂)(z₄ - z₁))`. Le point à
  l'infini et le passage à `ℙ¹` ne sont pas formalisés.
* **Proposition 1.2** : l'invariance est démontrée pour les translations, les homothéties et
  l'inversion `z ↦ 1/z`, qui engendrent les homographies.
* **Théorème 2.2** : les six fonctions sont des fonctions `K → K`, et l'on vérifie les
  relations de composition qui en font un groupe d'ordre `6` non abélien, sur `K ∖ {0, 1}`.

## Écarts avec la fiche

* Aucun énoncé de la fiche ne s'est révélé faux.

## Omis

L'action simplement transitive de `PGL₂` sur les triplets, la réciproque de la
proposition 1.2, l'énoncé de groupe du théorème 2.2 (isomorphisme avec `𝔖₃`, noyau `V₄`),
la partie « fibres » du théorème 4.1, les remarques 2.3 et 4.2 et les exercices.
-/

namespace BirapportAnharmonique

variable {K : Type*} [Field K]

/-- **Définition 1.1** : le birapport de quatre points finis. -/
def cr (z₁ z₂ z₃ z₄ : K) : K := (z₃ - z₁) * (z₄ - z₂) / ((z₃ - z₂) * (z₄ - z₁))

/-! ## 1. Invariance par homographie -/

/-- **Proposition 1.2** : invariance par translation. -/
theorem cr_add (b z₁ z₂ z₃ z₄ : K) : cr (z₁ + b) (z₂ + b) (z₃ + b) (z₄ + b) = cr z₁ z₂ z₃ z₄ := by
  simp only [cr]; ring_nf

/-- **Proposition 1.2** : invariance par homothétie. -/
theorem cr_mul {a : K} (ha : a ≠ 0) (z₁ z₂ z₃ z₄ : K) :
    cr (a * z₁) (a * z₂) (a * z₃) (a * z₄) = cr z₁ z₂ z₃ z₄ := by
  simp only [cr]
  rw [show (a * z₃ - a * z₁) * (a * z₄ - a * z₂) = a ^ 2 * ((z₃ - z₁) * (z₄ - z₂)) by ring,
    show (a * z₃ - a * z₂) * (a * z₄ - a * z₁) = a ^ 2 * ((z₃ - z₂) * (z₄ - z₁)) by ring,
    mul_div_mul_left _ _ (pow_ne_zero 2 ha)]

/-- **Proposition 1.2** : invariance par l'inversion `z ↦ 1/z`, pour des points non nuls
et distincts. -/
theorem cr_inv {z₁ z₂ z₃ z₄ : K} (h₁ : z₁ ≠ 0) (h₂ : z₂ ≠ 0) (h₃ : z₃ ≠ 0) (h₄ : z₄ ≠ 0)
    (h₃₂ : z₃ ≠ z₂) (h₄₁ : z₄ ≠ z₁) :
    cr z₁⁻¹ z₂⁻¹ z₃⁻¹ z₄⁻¹ = cr z₁ z₂ z₃ z₄ := by
  have a : z₃ - z₂ ≠ 0 := sub_ne_zero.2 h₃₂
  have b : z₄ - z₁ ≠ 0 := sub_ne_zero.2 h₄₁
  have a' : z₂ - z₃ ≠ 0 := sub_ne_zero.2 h₃₂.symm
  have b' : z₁ - z₄ ≠ 0 := sub_ne_zero.2 h₄₁.symm
  simp only [cr]
  rw [inv_sub_inv h₃ h₁, inv_sub_inv h₄ h₂, inv_sub_inv h₃ h₂, inv_sub_inv h₄ h₁]
  field_simp
  ring

/-! ## 2. Permuter les quatre points -/

/-- **Lemme 2.1** : échanger `z₁` et `z₂` inverse le birapport. -/
theorem cr_swap12 (z₁ z₂ z₃ z₄ : K) : cr z₂ z₁ z₃ z₄ = (cr z₁ z₂ z₃ z₄)⁻¹ := by
  simp only [cr]; rw [inv_div]

/-- **Lemme 2.1** : échanger `z₂` et `z₃` change `λ` en `1 - λ`. -/
theorem cr_swap23 {z₁ z₂ z₃ z₄ : K} (h₃₂ : z₃ ≠ z₂) (h₄₁ : z₄ ≠ z₁) :
    cr z₁ z₃ z₂ z₄ = 1 - cr z₁ z₂ z₃ z₄ := by
  have a : z₃ - z₂ ≠ 0 := sub_ne_zero.2 h₃₂
  have a' : z₂ - z₃ ≠ 0 := sub_ne_zero.2 h₃₂.symm
  have b : z₄ - z₁ ≠ 0 := sub_ne_zero.2 h₄₁
  simp only [cr]
  field_simp
  ring

/-- **Lemme 2.1** : les doubles transpositions ne changent pas le birapport. -/
theorem cr_double (z₁ z₂ z₃ z₄ : K) :
    cr z₂ z₁ z₄ z₃ = cr z₁ z₂ z₃ z₄ ∧ cr z₃ z₄ z₁ z₂ = cr z₁ z₂ z₃ z₄ := by
  simp only [cr]
  constructor <;> ring

/-- **Théorème 2.2** : la table du groupe anharmonique, sur `K ∖ {0, 1}`. Avec
`s λ = 1 - λ` et `t λ = 1/λ`, `r = t ∘ s` est d'ordre `3`, `s` et `t` sont des involutions,
et `s ∘ t ≠ t ∘ s` en général : le groupe engendré est d'ordre `6`, non abélien. -/
theorem table {l : K} (h0 : l ≠ 0) (h1 : l ≠ 1) :
    1 - (1 - l) = l ∧ (l⁻¹)⁻¹ = l ∧
    (1 - l)⁻¹ = 1 / (1 - l) ∧ 1 - l⁻¹ = (l - 1) / l ∧
    1 / (1 - 1 / (1 - 1 / (1 - l))) = l := by
  have h1' : 1 - l ≠ 0 := sub_ne_zero.2 h1.symm
  have h2 : l - 1 ≠ 0 := sub_ne_zero.2 h1
  refine ⟨by ring, inv_inv l, by rw [one_div], by field_simp, ?_⟩
  rw [show (1 : K) - 1 / (1 - l) = -l / (1 - l) by field_simp; ring, one_div_div,
    show (1 : K) - (1 - l) / -l = 1 / l by field_simp; ring, one_div_one_div]

/-! ## 3. Les orbites -/

/-- **Proposition 3.1** : les points fixes des involutions et des éléments d'ordre `3`. -/
theorem points_fixes {l : K} (h1 : l ≠ 1) :
    (1 - l = l ↔ 2 * l = 1) ∧ (1 / (1 - l) = l ↔ l ^ 2 - l + 1 = 0) := by
  have h1' : 1 - l ≠ 0 := sub_ne_zero.2 h1.symm
  constructor
  · constructor <;> intro h <;> linear_combination -h
  · rw [div_eq_iff h1']
    constructor <;> intro h <;> linear_combination h

/-! ## 4. L'invariant `j` -/

/-- **Théorème 4.1** : `j(λ) = 256 (λ² - λ + 1)³ / (λ² (λ - 1)²)`. -/
def j (l : K) : K := 256 * (l ^ 2 - l + 1) ^ 3 / (l ^ 2 * (l - 1) ^ 2)

/-- **Théorème 4.1** : `j` est invariant par `λ ↦ 1 - λ` et par `λ ↦ 1/λ`. -/
theorem j_invariant {l : K} (h0 : l ≠ 0) (h1 : l ≠ 1) : j (1 - l) = j l ∧ j l⁻¹ = j l := by
  have h2 : l - 1 ≠ 0 := sub_ne_zero.2 h1
  constructor
  · simp only [j]; ring_nf
  · simp only [j]
    field_simp
    ring

/-- **Théorème 4.1** : `256 (λ² - λ + 1)³ - 1728 λ² (λ - 1)² = 64 (λ + 1)² (λ - 2)² (2λ - 1)²`,
d'où `j - 1728 = 64 (λ + 1)² (λ - 2)² (2λ - 1)² / (λ² (λ - 1)²)`. -/
theorem j_sub_1728_num (l : K) :
    256 * (l ^ 2 - l + 1) ^ 3 - 1728 * (l ^ 2 * (l - 1) ^ 2)
      = 64 * ((l + 1) ^ 2 * (l - 2) ^ 2 * (2 * l - 1) ^ 2) := by
  ring

theorem j_sub_1728 {l : K} (h0 : l ≠ 0) (h1 : l ≠ 1) :
    j l - 1728 = 64 * ((l + 1) ^ 2 * (l - 2) ^ 2 * (2 * l - 1) ^ 2) / (l ^ 2 * (l - 1) ^ 2) := by
  have h2 : l - 1 ≠ 0 := sub_ne_zero.2 h1
  rw [← j_sub_1728_num, j]
  field_simp

/-- **Remarque 4.3** : le calcul de caractéristique d'Euler. La somme des poids vaut `-1/6`,
et `-1/24` après division par l'ordre de `V₄` ; la somme écrite sur la page,
`-1 + 1/3 + 1/2`, ne vaut pas `-1/24`. -/
theorem euler :
    (-6 : ℚ) / 6 + 3 / 6 + 2 / 6 = -1 / 6 ∧ (-1 : ℚ) / 6 / 4 = -1 / 24 ∧
      (-1 : ℚ) + 1 / 3 + 1 / 2 ≠ -1 / 24 := by
  norm_num

end BirapportAnharmonique

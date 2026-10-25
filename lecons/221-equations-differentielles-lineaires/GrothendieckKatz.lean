import Mathlib

/-!
# La $p$-courbure, et la conjecture de Grothendieck–Katz dans deux cas simples

Formalisation de la section 8 de la note « Crochet de Lie et équations différentielles
linéaires » (M. Hua, octobre 2026), fichier `crochet-lie-edo.tex` du même dossier.

## Modèles

* **Dérivations en caractéristique `p`** (lemme 8.1). Un anneau commutatif `R` avec `CharP R p`,
  et une dérivation `D : Derivation ℤ R R`, vue comme application `R → R` que l'on itère.
* **Le crochet en caractéristique `p`** (lemme 8.2). Un anneau quelconque `A` avec `CharP A p` ;
  `ad X` est l'application `Y ↦ X * Y - Y * X`.
* **Coefficients constants** (proposition 8.8, théorème 8.11). Deux éléments qui commutent dans
  un anneau de caractéristique `p` (typiquement `Module.End`), et des matrices à coefficients
  entiers réduites modulo `p` par `Matrix.map` et `Int.castRingHom (ZMod p)`. Les matrices de
  la note sont rationnelles ; on se ramène aux entiers en multipliant par un dénominateur
  commun, ce qui ne change ni la nilpotence ni la nullité de `A^p` modulo presque tout `p`.
* **Formule de Jacobson en rang 1** (proposition 8.12). L'opérateur `L y = D y + b * y` sur `R`,
  itéré. La note démontre l'identité par les partitions d'ensembles et la rotation. Ici, on suit
  une autre preuve, plus commode à formaliser : on introduit un paramètre `t`, l'opérateur
  `L_t = D + t b`, et on dérive `L_t^p (1)` par rapport à `t`. Le crochet `[∂_t, L_t] = b` et le
  lemme 8.2 donnent une dérivée constante, égale à `D^{p-1} b`, d'où la formule.
* **L'exponentielle n'est pas algébrique** (lemme 8.10), dans le cas d'un `λ` réel.

## Écarts avec la note

(À compléter au fil de la formalisation.)

## Omis

Le théorème de descente de Cartier (admis dans la note), le calcul de `Ψ` sur les éléments
simples à pôles (lemme 8.13, qui demanderait la dérivation des fractions rationnelles sur
`ZMod p`), et le théorème 8.14 lui-même ; la conjecture générale.
-/

open Polynomial

noncomputable section

namespace GrothendieckKatz

/-! ## 8.1. Dériver modulo `p` -/

section Derivations

variable {R : Type*} [CommRing R]

/-- **Lemme 8.1 (1)**, formule de Leibniz : `Dⁿ(fg) = ∑ C(n,k) Dᵏf · Dⁿ⁻ᵏg`. -/
theorem iterate_leibniz (D : Derivation ℤ R R) (n : ℕ) (f g : R) :
    (⇑D)^[n] (f * g) =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : R) * ((⇑D)^[k] f * (⇑D)^[n - k] g) := by
  sorry

variable (p : ℕ) [hp : Fact p.Prime] [CharP R p]

/-- **Lemme 8.1 (2)** : en caractéristique `p`, `Dᵖ` est encore une dérivation. -/
theorem iterate_char_leibniz (D : Derivation ℤ R R) (f g : R) :
    (⇑D)^[p] (f * g) = f * (⇑D)^[p] g + g * (⇑D)^[p] f := by
  sorry

end Derivations

/-- **Lemme 8.1 (3)**, sur les polynômes : la dérivée `p`-ième est nulle sur `𝔽_p[x]`. -/
theorem iterate_derivative_char_eq_zero (p : ℕ) [Fact p.Prime] (f : (ZMod p)[X]) :
    derivative^[p] f = 0 := by
  sorry

/-! ## Le crochet en caractéristique `p` -/

section Bracket

variable {A : Type*} [Ring A] (p : ℕ) [Fact p.Prime] [CharP A p]

/-- `ad X : Y ↦ XY − YX`. -/
def ad (X : A) : A → A := fun Y => X * Y - Y * X

/-- **Lemme 8.2** : `ad_Xᵖ (Y) = [Xᵖ, Y]` en caractéristique `p`. -/
theorem ad_iterate_char (X Y : A) : (ad X)^[p] Y = X ^ p * Y - Y * X ^ p := by
  sorry

/-- **Proposition 8.4**, forme abstraite : si `ad_∇ᵖ (M) = 0`, alors `∇ᵖ` commute avec `M`. C'est
l'argument qui rend la `p`-courbure linéaire (avec `ad_∇ (M_f) = M_{f'}` et `Dᵖ f = 0`). -/
theorem commute_pow_of_ad_iterate_eq_zero (X Y : A) (h : (ad X)^[p] Y = 0) :
    Commute (X ^ p) Y := by
  sorry

/-- **Proposition 8.8** : si `D` et `A` commutent, `(D − A)ᵖ = Dᵖ − Aᵖ` en caractéristique `p`.
Avec `Dᵖ = 0`, la `p`-courbure d'un système à coefficients constants est `−Aᵖ`. -/
theorem sub_pow_of_commute (D M : A) (h : Commute D M) : (D - M) ^ p = D ^ p - M ^ p := by
  sorry

end Bracket

/-! ## 8.3. Coefficients constants -/

section Constant

variable {n : ℕ}

/-- La réduction modulo `p` d'une matrice à coefficients entiers. -/
abbrev red (p : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) (ZMod p) :=
  A.map (Int.castRingHom (ZMod p))

/-- **Théorème 8.11, 2 ⇒ 3** : si `A` est nilpotente, `(A mod p)ᵖ = 0` pour tout `p ≥ n`. -/
theorem red_pow_eq_zero_of_isNilpotent (A : Matrix (Fin n) (Fin n) ℤ) (hA : IsNilpotent A)
    (p : ℕ) (hp : n ≤ p) : red p A ^ p = 0 := by
  sorry

/-- **Théorème 8.11, 4 ⇒ 2** : si `(A mod p)ᵖ = 0` pour une infinité de nombres premiers `p`,
alors `A` est nilpotente. Preuve de la note : le polynôme caractéristique de `A mod p` est `tⁿ`,
c'est la réduction de celui de `A`, dont les coefficients non dominants sont donc divisibles par
une infinité de nombres premiers, donc nuls ; puis Cayley–Hamilton. -/
theorem isNilpotent_of_frequently (A : Matrix (Fin n) (Fin n) ℤ)
    (h : ∀ N : ℕ, ∃ p, N < p ∧ p.Prime ∧ red p A ^ p = 0) : IsNilpotent A := by
  sorry

/-- **Théorème 8.11, 2 ⇔ 4** : nilpotence et annulation de `(A mod p)ᵖ` pour une infinité
de `p`. -/
theorem isNilpotent_iff_frequently (A : Matrix (Fin n) (Fin n) ℤ) :
    IsNilpotent A ↔ ∀ N : ℕ, ∃ p, N < p ∧ p.Prime ∧ red p A ^ p = 0 := by
  sorry

/-- **Exemple 8.9** : pour `y' = y`, `A = (1)` et `(A mod p)ᵖ = 1 ≠ 0` pour tout `p` premier. -/
theorem exp_pCurvature_ne_zero (p : ℕ) [Fact p.Prime] :
    red p (1 : Matrix (Fin 1) (Fin 1) ℤ) ^ p ≠ 0 := by
  sorry

/-- **Exercice 6** : pour `y'' + y = 0`, `A = [[0,1],[-1,0]]` vérifie `A² = −1`, donc `Aᵖ = ± A`
n'est jamais nul modulo un premier impair. -/
theorem rotation_pCurvature_ne_zero (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    red p !![0, 1; -1, 0] ^ p ≠ 0 := by
  sorry

end Constant

/-- **Lemme 8.10**, cas réel : pour `λ ≠ 0`, si `∑ₖ cₖ(x) e^{kλx} = 0` pour tout `x` réel, avec des
polynômes `cₖ`, alors tous les `cₖ` sont nuls. Autrement dit, `e^{λx}` n'est pas algébrique sur
`ℝ(x)`. -/
theorem exp_not_algebraic {l : ℝ} (hl : l ≠ 0) (d : ℕ) (c : ℕ → ℝ[X])
    (h : ∀ x : ℝ, ∑ k ∈ Finset.range (d + 1), (c k).eval x * Real.exp (k * l * x) = 0) :
    ∀ k ≤ d, c k = 0 := by
  sorry

/-! ## 8.4. L'ordre 1 : la formule de Jacobson -/

section Jacobson

variable {R : Type*} [CommRing R] (D : Derivation ℤ R R) (b : R)

/-- L'opérateur `L y = D y + b y`, celui de l'équation `y' = −b y`. -/
def L (y : R) : R := D y + b * y

/-- `uₘ = Lᵐ(1)`. -/
def u (m : ℕ) : R := (L D b)^[m] 1

/-- **Proposition 8.12, étape 1** : `Lⁿ(y) = ∑ C(n,k) u_{n−k} Dᵏ y`. -/
theorem L_iterate (n : ℕ) (y : R) :
    (L D b)^[n] y =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : R) * u D b (n - k) * (⇑D)^[k] y := by
  sorry

variable (p : ℕ) [Fact p.Prime] [CharP R p]

/-- **Proposition 8.12, étape 1 en caractéristique `p`** : `Lᵖ(y) = u_p · y + Dᵖ y`. -/
theorem L_iterate_char (y : R) : (L D b)^[p] y = u D b p * y + (⇑D)^[p] y := by
  sorry

/-- **Proposition 8.12** (formule de Jacobson en rang 1) : `u_p = bᵖ + D^{p−1} b`. -/
theorem u_char : u D b p = b ^ p + (⇑D)^[p - 1] b := by
  sorry

/-- **Proposition 8.12**, forme opératorielle : `(D + b)ᵖ = Dᵖ + (bᵖ + D^{p−1} b)`. -/
theorem jacobson (y : R) :
    (L D b)^[p] y = (⇑D)^[p] y + (b ^ p + (⇑D)^[p - 1] b) * y := by
  sorry

/-- **Additivité de `Ψ`** (utilisée pour les théorèmes 8.14) : `Ψ(b) = bᵖ + D^{p−1} b` est
additive en caractéristique `p`. -/
theorem psi_add (b c : R) :
    (b + c) ^ p + (⇑D)^[p - 1] (b + c) = (b ^ p + (⇑D)^[p - 1] b) + (c ^ p + (⇑D)^[p - 1] c) := by
  sorry

end Jacobson

/-- **Lemme 8.13**, partie polynomiale : sur `𝔽_p[x]`, `Ψ(α xⁿ) = α x^{np}` pour `n ≤ p − 2`. -/
theorem psi_monomial (p : ℕ) [Fact p.Prime] (α : ZMod p) (n : ℕ) (hn : n + 2 ≤ p) :
    (C α * X ^ n) ^ p + derivative^[p - 1] (C α * X ^ n) = C α * X ^ (n * p) := by
  sorry

end GrothendieckKatz

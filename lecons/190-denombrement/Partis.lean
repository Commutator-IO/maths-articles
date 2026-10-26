import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum.Prime

/-!
# Partis, dés et loterie

Formalisation de la fiche « Partis, dés et loterie » (M. Hua, octobre 2026),
`partis-des-loterie.tex`, qui suit des feuillets anonymes du XVIIᵉ siècle de la BnF
(NAF 5176). Les numéros des énoncés sont ceux de la fiche.

## Modèles

* **Partis** (section 3). Une fonction `P : ℕ → ℕ → ℚ` qui vérifie les conditions de la
  proposition 3.1 (bords et moyenne des deux successeurs) est égale à la formule close du
  théorème 3.3, `P i j = (∑_{k<j} C(N, k)) / 2^N` avec `N = i + j - 1` (`partis_unique`).
  La formule elle-même est `G`, et `G_rec` est la récurrence, démontrée par la formule de
  Pascal (`sumChoose_succ`).
* **Dés** (section 5). Les probabilités sont des rationnels explicites, et les seuils se
  vérifient par `norm_num`.
* **Loterie** (section 7). Les coefficients binomiaux sont calculés par
  `Nat.choose_eq_descFactorial_div_factorial`, et la somme par l'identité de Vandermonde
  de Mathlib (`Nat.add_choose_eq`).

## Écarts avec la fiche

* Aucun énoncé de la fiche ne s'est révélé faux.

## Omis

L'interprétation probabiliste (espace des suites de manches, indépendance) : on formalise
la récurrence et sa solution, pas le modèle aléatoire dont elle vient ; la preuve par le
prolongement fictif ; la section 4 (trois joueurs) et la proposition 5.1 (trois dés) ;
la proposition 6.1 (anagrammes) ; les exercices.
-/

namespace Partis

open Finset

/-! ## 3. Le partage entre deux joueurs -/

/-- `∑_{k<j} C(n, k)`. -/
def sumChoose (n j : ℕ) : ℕ := ∑ k ∈ range j, n.choose k

/-- La formule de Pascal, sommée : `∑_{k<j+1} C(n+1, k) = ∑_{k<j+1} C(n, k) + ∑_{k<j} C(n, k)`. -/
theorem sumChoose_succ (n j : ℕ) :
    sumChoose (n + 1) (j + 1) = sumChoose n (j + 1) + sumChoose n j := by
  simp only [sumChoose, sum_range_succ' _ j, Nat.choose_succ_succ, sum_add_distrib,
    Nat.choose_zero_right]
  ring

/-- **Théorème 3.3**, la formule close : `G i j = (∑_{k<j} C(N, k)) / 2^N`, `N = i + j - 1`. -/
def G (i j : ℕ) : ℚ := (sumChoose (i + j - 1) j : ℚ) / 2 ^ (i + j - 1)

theorem G_zero_left (j : ℕ) (hj : 1 ≤ j) : G 0 j = 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hj
  rw [G, show 0 + (n + 1) - 1 = n by omega, sumChoose, Nat.sum_range_choose]
  simp

theorem G_zero_right (i : ℕ) : G i 0 = 0 := by
  simp [G, sumChoose]

/-- La récurrence de la proposition 3.1 pour la formule close. -/
theorem G_rec (i j : ℕ) : G (i + 1) (j + 1) = (G i (j + 1) + G (i + 1) j) / 2 := by
  rw [G, G, G, show i + 1 + (j + 1) - 1 = (i + j) + 1 by omega,
    show i + (j + 1) - 1 = i + j by omega, show i + 1 + j - 1 = i + j by omega,
    sumChoose_succ]
  push_cast
  field_simp
  ring

/-- **Proposition 3.1 et théorème 3.3** : une fonction qui vérifie les conditions des partis
est donnée par la formule close, en tout point autre que `(0, 0)`. -/
theorem partis_unique (P : ℕ → ℕ → ℚ) (h0 : ∀ j, 1 ≤ j → P 0 j = 1) (h1 : ∀ i, P i 0 = 0)
    (hrec : ∀ i j, P (i + 1) (j + 1) = (P i (j + 1) + P (i + 1) j) / 2) :
    ∀ i j, 1 ≤ i + j → P i j = G i j := by
  suffices h : ∀ s i j, i + j = s → 1 ≤ s → P i j = G i j from fun i j hij => h _ i j rfl hij
  intro s
  induction s with
  | zero => intro i j _ h; omega
  | succ s ih =>
    intro i j hs _
    rcases i with _ | i
    · rw [h0 j (by omega), G_zero_left j (by omega)]
    rcases j with _ | j
    · rw [h1, G_zero_right]
    rw [hrec, G_rec, ih i (j + 1) (by omega) (by omega), ih (i + 1) j (by omega) (by omega)]

/-- **Exemple 3.2** : la partie en trois manches (`11/16`, `14/16`, `12/16`) et en quatre
manches (`21/32`, `13/16`, `15/16`, `11/16`), et `2 à 0 de 4` vaut mieux que `1 à 0 de 2`. -/
theorem table :
    G 2 3 = 11 / 16 ∧ G 1 3 = 14 / 16 ∧ G 1 2 = 12 / 16 ∧
    G 3 4 = 21 / 32 ∧ G 2 4 = 13 / 16 ∧ G 1 4 = 15 / 16 ∧ G 2 3 = 11 / 16 ∧
    G 1 2 < G 2 4 := by
  simp only [G, sumChoose]
  norm_num [sum_range_succ, Nat.choose]

/-! ## 5. Les dés -/

/-- **Proposition 5.2** : au moins un six en `n` coups ; désavantageux en trois coups,
avantageux en quatre. -/
theorem six_seuil :
    1 - (5 / 6 : ℚ) ^ 3 = 91 / 216 ∧ 1 - (5 / 6 : ℚ) ^ 4 = 671 / 1296 ∧
    1 - (5 / 6 : ℚ) ^ 3 < 1 / 2 ∧ 1 / 2 < 1 - (5 / 6 : ℚ) ^ 4 := by
  norm_num

/-- **Proposition 5.3** : on ne peut jamais trouver un nombre de coups pour jouer jeu égal,
car `6^n ≠ 2 · 5^n`. -/
theorem jamais_egal (n : ℕ) : 6 ^ n ≠ 2 * 5 ^ n := by
  intro h
  rcases n with _ | n
  · norm_num at h
  have h3 : 3 ∣ 2 * 5 ^ (n + 1) := h ▸ dvd_pow (by norm_num : 3 ∣ 6) n.succ_ne_zero
  norm_num [Nat.prime_three.dvd_mul, Nat.prime_three.prime.dvd_pow_iff_dvd] at h3

/-- **Proposition 5.3**, sous forme de probabilité : `1 - (5/6)^n ≠ 1/2`. -/
theorem jamais_egal_proba (n : ℕ) : 1 - (5 / 6 : ℚ) ^ n ≠ 1 / 2 := by
  intro h
  have h' : ((6 ^ n : ℕ) : ℚ) = ((2 * 5 ^ n : ℕ) : ℚ) := by
    push_cast
    rw [div_pow] at h
    field_simp at h
    linarith
  exact jamais_egal n (by exact_mod_cast h')

/-- **Section 5** : le double six, désavantageux en 24 coups, avantageux en 25. -/
theorem mere :
    1 - (35 / 36 : ℚ) ^ 24 < 1 / 2 ∧ 1 / 2 < 1 - (35 / 36 : ℚ) ^ 25 := by
  norm_num

/-- **Section 5** : pour amener deux six du premier coup, `9` dés ne suffisent pas, `10`
suffisent. -/
theorem dix_des :
    1 - (5 / 6 : ℚ) ^ 9 - 9 * (1 / 6) * (5 / 6) ^ 8 < 1 / 2 ∧
    1 / 2 < 1 - (5 / 6 : ℚ) ^ 10 - 10 * (1 / 6) * (5 / 6) ^ 9 := by
  norm_num

/-! ## 7. La loterie de Gênes -/

theorem choose_100_5 : Nat.choose 100 5 = 75287520 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]; rfl

/-- **Proposition 7.1** : les nombres de tirages à `k` numéros communs. -/
theorem tirages :
    Nat.choose 95 5 = 57940519 ∧ 5 * Nat.choose 95 4 = 15917725 ∧
    10 * Nat.choose 95 3 = 1384150 ∧ 10 * Nat.choose 95 2 = 44650 ∧ 5 * 95 = 475 := by
  refine ⟨?_, ?_, ?_, ?_, rfl⟩ <;> rw [Nat.choose_eq_descFactorial_div_factorial] <;> rfl

/-- **Proposition 7.1** : l'identité de Vandermonde, `∑_k C(5,k) C(95,5-k) = C(100,5)`. -/
theorem vandermonde :
    ∑ ij ∈ antidiagonal 5, Nat.choose 5 ij.1 * Nat.choose 95 ij.2 = Nat.choose 100 5 :=
  (Nat.add_choose_eq 5 95 5).symm

/-- **Section 7** : le « fondement », `C(95, 2) = 94 + 93 + ⋯ + 1`. -/
theorem fondement : Nat.choose 95 2 = ∑ k ∈ range 95, k := by
  rw [Nat.choose_two_right, Finset.sum_range_id]

/-- **Section 7** : l'espérance du gain pour une pistole misée,
`21 326 600 / 75 287 520`, un peu plus du quart. -/
theorem esperance :
    ((20000 * 1 + 5000 * 475 + 300 * 44650 + 4 * 1384150 : ℕ) : ℚ) / 75287520
      = 21326600 / 75287520 ∧
    (1 : ℚ) / 4 < 21326600 / 75287520 ∧ (21326600 : ℚ) / 75287520 < 2 / 7 := by
  norm_num

end Partis

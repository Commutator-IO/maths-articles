import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.Tactic.LinearCombination

/-!
# Polygones réguliers et polynômes cyclotomiques

Formalisation de la fiche « Polygones réguliers et polynômes cyclotomiques » (M. Hua,
octobre 2026), `polygones-reguliers.tex`. Les numéros des énoncés sont ceux de la fiche.

Les sections 1 à 3 reprennent, en les traduisant, les définitions et les preuves du fichier
`lean/Grothendieck/Folder78.lean` du dépôt grothendieck-project, qui formalise une partie du dossier 78 des archives de
Grothendieck (cours de 1977-1978 sur les polygones réguliers).

## Modèles

* **Polynômes `F_n`** (définition 2.1). Ils sont définis par les polynômes de Tchebychev de
  seconde espèce renormalisés de Mathlib (`Polynomial.Chebyshev.S`) : `F_{2m} = S_{m-1}`,
  `F_{2m+1} = S_m + S_{m-1}`. Les formules de la fiche, `F_n(T + T⁻¹) = …`, sont
  `F_even_closed` et `F_odd_closed`, sur tout anneau commutatif, pour `T` inversible.
* **Le polygone universel** (section 1). Sur un anneau commutatif `k`, `u α` est la
  bijection `(x, y) ↦ (1 - y + α x, x)` de `k²`, et `s α n = u_α^n (0, 0)`.
* **Cyclotomie** (sections 4 et 6). L'irréductibilité de `Φ_n` sur `ℚ` et la congruence
  modulo `p` sont celles de Mathlib, réénoncées dans les termes de la fiche.

## Écarts avec la fiche

* Aucun énoncé de la fiche ne s'est révélé faux.
* Prop. 2.3 : l'identité est démontrée pour tout `n ∈ ℤ`, avec `F_{-n} = -F_n`.
* Prop. 6.1 : la congruence est énoncée avec l'exposant `p^r - p^{r-1}`, qui est `φ(p^r)`.

## Omis

La définition 1.1 des polygones réguliers dans un plan affine quelconque et le calcul qui
ramène tout polygone régulier au polygone universel (proposition 1.3) ; le théorème 5.2 sur
le polynôme minimal de `2 cos(2π/n)` et le corollaire 5.3 (`2 cos(2π/n) ∈ ℚ` seulement pour
`n ∈ {1, 2, 3, 4, 6}`) ; le corollaire 6.2 ; les exercices 1 et 2.
-/

namespace PolygonesReguliers

open Polynomial Polynomial.Chebyshev

/-! ## 2. Les polynômes `F_n` -/

section Poly

variable (R : Type*) [CommRing R]

/-- **Définition 2.1.** `F_{2m} = S_{m-1}`, `F_{2m+1} = S_m + S_{m-1}`. -/
noncomputable def F (n : ℤ) : R[X] :=
  if Even n then S R (n / 2 - 1) else S R (n / 2) + S R (n / 2 - 1)

theorem F_even (n m : ℤ) (h : n = 2 * m) : F R n = S R (m - 1) := by
  simp [F, h]

theorem F_odd (n m : ℤ) (h : n = 2 * m + 1) : F R n = S R m + S R (m - 1) := by
  subst h
  simp [F, show (2 * m + 1) / 2 = m by omega]

theorem F_zero : F R 0 = 0 := by
  rw [F_even R 0 0 (by ring)]; simp

theorem F_one : F R 1 = 1 := by
  rw [F_odd R 1 0 (by ring)]; simp

theorem F_two : F R 2 = 1 := by
  rw [F_even R 2 1 (by ring)]; simp

theorem F_three : F R 3 = X + 1 := by
  rw [F_odd R 3 1 (by ring)]; simp

theorem F_four : F R 4 = X := by
  rw [F_even R 4 2 (by ring)]; simp

theorem F_five : F R 5 = X ^ 2 + X - 1 := by
  rw [F_odd R 5 2 (by ring), show (2 : ℤ) - 1 = 1 by norm_num, S_two, S_one]; ring

theorem F_six : F R 6 = X ^ 2 - 1 := by
  rw [F_even R 6 3 (by ring), show (3 : ℤ) - 1 = 2 by norm_num, S_two]

/-- `F_{-n} = -F_n`. -/
theorem F_neg (n : ℤ) : F R (-n) = -F R n := by
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' n
  · rw [F_even R (-(2 * m)) (-m) (by ring), F_even R (2 * m) m rfl,
      ← show -(m - 1) - 2 = -m - 1 by ring, S_neg_sub_two]
  · rw [F_odd R (-(2 * m + 1)) (-m - 1) (by ring), F_odd R (2 * m + 1) m rfl,
      show -m - 1 - 1 = -m - 2 by ring, ← show -(m - 1) - 2 = -m - 1 by ring, S_neg_sub_two,
      S_neg_sub_two]
    ring

/-- `F_{n+4} = U F_{n+2} - F_n` : la récurrence à l'intérieur de chaque classe de parité. -/
theorem F_add_four (n : ℤ) : F R (n + 4) = X * F R (n + 2) - F R n := by
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' n
  · rw [F_even R (2 * m + 4) (m + 2) (by ring), F_even R (2 * m + 2) (m + 1) (by ring),
      F_even R (2 * m) m rfl, show m + 2 - 1 = m - 1 + 2 by ring,
      show m + 1 - 1 = m - 1 + 1 by ring]
    exact S_add_two R (m - 1)
  · rw [F_odd R (2 * m + 1 + 4) (m + 2) (by ring), F_odd R (2 * m + 1 + 2) (m + 1) (by ring),
      F_odd R (2 * m + 1) m rfl]
    have h1 := S_add_two R m
    have h2 := S_add_two R (m - 1)
    rw [show m - 1 + 2 = m + 1 by ring, show m - 1 + 1 = m by ring] at h2
    rw [show m + 2 - 1 = m + 1 by ring, show m + 1 - 1 = m by ring, h1, h2]
    ring

/-- **Proposition 2.3** (Grothendieck) :
`F_n F_{n+1} - U F_{n-1} F_n + F_{n-2} F_{n-1} = 1` pour tout `n ∈ ℤ`. -/
theorem F_identity (n : ℤ) :
    F R n * F R (n + 1) - X * F R (n - 1) * F R n + F R (n - 2) * F R (n - 1) = 1 := by
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' n
  · rw [F_even R (2 * m) m rfl, F_odd R (2 * m + 1) m rfl,
      F_odd R (2 * m - 1) (m - 1) (by ring), F_even R (2 * m - 2) (m - 1) (by ring)]
    have hS := S_eq R m
    have hC := S_sq_add_S_sq R (m - 2)
    rw [show m - 2 + 1 = m - 1 by ring] at hC
    rw [show m - 1 - 1 = m - 2 by ring]
    linear_combination S R (m - 1) * hS + hC
  · rw [F_odd R (2 * m + 1) m rfl, F_even R (2 * m + 1 + 1) (m + 1) (by ring),
      F_even R (2 * m + 1 - 1) m (by ring), F_odd R (2 * m + 1 - 2) (m - 1) (by ring)]
    have hS := S_eq R m
    have hC := S_sq_add_S_sq R (m - 1)
    rw [show m - 1 + 1 = m by ring] at hC
    rw [show m + 1 - 1 = m by ring, show m - 1 - 1 = m - 2 by ring]
    linear_combination S R (m - 1) * hS + hC

/-- **Corollaire 2.4** : la relation de Bézout `(F_{n-2} - U F_n) F_{n-1} + F_n F_{n+1} = 1`. -/
theorem F_bezout (n : ℤ) :
    (F R (n - 2) - X * F R n) * F R (n - 1) + F R n * F R (n + 1) = 1 := by
  linear_combination F_identity R n

/-- **Corollaire 2.4** : `F_{n-1}` et `F_{n+1}` sont premiers entre eux. -/
theorem isCoprime_F (n : ℤ) : IsCoprime (F R (n - 1)) (F R (n + 1)) :=
  ⟨_, _, F_bezout R n⟩

end Poly

/-- **Définition 2.1**, `n = 2m + 2` pair, sans dénominateur :
`F_n(t + t⁻¹) (t² - 1) t^m = t^{2m+2} - 1`, pour `t t' = 1` dans un anneau commutatif. -/
theorem F_even_closed {k : Type*} [CommRing k] (t t' : k) (ht : t * t' = 1) (m : ℕ) :
    (F k (2 * m + 2)).eval (t + t') * (t ^ 2 - 1) * t ^ m = t ^ (2 * m + 2) - 1 := by
  induction m using Nat.twoStepInduction with
  | zero => simp [F_two]
  | one =>
    rw [show 2 * ((1 : ℕ) : ℤ) + 2 = 4 by norm_num, F_four]; simp
    linear_combination (t ^ 2 - 1) * ht
  | more m ih0 ih1 =>
    have hrec := F_add_four k (2 * (m : ℤ) + 2)
    rw [show 2 * (m : ℤ) + 2 + 4 = 2 * ((m + 2 : ℕ) : ℤ) + 2 by push_cast; ring,
      show 2 * (m : ℤ) + 2 + 2 = 2 * ((m + 1 : ℕ) : ℤ) + 2 by push_cast; ring] at hrec
    rw [hrec, eval_sub, eval_mul, eval_X]
    linear_combination (t + t') * t * ih1 - t ^ 2 * ih0 + (t ^ (2 * (m + 1) + 2) - 1) * ht

/-- **Définition 2.1**, `n = 2m + 1` impair, sans dénominateur :
`F_n(t + t⁻¹) (t - 1) t^m = t^{2m+1} - 1`. -/
theorem F_odd_closed {k : Type*} [CommRing k] (t t' : k) (ht : t * t' = 1) (m : ℕ) :
    (F k (2 * m + 1)).eval (t + t') * (t - 1) * t ^ m = t ^ (2 * m + 1) - 1 := by
  induction m using Nat.twoStepInduction with
  | zero => simp [F_one]
  | one =>
    rw [show 2 * ((1 : ℕ) : ℤ) + 1 = 3 by norm_num, F_three]; simp
    linear_combination (t - 1) * ht
  | more m ih0 ih1 =>
    have hrec := F_add_four k (2 * (m : ℤ) + 1)
    rw [show 2 * (m : ℤ) + 1 + 4 = 2 * ((m + 2 : ℕ) : ℤ) + 1 by push_cast; ring,
      show 2 * (m : ℤ) + 1 + 2 = 2 * ((m + 1 : ℕ) : ℤ) + 1 by push_cast; ring] at hrec
    rw [hrec, eval_sub, eval_mul, eval_X]
    linear_combination (t + t') * t * ih1 - t ^ 2 * ih0 + (t ^ (2 * (m + 1) + 1) - 1) * ht

/-- `F_{2m+1}(2) = 2m + 1` (Grothendieck). -/
theorem F_odd_eval_two {k : Type*} [CommRing k] (m : ℕ) :
    (F k (2 * m + 1)).eval 2 = 2 * (m : k) + 1 := by
  induction m using Nat.twoStepInduction with
  | zero => simp [F_one]
  | one =>
    rw [show 2 * ((1 : ℕ) : ℤ) + 1 = 3 by norm_num, F_three]
    norm_num
  | more m ih0 ih1 =>
    have hrec := F_add_four k (2 * (m : ℤ) + 1)
    rw [show 2 * (m : ℤ) + 1 + 4 = 2 * ((m + 2 : ℕ) : ℤ) + 1 by push_cast; ring,
      show 2 * (m : ℤ) + 1 + 2 = 2 * ((m + 1 : ℕ) : ℤ) + 1 by push_cast; ring] at hrec
    rw [hrec, eval_sub, eval_mul, eval_X, ih1, ih0]
    push_cast; ring

/-! ## 1 et 3. Le polygone universel et le critère de fermeture -/

section Map

variable {k : Type*} [CommRing k]

/-- **Section 1.** `u_α (x, y) = (1 - y + α x, x)`, comme permutation de `k²`. -/
def u (α : k) : Equiv.Perm (k × k) where
  toFun p := (1 - p.2 + α * p.1, p.1)
  invFun p := (p.2, 1 - p.1 + α * p.2)
  left_inv p := Prod.ext rfl (show 1 - (1 - p.2 + α * p.1) + α * p.1 = p.2 by ring)
  right_inv p := Prod.ext (show 1 - (1 - p.1 + α * p.2) + α * p.2 = p.1 by ring) rfl

theorem u_apply (α : k) (p : k × k) : u α p = (1 - p.2 + α * p.1, p.1) := rfl

theorem u_inv_apply (α : k) (p : k × k) : (u α)⁻¹ p = (p.2, 1 - p.1 + α * p.2) := rfl

theorem zpow_succ_apply {X : Type*} (g : Equiv.Perm X) (n : ℤ) (p : X) :
    (g ^ (n + 1)) p = g ((g ^ n) p) := by
  rw [add_comm, zpow_add, zpow_one, Equiv.Perm.mul_apply]

theorem zpow_pred_apply {X : Type*} (g : Equiv.Perm X) (n : ℤ) (p : X) :
    (g ^ (n - 1)) p = g⁻¹ ((g ^ n) p) := by
  rw [sub_eq_neg_add, zpow_add, zpow_neg_one, Equiv.Perm.mul_apply]

/-- `X_n(α) = F_n F_{n+1}(α)`. -/
noncomputable def xs (α : k) (n : ℤ) : k := (F k n).eval α * (F k (n + 1)).eval α

theorem F_identity_eval (α : k) (n : ℤ) :
    (F k n).eval α * (F k (n + 1)).eval α - α * (F k (n - 1)).eval α * (F k n).eval α
      + (F k (n - 2)).eval α * (F k (n - 1)).eval α = 1 := by
  simpa using congrArg (eval α) (F_identity k n)

/-- `X_{n+1} = α X_n - X_{n-1} + 1`. -/
theorem xs_rec (α : k) (n : ℤ) : xs α (n + 1) = α * xs α n - xs α (n - 1) + 1 := by
  have h := F_identity_eval α (n + 1)
  rw [show n + 1 - 1 = n by ring, show n + 1 - 2 = n - 1 by ring] at h
  unfold xs
  rw [show n - 1 + 1 = n by ring]
  linear_combination h

/-- L'application affine qui envoie `(0,0), (1,0), (0,1)` sur `s_n, s_{n+1}, s_{n-1}`. -/
noncomputable def V (α : k) (n : ℤ) (p : k × k) : k × k :=
  ((1 - p.1 - p.2) * xs α n + p.1 * xs α (n + 1) + p.2 * xs α (n - 1),
    (1 - p.1 - p.2) * xs α (n - 1) + p.1 * xs α n + p.2 * xs α (n - 2))

theorem u_V (α : k) (n : ℤ) (p : k × k) : u α (V α n p) = V α (n + 1) p := by
  have r0 := xs_rec α (n - 1)
  have r1 := xs_rec α n
  have r2 := xs_rec α (n + 1)
  rw [show n - 1 + 1 = n by ring, show n - 1 - 1 = n - 2 by ring] at r0
  rw [show n + 1 - 1 = n by ring, show n + 1 + 1 = n + 2 by ring] at r2
  rw [u_apply]
  refine Prod.ext ?_ ?_
  · simp only [V, show n + 1 - 1 = n by ring, show n + 1 + 1 = n + 2 by ring]
    linear_combination -(1 - p.1 - p.2) * r1 - p.1 * r2 - p.2 * r0
  · simp only [V, show n + 1 - 1 = n by ring, show n + 1 - 2 = n - 1 by ring]

/-- `u_α^n (x, y) = (1 - x - y) s_n + x s_{n+1} + y s_{n-1}`. -/
theorem u_zpow_apply (α : k) (n : ℤ) (p : k × k) : (u α ^ n) p = V α n p := by
  induction n using Int.induction_on with
  | zero =>
    ext <;> simp [V, xs, F_neg, F_zero, F_one, F_two]
  | succ n ih => rw [zpow_succ_apply, ih, u_V]
  | pred n ih =>
    have h := u_V α (-(n : ℤ) - 1) p
    rw [show -(n : ℤ) - 1 + 1 = -n by ring] at h
    rw [zpow_pred_apply, ih, ← h]
    exact (u α).symm_apply_apply _

/-- Les sommets `s_n = u_α^n (0, 0)`. -/
noncomputable def s (α : k) (n : ℤ) : k × k := (u α ^ n) (0, 0)

/-- **Proposition 3.1** : `s_n = (F_n F_{n+1}(α), F_{n-1} F_n(α))`. -/
theorem vertex (α : k) (n : ℤ) :
    s α n = ((F k n).eval α * (F k (n + 1)).eval α,
      (F k (n - 1)).eval α * (F k n).eval α) := by
  rw [s, u_zpow_apply]
  simp [V, xs]

theorem s_zero (α : k) : s α 0 = (0, 0) := by simp [s]

theorem s_one (α : k) : s α 1 = (1, 0) := by simp [s, u_apply]

theorem s_neg_one (α : k) : s α (-1) = (0, 1) := by simp [s, u_inv_apply]

/-- **Théorème 3.2** (Grothendieck), b) ⇔ d) : `s_n = s_0 ⇔ F_n(α) = 0`. -/
theorem vertex_eq_iff (α : k) (n : ℤ) : s α n = (0, 0) ↔ (F k n).eval α = 0 := by
  rw [vertex, Prod.mk.injEq]
  refine ⟨fun ⟨h1, h2⟩ => ?_, fun h => by simp [h]⟩
  linear_combination -((F k n).eval α) * F_identity_eval α n + (F k n).eval α * h1
    + ((F k (n - 2)).eval α - α * (F k n).eval α) * h2

/-- **Théorème 3.2**, a) ⇔ d) : `u_α^n = id ⇔ F_n(α) = 0`, sur tout anneau commutatif. -/
theorem zpow_eq_one_iff (α : k) (n : ℤ) : u α ^ n = 1 ↔ (F k n).eval α = 0 := by
  refine ⟨fun h => by rw [← vertex_eq_iff, s, h]; rfl, fun h => ?_⟩
  have hx0 : xs α n = 0 := by simp [xs, h]
  have hxm : xs α (n - 1) = 0 := by simp [xs, h, show n - 1 + 1 = n by ring]
  have hx1 : xs α (n + 1) = 1 := by rw [xs_rec, hx0, hxm]; ring
  have hxm2 : xs α (n - 2) = 1 := by
    have := xs_rec α (n - 1)
    rw [show n - 1 + 1 = n by ring, show n - 1 - 1 = n - 2 by ring, hx0, hxm] at this
    linear_combination this
  ext p
  · rw [u_zpow_apply]; simp [V, hx0, hx1, hxm]
  · rw [u_zpow_apply]; simp [V, hx0, hxm, hxm2]

/-- **Théorème 3.2**, c) ⇔ d) : `u_α^n s_i = s_i` pour un `i` si et seulement si `F_n(α) = 0`. -/
theorem zpow_fix_iff (α : k) (n i : ℤ) :
    (u α ^ n) (s α i) = s α i ↔ (F k n).eval α = 0 := by
  rw [← vertex_eq_iff, s, s, ← Equiv.Perm.mul_apply, ← zpow_add, add_comm, zpow_add,
    Equiv.Perm.mul_apply, (u α ^ i).injective.eq_iff]

/-- La symétrie `σ₁ (x, y) = (y, x)`. -/
def σ₁ : Equiv.Perm (k × k) := Equiv.prodComm k k

/-- **Section 1** : `σ₁ u_α σ₁ = u_α⁻¹`, donc `u_α` et `σ₁` engendrent une action diédrale. -/
theorem inv_eq_conj (α : k) : σ₁ * u α * σ₁ = (u α)⁻¹ := by
  ext p <;> simp [σ₁, u_apply, u_inv_apply]

/-- **Remarque 3.4** : la conique `f_α (x, y) = x² - x + y² - y - α x y` est invariante par
`u_α` et passe par tous les sommets. -/
def fα (α : k) (p : k × k) : k := p.1 ^ 2 - p.1 + p.2 ^ 2 - p.2 - α * p.1 * p.2

theorem conic_invariant (α : k) :
    (∀ p, fα α (u α p) = fα α p) ∧ ∀ n, fα α (s α n) = 0 := by
  have hinv : ∀ p, fα α (u α p) = fα α p := fun p => by simp only [fα, u_apply]; ring
  refine ⟨hinv, fun n => ?_⟩
  induction n using Int.induction_on with
  | zero => simp [s, fα]
  | succ n ih => rw [s, zpow_succ_apply, hinv]; exact ih
  | pred n ih =>
    rw [← hinv, s, ← zpow_succ_apply, show -(n : ℤ) - 1 + 1 = -n by ring]; exact ih

/-- **Exemple 3.3** : le triangle (`α = -1`), le carré (`α = 0`) et l'hexagone (`α = 1`)
sont définis sur tout anneau commutatif. -/
theorem triangle_carre_hexagone :
    u (-1 : k) ^ (3 : ℤ) = 1 ∧ u (0 : k) ^ (4 : ℤ) = 1 ∧ u (1 : k) ^ (6 : ℤ) = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [zpow_eq_one_iff]
  · simp [F_three]
  · simp [F_four]
  · simp [F_six]

/-- **Exemple 3.3** : si `α² + α - 1 = 0`, le polygone d'invariant `α` est un pentagone. -/
theorem pentagone (α : k) (h : α ^ 2 + α - 1 = 0) : u α ^ (5 : ℤ) = 1 := by
  rw [zpow_eq_one_iff, F_five]; simpa using h

/-- **Remarque 3.4** : pour `α = 2`, la conique invariante est la parabole
`(x - y)² = x + y`. -/
theorem parabole_conic (q : k × k) : fα 2 q = (q.1 - q.2) ^ 2 - (q.1 + q.2) := by
  simp only [fα]; ring

/-- **Remarque 3.4** : en caractéristique `p` impaire, `u_2^p = id` : le `p`-gone régulier
inscrit dans une parabole. -/
theorem parabole_zpow (p : ℕ) [hp : Fact p.Prime] [CharP k p] (hp2 : p ≠ 2) :
    u (2 : k) ^ (p : ℤ) = 1 := by
  rw [zpow_eq_one_iff]
  obtain ⟨m, hm⟩ := hp.out.odd_of_ne_two hp2
  rw [show (p : ℤ) = 2 * ((m : ℕ) : ℤ) + 1 by rw [hm]; push_cast; ring, F_odd_eval_two]
  exact_mod_cast hm ▸ CharP.cast_eq_zero k p

end Map

/-! ## 4 et 6. Polynômes cyclotomiques -/

/-- **Théorème 4.3** : `Φ_n` est irréductible sur `ℚ` (Mathlib). -/
theorem cyclotomic_irreducible {n : ℕ} (hn : 0 < n) : Irreducible (cyclotomic n ℚ) :=
  cyclotomic.irreducible_rat hn

/-- **Proposition 6.1** (Grothendieck) : pour `n = p^r n'` avec `p ∤ n'` et
`r ≥ 1`, `Φ_n ≡ Φ_{n'}^{p^r - p^{r-1}} (mod p)`, et `p^r - p^{r-1} = φ(p^r)`. -/
theorem cyclotomic_mod_p (p : ℕ) [Fact p.Prime] {n' r : ℕ} (hn' : ¬ p ∣ n') (hr : 0 < r) :
    cyclotomic (p ^ r * n') (ZMod p) = cyclotomic n' (ZMod p) ^ (p ^ r - p ^ (r - 1)) :=
  cyclotomic_mul_prime_pow_eq (ZMod p) hn' hr

end PolygonesReguliers

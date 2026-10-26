import Mathlib.NumberTheory.Pell
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.Niven
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Entiers quadratiques : unités de ℤ[√2] et polygones réguliers du réseau

Formalisation de la fiche « Entiers quadratiques : unités de ℤ[√2] et polygones réguliers
du réseau » (M. Hua, octobre 2026, leçon 126). Les numéros cités sont ceux de la fiche.

## Modèles

* **Anneau `ℤ[√d]`** (§ 2). C'est `ℤ√d` (`Zsqrtd d`) de Mathlib, avec sa norme `Zsqrtd.norm`
  (`N(x + y√d) = x² - d y²`) ; la conjugaison `σ` est `star`. Les énoncés sur `ℤ[√2]` sont
  purement algébriques : on n'utilise pas le plongement dans `ℝ`, sauf pour la
  proposition 2.8, énoncée dans `ℝ` avec `Real.sqrt`.
* **Unités** (corollaire 2.6). `ε : (ℤ√2)ˣ` est `1 + √2`, d'inverse `-1 + √2`, et
  `ε₀ : ℤ√2` est le même élément vu dans l'anneau.
* **Équation de Pell** (corollaire 2.6, exercice 2). On relie la fiche à `Pell.Solution₁` et
  `Pell.IsFundamental` de Mathlib, qui ne traitent que la norme `1`.
* **Géométrie** (§ 3). Un point de `ℤ²` est un couple d'entiers ; le carré de la distance est
  `dist2`. Une rotation d'angle `θ` est écrite en coordonnées, avec `cos θ` et `sin θ`.

## Écarts avec la fiche

* Corollaire 2.6 (1) : la fiche passe par le théorème 2.5 (plus petite unité `> 1` et
  descente sur les réels). Ici, la descente est entière (`exists_pow_of_norm`), puis on traite
  les quatre signes de `(a, b)`.
* Proposition 3.1 : seule la preuve par l'aire est formalisée, sous la forme entière
  `(2 det(u, v))² = 3 |u|⁴`.
* Théorème 3.3 : on formalise l'énoncé « la rotation d'angle `2π/n` envoie un vecteur entier
  non nul sur un vecteur entier si et seulement si `n = 4` » (`thm_3_3`), qui s'applique aux
  vecteurs côtés `w₀, w₁ = R w₀` d'un polygone régulier. La preuve utilise le théorème de
  Niven de Mathlib au lieu du réseau `L` et de la trace ; l'étape « `2 cos(2π/n) ∈ ℤ` entraîne
  `n ∈ {3, 4, 6}` » est énoncée à part (`trace_entiere`).
* Aucun énoncé de la fiche ne s'est révélé faux.

## Omis

Le théorème 2.5 pour `d` quelconque (existence et minimalité de `ε_d`), les remarques 2.12 à
2.14 (`ℤ[√10]`, fractions continues, théorème de Dirichlet), la définition générale d'un
polygone régulier et l'étape 2 du théorème 3.3 (le réseau `L` est libre de rang 2), les
remarques 3.4 à 3.6, les exercices 1, 4 et 5 (sauf l'étape de trace), et la liste explicite des
solutions de l'exercice 3.
-/
open Real

namespace EntiersQuadratiques

/-- Fiche, lemme 2.1 : si `d` n'est pas un carré parfait, `√d` est irrationnel. -/
theorem irrational_sqrt {d : ℕ} (hd : ¬IsSquare d) : Irrational √(d : ℝ) :=
  irrational_sqrt_natCast_iff.2 hd

/-- Fiche, lemme 2.1 : si `r + s√d = 0` avec `r, s` rationnels, alors `r = s = 0`. -/
theorem lemme_2_1 {d : ℕ} (hd : ¬IsSquare d) {r s : ℚ} (h : (r : ℝ) + s * √(d : ℝ) = 0) :
    r = 0 ∧ s = 0 := by
  by_cases hs : s = 0
  · subst hs; simpa using h
  · exfalso
    apply (irrational_sqrt hd).ne_rat (-r / s)
    have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs
    push_cast
    field_simp
    linarith

/-- Fiche, lemme 2.1, forme entière : `x² = d y²` n'a que la solution triviale. -/
theorem sq_eq_mul_sq {d : ℕ} (hd : ¬IsSquare d) {x y : ℤ} (h : x ^ 2 = d * y ^ 2) :
    x = 0 ∧ y = 0 := by
  have hy : y = 0 := by
    by_contra hy
    apply (irrational_sqrt hd).ne_rat (|x| / |y| : ℚ)
    have hy' : (y : ℝ) ≠ 0 := by exact_mod_cast hy
    have e : (d : ℝ) = (|(x : ℝ)| / |(y : ℝ)|) ^ 2 := by
      rw [div_pow, sq_abs, sq_abs, eq_div_iff (pow_ne_zero 2 hy')]
      exact_mod_cast h.symm
    push_cast
    rw [e, Real.sqrt_sq (by positivity)]
  subst hy
  simpa using h

open Zsqrtd

/-- `1 + √2`. -/
def ε₀ : ℤ√2 := ⟨1, 1⟩

/-- Fiche, proposition 2.3 (2) : la norme est multiplicative (`Zsqrtd.norm_mul` de Mathlib). -/
theorem prop_2_3_norm_mul {d : ℤ} (z w : ℤ√d) : (z * w).norm = z.norm * w.norm :=
  Zsqrtd.norm_mul z w

/-- Fiche, proposition 2.3 (3) : `z` est inversible si et seulement si `N(z) = ±1`. -/
theorem prop_2_3_isUnit_iff {d : ℤ} (z : ℤ√d) : IsUnit z ↔ z.norm = 1 ∨ z.norm = -1 := by
  rw [Zsqrtd.isUnit_iff_norm_isUnit, Int.isUnit_iff]

/-- Fiche, proposition 2.3 (3) : l'inverse de `z` est `N(z) σ(z)` (la conjugaison `σ` est `star`). -/
theorem prop_2_3_inv {d : ℤ} (z : ℤ√d) (hz : z.norm = 1 ∨ z.norm = -1) :
    z * ((z.norm : ℤ√d) * star z) = 1 := by
  rw [mul_left_comm, ← Zsqrtd.norm_eq_mul_conj, ← Int.cast_mul]
  rcases hz with h | h <;> simp [h]

/-- La norme de `x + y√d` est `x² - d y²`. -/
theorem norm_mk {d : ℤ} (x y : ℤ) : (⟨x, y⟩ : ℤ√d).norm = x ^ 2 - d * y ^ 2 := by
  simp [Zsqrtd.norm_def]; ring

/-- Fiche, proposition 2.3 : `N(z^q) = N(z)^q`. -/
theorem norm_pow {d : ℤ} (z : ℤ√d) (q : ℕ) : (z ^ q).norm = z.norm ^ q := by
  induction q with
  | zero => simp
  | succ q ih => rw [pow_succ, pow_succ, Zsqrtd.norm_mul, ih]

/-- Fiche, § 2.1 : `a_q² - 2 b_q² = N((1 + √2)^q) = (-1)^q`. -/
theorem norm_ε₀_pow (q : ℕ) : (ε₀ ^ q).norm = (-1) ^ q := by
  rw [norm_pow]; simp [ε₀, norm_mk]

/-- Fiche, corollaire 2.6 (2), réciproque : les coefficients `a_q, b_q` de `(1 + √2)^q` sont positifs. -/
theorem ε₀_pow_nonneg (q : ℕ) : 0 ≤ (ε₀ ^ q).re ∧ 0 ≤ (ε₀ ^ q).im := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [pow_succ, Zsqrtd.re_mul, Zsqrtd.im_mul]
    simp only [show ε₀.re = 1 from rfl, show ε₀.im = 1 from rfl]
    constructor <;> linarith [ih.1, ih.2]

/-- Fiche, corollaire 2.6 (2), sens direct. Descente : si `x, y ≥ 0` et `x² - 2y² = ±1`,
alors `x + y√2 = (1 + √2)^q`. On divise par `1 + √2`, ce qui donne `(2y - x) + (x - y)√2`
avec `0 ≤ x - y < y`. -/
theorem exists_pow_of_norm {x y : ℤ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x ^ 2 - 2 * y ^ 2 = 1 ∨ x ^ 2 - 2 * y ^ 2 = -1) :
    ∃ q : ℕ, (⟨x, y⟩ : ℤ√2) = ε₀ ^ q := by
  lift y to ℕ using hy
  induction y using Nat.strong_induction_on generalizing x with
  | _ y ih =>
    rcases Nat.eq_zero_or_pos y with rfl | hy0
    · refine ⟨0, ?_⟩
      have h' : (x - 1) * (x + 1) = 0 := by
        rcases h with h | h <;> push_cast at h <;> nlinarith [sq_nonneg x]
      have : x = 1 := by rcases mul_eq_zero.1 h' with h | h <;> omega
      subst this; rfl
    · have hy1 : (1 : ℤ) ≤ y := by exact_mod_cast hy0
      have hxy : (y : ℤ) ≤ x := by
        by_contra! hc
        rcases h with h | h <;> nlinarith
      have hx2 : x < 2 * y := by
        by_contra! hc
        rcases h with h | h <;> nlinarith
      obtain ⟨y', hy'⟩ : ∃ y' : ℕ, (y' : ℤ) = x - y := ⟨(x - y).toNat, by omega⟩
      have hlt : y' < y := by omega
      obtain ⟨q, hq⟩ := ih y' hlt (x := 2 * y - x) (by omega) (by
        rw [hy']; rcases h with h | h
        · right; linarith [h]
        · left; linarith [h])
      refine ⟨q + 1, ?_⟩
      rw [pow_succ, ← hq]
      ext <;> simp [ε₀, hy'] <;> ring

/-- Fiche, corollaire 2.6 (2) : les solutions positives de `x² - 2y² = η`, `η = ±1`, sont les
coefficients `(a_q, b_q)` de `(1 + √2)^q`, et le signe est `η = (-1)^q`. -/
theorem cor_2_6_2 {x y : ℤ} (hx : 0 ≤ x) (hy : 0 ≤ y) (η : ℤ) :
    x ^ 2 - 2 * y ^ 2 = η ∧ (η = 1 ∨ η = -1) ↔
      ∃ q : ℕ, (⟨x, y⟩ : ℤ√2) = ε₀ ^ q ∧ η = (-1) ^ q := by
  constructor
  · rintro ⟨h, hη⟩
    obtain ⟨q, hq⟩ := exists_pow_of_norm hx hy (h ▸ hη)
    refine ⟨q, hq, ?_⟩
    rw [← h, ← norm_ε₀_pow, ← hq, norm_mk]
  · rintro ⟨q, hq, rfl⟩
    refine ⟨?_, neg_one_pow_eq_or ℤ q⟩
    rw [← norm_ε₀_pow, ← hq, norm_mk]

/-- L'unité `ε = 1 + √2`, d'inverse `-1 + √2`. -/
def ε : (ℤ√2)ˣ where
  val := ⟨1, 1⟩
  inv := ⟨-1, 1⟩
  val_inv := by ext <;> simp
  inv_val := by ext <;> simp

/-- `σ(1 + √2) = 1 - √2 = -(1 + √2)⁻¹`. -/
theorem star_ε₀ : star ε₀ = -((ε⁻¹ : (ℤ√2)ˣ) : ℤ√2) := by
  ext <;> simp [ε₀, ε]

/-- Prédicat « `z = ±ε^k` ». -/
def PmPow (z : ℤ√2) : Prop := ∃ k : ℤ, z = ((ε ^ k : (ℤ√2)ˣ) : ℤ√2) ∨ z = -((ε ^ k : (ℤ√2)ˣ) : ℤ√2)

/-- Auxiliaire : la propriété « `z = ±ε^k` » est stable par `z ↦ -z`. -/
theorem pmPow_neg {z : ℤ√2} (h : PmPow z) : PmPow (-z) := by
  obtain ⟨k, hk | hk⟩ := h
  · exact ⟨k, Or.inr (by rw [hk])⟩
  · exact ⟨k, Or.inl (by rw [hk, neg_neg])⟩

/-- Auxiliaire : `(1 + √2)^q` est de la forme `±ε^k`. -/
theorem pmPow_pow (q : ℕ) : PmPow (ε₀ ^ q) :=
  ⟨q, Or.inl (by rw [zpow_natCast, Units.val_pow_eq_pow_val]; rfl)⟩

/-- Auxiliaire : `σ((1 + √2)^q) = (-1)^q ε^(-q)` est de la forme `±ε^k`. -/
theorem pmPow_star_pow (q : ℕ) : PmPow (star (ε₀ ^ q)) := by
  rw [star_pow, star_ε₀, neg_pow, ← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_neg_one,
    ← zpow_mul]
  rcases neg_one_pow_eq_or (ℤ√2) q with h | h <;> rw [h]
  · exact ⟨_, Or.inl (one_mul _)⟩
  · exact ⟨_, Or.inr (neg_one_mul _)⟩

/-- Fiche, corollaire 2.6 (1) : `ℤ[√2]ˣ = {±(1 + √2)^k, k ∈ ℤ}`.

La preuve n'est pas celle de la fiche (descente sur les réels, théorème 2.5) : on applique la
descente entière `exists_pow_of_norm` à `|a| + |b|√2`, puis on distingue les quatre signes,
qui correspondent à `±u` et `±σ(u)`. -/
theorem cor_2_6_1 (u : (ℤ√2)ˣ) : ∃ k : ℤ, u = ε ^ k ∨ u = -ε ^ k := by
  have hn := (prop_2_3_isUnit_iff (u : ℤ√2)).1 u.isUnit
  rw [show (u : ℤ√2) = ⟨(u : ℤ√2).re, (u : ℤ√2).im⟩ from rfl, norm_mk] at hn
  obtain ⟨q, hq⟩ := exists_pow_of_norm (abs_nonneg (u : ℤ√2).re) (abs_nonneg (u : ℤ√2).im)
    (by simpa only [sq_abs] using hn)
  have hP : PmPow (u : ℤ√2) := by
    rcases abs_cases (u : ℤ√2).re with ⟨h1, -⟩ | ⟨h1, -⟩ <;>
      rcases abs_cases (u : ℤ√2).im with ⟨h2, -⟩ | ⟨h2, -⟩ <;> rw [h1, h2] at hq
    · convert pmPow_pow q using 1
    · convert pmPow_star_pow q using 1; rw [← hq]; ext <;> simp
    · convert pmPow_neg (pmPow_star_pow q) using 1; rw [← hq]; ext <;> simp
    · convert pmPow_neg (pmPow_pow q) using 1; rw [← hq]; ext <;> simp
  obtain ⟨k, hk | hk⟩ := hP
  · exact ⟨k, Or.inl (Units.ext hk)⟩
  · exact ⟨k, Or.inr (Units.ext (by rw [hk, Units.val_neg]))⟩

/-- Fiche, proposition 2.8 (unicité) : `n ↦ √(n+1) + √n` est strictement croissante. -/
theorem sqrt_succ_add_sqrt_strictMono : StrictMono (fun n : ℕ => √((n : ℝ) + 1) + √(n : ℝ)) := by
  intro m n hmn
  have h : (m : ℝ) < n := by exact_mod_cast hmn
  exact add_lt_add (Real.sqrt_lt_sqrt (by positivity) (by linarith))
    (Real.sqrt_lt_sqrt (by positivity) h)

/-- Fiche, proposition 2.8 : les coefficients `A_q, B_q` de `(a + b√d)^q` sont positifs. -/
theorem pow_coeffs_nonneg {d : ℤ} (hd : 0 ≤ d) {w : ℤ√d} (h1 : 0 ≤ w.re) (h2 : 0 ≤ w.im)
    (q : ℕ) : 0 ≤ (w ^ q).re ∧ 0 ≤ (w ^ q).im := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [pow_succ, Zsqrtd.re_mul, Zsqrtd.im_mul]
    constructor
    · nlinarith [mul_nonneg ih.1 h1, mul_nonneg (mul_nonneg hd ih.2) h2]
    · nlinarith [mul_nonneg ih.1 h2, mul_nonneg ih.2 h1]

/-- Passage de `ℤ[√d]` aux réels : `(a + b√d)^q = A_q + B_q √d`. -/
theorem toReal_pow (d : ℕ) (w : ℤ√(d : ℤ)) (q : ℕ) :
    ((w.re : ℝ) + w.im * √(d : ℝ)) ^ q = (w ^ q).re + (w ^ q).im * √(d : ℝ) := by
  have hs : √(d : ℝ) * √(d : ℝ) = d := Real.mul_self_sqrt (Nat.cast_nonneg d)
  induction q with
  | zero => simp
  | succ q ih =>
    rw [pow_succ, pow_succ, ih, Zsqrtd.re_mul, Zsqrtd.im_mul]
    push_cast
    linear_combination ((w ^ q).im * w.im : ℝ) * hs

/-- Fiche, proposition 2.8 : si `a² - d b² = ±1` avec `a, b ∈ ℕ`, alors pour tout `q`,
`(a + b√d)^q = √(n+1) + √n` pour un unique `n ∈ ℕ`. Ici `d ∈ ℕ` est quelconque
(remarque 2.10 : l'hypothèse « `d` non carré » est inutile). -/
theorem prop_2_8 (d a b : ℕ) (h : (a : ℤ) ^ 2 - d * b ^ 2 = 1 ∨ (a : ℤ) ^ 2 - d * b ^ 2 = -1)
    (q : ℕ) : ∃! n : ℕ, ((a : ℝ) + b * √(d : ℝ)) ^ q = √((n : ℝ) + 1) + √(n : ℝ) := by
  obtain ⟨z, hz⟩ : ∃ z, z = (⟨a, b⟩ : ℤ√(d : ℤ)) ^ q := ⟨_, rfl⟩
  have hpos : 0 ≤ z.re ∧ 0 ≤ z.im := by
    rw [hz]; exact pow_coeffs_nonneg (by positivity) (by simp) (by simp) q
  have hreal : ((a : ℝ) + b * √(d : ℝ)) ^ q = z.re + z.im * √(d : ℝ) := by
    rw [hz, ← toReal_pow]; simp
  have hnorm : z.re ^ 2 - d * z.im ^ 2 = 1 ∨ z.re ^ 2 - d * z.im ^ 2 = -1 := by
    rw [← norm_mk, show (⟨z.re, z.im⟩ : ℤ√(d : ℤ)) = z from rfl, hz, norm_pow, norm_mk]
    rcases h with h | h <;> rw [h]
    · simp
    · exact neg_one_pow_eq_or ℤ q
  obtain ⟨A, hA⟩ : ∃ A : ℕ, (A : ℤ) = z.re := ⟨z.re.toNat, Int.toNat_of_nonneg hpos.1⟩
  obtain ⟨B, hB⟩ : ∃ B : ℕ, (B : ℤ) = z.im := ⟨z.im.toNat, Int.toNat_of_nonneg hpos.2⟩
  rw [← hA, ← hB] at hnorm
  rw [← hA, ← hB] at hreal
  have hsA : √((A : ℝ) ^ 2) = A := Real.sqrt_sq (Nat.cast_nonneg A)
  have hsB : √((d : ℝ) * (B : ℝ) ^ 2) = B * √(d : ℝ) := by
    rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq (Nat.cast_nonneg B), mul_comm]
  have key : ∃ n : ℕ, ((a : ℝ) + b * √(d : ℝ)) ^ q = √((n : ℝ) + 1) + √(n : ℝ) := by
    rcases hnorm with hn | hn
    · have hn' : A ^ 2 = d * B ^ 2 + 1 := by zify; linarith
      refine ⟨d * B ^ 2, ?_⟩
      rw [hreal]
      have : ((d * B ^ 2 : ℕ) : ℝ) + 1 = (A : ℝ) ^ 2 := by exact_mod_cast hn'.symm
      rw [this, hsA]; push_cast; rw [hsB]
    · have hn' : d * B ^ 2 = A ^ 2 + 1 := by zify; linarith
      refine ⟨A ^ 2, ?_⟩
      rw [hreal]
      have : ((A ^ 2 : ℕ) : ℝ) + 1 = (d : ℝ) * (B : ℝ) ^ 2 := by exact_mod_cast hn'.symm
      rw [this, hsB]; push_cast; rw [hsA, add_comm]
  obtain ⟨n, hn⟩ := key
  exact ⟨n, hn, fun m hm => sqrt_succ_add_sqrt_strictMono.injective (hm.symm.trans hn)⟩

/-- Fiche, § 1 et exemple 2.9 : l'exercice d'origine, `(1 + √2)^q = √(n+1) + √n`, `n` unique. -/
theorem exercice_origine (q : ℕ) : ∃! n : ℕ, (1 + √2) ^ q = √((n : ℝ) + 1) + √(n : ℝ) := by
  simpa using prop_2_8 2 1 1 (by norm_num) q

/-- `3` n'est pas un carré parfait. -/
theorem not_isSquare_three : ¬IsSquare (3 : ℕ) := by
  rintro ⟨r, hr⟩
  have : r ≤ 2 := by nlinarith
  interval_cases r <;> omega

/-- Carré de la distance euclidienne entre deux points de `ℤ²`. -/
def dist2 (p q : ℤ × ℤ) : ℤ := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- Fiche, proposition 3.1 : trois points de `ℤ²` deux à deux équidistants sont confondus.

C'est la preuve par l'aire, sous forme entière : avec `u = b - a`, `v = c - a`, `S = |u|²` et
`D = det(u, v)`, on a `(2D)² = 3 S²`, donc `S = 0` par le lemme 2.1. -/
theorem prop_3_1 (a b c : ℤ × ℤ) (h1 : dist2 a b = dist2 b c) (h2 : dist2 b c = dist2 c a) :
    a = b ∧ b = c := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  obtain ⟨c1, c2⟩ := c
  simp only [dist2] at h1 h2
  obtain ⟨u1, rfl⟩ : ∃ t, b1 = a1 + t := ⟨b1 - a1, by ring⟩
  obtain ⟨u2, rfl⟩ : ∃ t, b2 = a2 + t := ⟨b2 - a2, by ring⟩
  obtain ⟨v1, rfl⟩ : ∃ t, c1 = a1 + t := ⟨c1 - a1, by ring⟩
  obtain ⟨v2, rfl⟩ : ∃ t, c2 = a2 + t := ⟨c2 - a2, by ring⟩
  -- `|u|² = |v|²` et `2 u·v = |u|²`
  have hS : v1 ^ 2 + v2 ^ 2 = u1 ^ 2 + u2 ^ 2 := by linear_combination -h1 - h2
  have hP : 2 * (u1 * v1 + u2 * v2) = u1 ^ 2 + u2 ^ 2 := by linear_combination h1 + hS
  have key : (2 * (u1 * v2 - u2 * v1)) ^ 2 = (3 : ℕ) * (u1 ^ 2 + u2 ^ 2) ^ 2 := by
    push_cast
    linear_combination (4 * (u1 ^ 2 + u2 ^ 2)) * hS
      - (2 * (u1 * v1 + u2 * v2) + (u1 ^ 2 + u2 ^ 2)) * hP
  have hS0 := (sq_eq_mul_sq not_isSquare_three key).2
  have e1 : u1 = 0 := by nlinarith [sq_nonneg u1, sq_nonneg u2]
  have e2 : u2 = 0 := by nlinarith [sq_nonneg u1, sq_nonneg u2]
  have e3 : v1 = 0 := by nlinarith [sq_nonneg v1, sq_nonneg v2]
  have e4 : v2 = 0 := by nlinarith [sq_nonneg v1, sq_nonneg v2]
  subst e1 e2 e3 e4
  simp

/-- Fiche, théorème 3.3, étape 3 : pour `n ≥ 3`, `-1/2 ≤ cos(2π/n) < 1`. -/
theorem cos_two_pi_div_bounds {n : ℕ} (hn : 3 ≤ n) :
    -(1 / 2) ≤ cos (2 * π / n) ∧ cos (2 * π / n) < 1 := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < 2 * π / n := by positivity
  have hle : 2 * π / n ≤ π - π / 3 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [pi_pos]
  constructor
  · have := cos_le_cos_of_nonneg_of_le_pi hpos.le (by linarith [pi_pos]) hle
    rw [cos_pi_sub, cos_pi_div_three] at this
    linarith
  · have := cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith [pi_pos]) hpos
    rwa [cos_zero] at this

/-- Pour `n ≥ 3`, `2π/n ∈ [0, π]`, où le cosinus est injectif. -/
theorem two_pi_div_mem {n : ℕ} (hn : 3 ≤ n) : 2 * π / n ∈ Set.Icc 0 π := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (by linarith)]; nlinarith [pi_pos]

/-- Auxiliaire : `2π/n = 2π/m` entraîne `n = m`. -/
theorem eq_of_two_pi_div {n : ℕ} {m : ℝ} (hn : 3 ≤ n) (hm : 0 < m) (h : 2 * π / n = 2 * π / m) :
    (n : ℝ) = m := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  rw [div_eq_div_iff hn'.ne' hm.ne'] at h
  exact (mul_left_cancel₀ (by positivity : (2 * π : ℝ) ≠ 0) h).symm

/-- `cos(2π/n) = -1/2` entraîne `n = 3`. -/
theorem eq_three_of_cos {n : ℕ} (hn : 3 ≤ n) (h : cos (2 * π / n) = -(1 / 2)) : n = 3 := by
  have h3 : cos (2 * π / (3 : ℝ)) = -(1 / 2) := by
    rw [show 2 * π / (3 : ℝ) = π - π / 3 by ring, cos_pi_sub, cos_pi_div_three]
  have := injOn_cos (two_pi_div_mem hn) (by simpa using two_pi_div_mem (le_refl 3)) (h.trans h3.symm)
  exact_mod_cast eq_of_two_pi_div hn (by norm_num) this

/-- `cos(2π/n) = 0` entraîne `n = 4`. -/
theorem eq_four_of_cos {n : ℕ} (hn : 3 ≤ n) (h : cos (2 * π / n) = 0) : n = 4 := by
  have h4 : cos (2 * π / (4 : ℝ)) = 0 := by
    rw [show 2 * π / (4 : ℝ) = π / 2 by ring, cos_pi_div_two]
  have := injOn_cos (two_pi_div_mem hn) (by simpa using two_pi_div_mem (n := 4) (by norm_num))
    (h.trans h4.symm)
  exact_mod_cast eq_of_two_pi_div hn (by norm_num) this

/-- `cos(2π/n) = 1/2` entraîne `n = 6`. -/
theorem eq_six_of_cos {n : ℕ} (hn : 3 ≤ n) (h : cos (2 * π / n) = 1 / 2) : n = 6 := by
  have h6 : cos (2 * π / (6 : ℝ)) = 1 / 2 := by
    rw [show 2 * π / (6 : ℝ) = π / 3 by ring, cos_pi_div_three]
  have := injOn_cos (two_pi_div_mem hn) (by simpa using two_pi_div_mem (n := 6) (by norm_num))
    (h.trans h6.symm)
  exact_mod_cast eq_of_two_pi_div hn (by norm_num) this

/-- Fiche, théorème 3.3, étape 3 (et exercice 5) : si `n ≥ 3` et `2 cos(2π/n)` est entier,
alors `n ∈ {3, 4, 6}`. -/
theorem trace_entiere {n : ℕ} (hn : 3 ≤ n) {k : ℤ} (hk : 2 * cos (2 * π / n) = k) :
    n = 3 ∨ n = 4 ∨ n = 6 := by
  obtain ⟨h1, h2⟩ := cos_two_pi_div_bounds hn
  have hk1 : -1 ≤ k := by exact_mod_cast (by linarith : (-1 : ℝ) ≤ k)
  have hk2 : k < 2 := by exact_mod_cast (by linarith : (k : ℝ) < 2)
  obtain rfl | rfl | rfl : k = -1 ∨ k = 0 ∨ k = 1 := by omega
  · left; exact eq_three_of_cos hn (by push_cast at hk; linarith)
  · right; left; exact eq_four_of_cos hn (by push_cast at hk; linarith)
  · right; right; exact eq_six_of_cos hn (by push_cast at hk; linarith)

/-- Fiche, théorème 3.3, sens difficile : si la rotation d'angle `±2π/n` (`n ≥ 3`) envoie un
vecteur non nul `p` de `ℤ²` sur un vecteur `q` de `ℤ²`, alors `n = 4`. Les vecteurs côtés
`w₀` et `w₁ = R w₀` d'un polygone régulier à sommets entiers sont de ce type.

La preuve diffère de la fiche : `cos θ` et `sin θ` sont rationnels (on résout le système), le
théorème de Niven de Mathlib donne `cos θ ∈ {0, ±1/2, ±1}`, et `cos θ = ±1/2` forcerait
`sin θ = ±√3/2` rationnel. L'argument de réseau et de trace (étape 2) n'est pas formalisé. -/
theorem rotation_entiere {n : ℕ} (hn : 3 ≤ n) {s : ℝ}
    (hs : s = sin (2 * π / n) ∨ s = -sin (2 * π / n)) {p₁ p₂ q₁ q₂ : ℤ}
    (hp : (p₁, p₂) ≠ (0, 0))
    (h₁ : (q₁ : ℝ) = p₁ * cos (2 * π / n) - p₂ * s)
    (h₂ : (q₂ : ℝ) = p₁ * s + p₂ * cos (2 * π / n)) : n = 4 := by
  set θ := 2 * π / n with hθ
  set N : ℤ := p₁ ^ 2 + p₂ ^ 2 with hN
  have hN0 : N ≠ 0 := by
    intro h0
    apply hp
    have : p₁ = 0 := by nlinarith [sq_nonneg p₁, sq_nonneg p₂]
    have : p₂ = 0 := by nlinarith [sq_nonneg p₁, sq_nonneg p₂]
    simp [*]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN0
  have hc : (N : ℝ) * cos θ = (p₁ * q₁ + p₂ * q₂ : ℤ) := by
    push_cast; rw [h₁, h₂, hN]; push_cast; ring
  have hsN : (N : ℝ) * s = (p₁ * q₂ - p₂ * q₁ : ℤ) := by
    push_cast; rw [h₁, h₂, hN]; push_cast; ring
  have hs2 : s ^ 2 = 1 - cos θ ^ 2 := by
    rcases hs with rfl | rfl <;> nlinarith [sin_sq_add_cos_sq θ]
  have hrat : ∃ r : ℚ, cos θ = r :=
    ⟨((p₁ * q₁ + p₂ * q₂ : ℤ) : ℚ) / N, by
      push_cast at hc ⊢; rw [eq_div_iff hNr]; linarith [hc]⟩
  have hniv := niven (θ := θ) ⟨2 / n, by rw [hθ]; push_cast; ring⟩ hrat
  obtain ⟨b1, b2⟩ := cos_two_pi_div_bounds hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hniv
  have half : ∀ c : ℝ, cos θ = c → c ^ 2 = 1 / 4 → False := by
    intro c hcθ hc2
    have key : (2 * (p₁ * q₂ - p₂ * q₁)) ^ 2 = (3 : ℕ) * N ^ 2 := by
      rw [hcθ, hc2] at hs2
      have : (2 * ((p₁ * q₂ - p₂ * q₁ : ℤ) : ℝ)) ^ 2 = (3 : ℝ) * (N : ℝ) ^ 2 := by
        rw [← hsN]; linear_combination (4 * (N : ℝ) ^ 2) * hs2
      exact_mod_cast this
    exact hN0 (sq_eq_mul_sq not_isSquare_three key).2
  rcases hniv with h | h | h | h | h
  · linarith
  · exact (half _ h (by norm_num)).elim
  · exact eq_four_of_cos hn h
  · exact (half _ h (by norm_num)).elim
  · linarith

/-- Fiche, théorème 3.3 : pour `n ≥ 3`, la rotation d'angle `2π/n` envoie un vecteur non nul de
`ℤ²` sur un vecteur de `ℤ²` si et seulement si `n = 4`. -/
theorem thm_3_3 {n : ℕ} (hn : 3 ≤ n) :
    (∃ p₁ p₂ q₁ q₂ : ℤ, (p₁, p₂) ≠ (0, 0) ∧
      (q₁ : ℝ) = p₁ * cos (2 * π / n) - p₂ * sin (2 * π / n) ∧
      (q₂ : ℝ) = p₁ * sin (2 * π / n) + p₂ * cos (2 * π / n)) ↔ n = 4 := by
  constructor
  · rintro ⟨p₁, p₂, q₁, q₂, hp, h₁, h₂⟩
    exact rotation_entiere hn (Or.inl rfl) hp h₁ h₂
  · rintro rfl
    have e : 2 * π / ((4 : ℕ) : ℝ) = π / 2 := by push_cast; ring
    refine ⟨1, 0, 0, 1, by simp, ?_, ?_⟩ <;> rw [e] <;> simp [cos_pi_div_two, sin_pi_div_two]

/-- La solution `(3, 2)` de `x² - 2y² = 1`. -/
def sol32 : Pell.Solution₁ 2 := Pell.Solution₁.mk 3 2 (by norm_num)

/-- Lien avec Mathlib (corollaire 2.6) : `3 + 2√2 = (1 + √2)²` est la solution fondamentale
(`Pell.IsFundamental`) de `x² - 2y² = 1`. -/
theorem isFundamental_sol32 : Pell.IsFundamental sol32 := by
  refine ⟨by simp [sol32, Pell.Solution₁.x_mk], by simp [sol32, Pell.Solution₁.y_mk],
    fun {b} hb => ?_⟩
  rw [sol32, Pell.Solution₁.x_mk]
  by_contra hc
  have h2 : b.x = 2 := by omega
  have hp := b.prop
  rw [h2] at hp
  generalize b.y ^ 2 = t at hp
  omega

/-- La solution `(2, 1)` de `x² - 3y² = 1`. -/
def sol21 : Pell.Solution₁ 3 := Pell.Solution₁.mk 2 1 (by norm_num)

/-- Fiche, exercice 2 : `2 + √3` est la solution fondamentale de `x² - 3y² = 1`. -/
theorem isFundamental_sol21 : Pell.IsFundamental sol21 := by
  refine ⟨by simp [sol21, Pell.Solution₁.x_mk], by simp [sol21, Pell.Solution₁.y_mk],
    fun {b} hb => ?_⟩
  rw [sol21, Pell.Solution₁.x_mk]
  omega

/-- Fiche, corollaire 2.6, solutions de norme `1`, via Mathlib : toute solution de `x² - 2y² = 1`
est `±(3 + 2√2)^n`, `n ∈ ℤ`. -/
theorem pell_deux (a : Pell.Solution₁ 2) : ∃ n : ℤ, a = sol32 ^ n ∨ a = -sol32 ^ n :=
  isFundamental_sol32.eq_zpow_or_neg_zpow a

/-- Fiche, exercice 2 : toutes les unités de `ℤ[√3]` sont de norme `1` (`x² ≢ 2 mod 3`). -/
theorem exercice_2_norme (z : ℤ√3) (hz : IsUnit z) : z.norm = 1 := by
  rw [Zsqrtd.isUnit_iff_norm_isUnit, Int.isUnit_iff] at hz
  rcases hz with h | h
  · exact h
  · exfalso
    rw [show z = ⟨z.re, z.im⟩ from rfl, norm_mk] at h
    have h3 : (z.re * z.re) % 3 = 2 := by
      rw [← sq]; generalize z.re ^ 2 = A at h; generalize z.im ^ 2 = B at h; omega
    rw [Int.mul_emod] at h3
    have : z.re % 3 = 0 ∨ z.re % 3 = 1 ∨ z.re % 3 = 2 := by omega
    rcases this with h' | h' | h' <;> rw [h'] at h3 <;> norm_num at h3

/-- Fiche, exercice 2 : `ℤ[√3]ˣ = {±(2 + √3)^n, n ∈ ℤ}`. -/
theorem exercice_2 (z : ℤ√3) (hz : IsUnit z) :
    ∃ n : ℤ, z = ((sol21 ^ n : Pell.Solution₁ 3) : ℤ√3) ∨
      z = -((sol21 ^ n : Pell.Solution₁ 3) : ℤ√3) := by
  have h := exercice_2_norme z hz
  rw [show z = ⟨z.re, z.im⟩ from rfl, norm_mk] at h
  obtain ⟨n, hn | hn⟩ := isFundamental_sol21.eq_zpow_or_neg_zpow (Pell.Solution₁.mk z.re z.im h)
  · refine ⟨n, Or.inl ?_⟩
    rw [← hn, Pell.Solution₁.coe_mk]
  · refine ⟨n, Or.inr ?_⟩
    have := congrArg (fun t : Pell.Solution₁ 3 => (t : ℤ√3)) hn
    simp only [Pell.Solution₁.coe_mk] at this
    rw [show z = ⟨z.re, z.im⟩ from rfl, this]
    rfl

/-- Auxiliaire de la proposition 2.11 : arrondi à l'entier le plus proche, `|u - mN| ≤ |N|/2`. -/
theorem round_aux (u N : ℤ) (hN : N ≠ 0) : ∃ m : ℤ, 4 * (u - m * N) ^ 2 ≤ N ^ 2 := by
  refine ⟨round ((u : ℚ) / N), ?_⟩
  have h := abs_sub_round ((u : ℚ) / N)
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  set t : ℚ := (u : ℚ) / N - round ((u : ℚ) / N) with ht
  have e : (u : ℚ) - round ((u : ℚ) / N) * N = N * t := by
    rw [ht]; field_simp
  have ht2 : t ^ 2 ≤ 1 / 4 := by
    rw [← sq_abs]; nlinarith [abs_nonneg t]
  have : 4 * ((u : ℚ) - round ((u : ℚ) / N) * N) ^ 2 ≤ (N : ℚ) ^ 2 := by
    rw [e, mul_pow]; nlinarith [mul_le_mul_of_nonneg_left ht2 (sq_nonneg (N : ℚ))]
  exact_mod_cast this

/-- `2` n'est pas un carré dans `ℤ`. -/
theorem two_ne_mul_self (n : ℤ) : (2 : ℤ) ≠ n * n := by
  intro h
  have h1 : n ≤ 1 := by nlinarith
  have h2 : -1 ≤ n := by nlinarith
  interval_cases n <;> omega

/-- Fiche, proposition 2.11 : division euclidienne dans `ℤ[√2]` pour le stathme `|N|`. -/
theorem prop_2_11 (x y : ℤ√2) (hy : y ≠ 0) :
    ∃ q r : ℤ√2, x = q * y + r ∧ |r.norm| < |y.norm| := by
  set N := y.norm with hNdef
  have hN : N ≠ 0 := fun h => hy ((Zsqrtd.norm_eq_zero two_ne_mul_self y).1 h)
  set w := x * star y with hw
  obtain ⟨m, hm⟩ := round_aux w.re N hN
  obtain ⟨n, hn⟩ := round_aux w.im N hN
  set q : ℤ√2 := ⟨m, n⟩ with hq
  set r := x - q * y with hr
  refine ⟨q, r, by rw [hr]; ring, ?_⟩
  set s := w.re - m * N
  set t := w.im - n * N
  have e1 : r * star y = w - q * (N : ℤ√2) := by
    rw [hNdef, Zsqrtd.norm_eq_mul_conj, hr, hw]; ring
  have e2 : w - q * (N : ℤ√2) = ⟨s, t⟩ := by
    ext <;> simp [hq] <;> ring
  have P : r.norm * N = s ^ 2 - 2 * t ^ 2 := by
    rw [hNdef, ← Zsqrtd.norm_conj y, ← Zsqrtd.norm_mul, e1, e2, norm_mk]
  have hA : |2 * (s ^ 2 - 2 * t ^ 2)| ≤ N ^ 2 :=
    abs_le.2 ⟨by nlinarith [sq_nonneg s, sq_nonneg t], by nlinarith [sq_nonneg s, sq_nonneg t]⟩
  rw [abs_mul, abs_two, ← P, abs_mul, ← sq_abs N] at hA
  nlinarith [abs_pos.2 hN, abs_nonneg r.norm]

/-- Fiche, exercice 3 : `n(n+1)/2 = m²` équivaut à `(2n+1)² - 2(2m)² = 1`. -/
theorem exercice_3 (n m : ℤ) : n * (n + 1) = 2 * m ^ 2 ↔ (2 * n + 1) ^ 2 - 2 * (2 * m) ^ 2 = 1 := by
  constructor <;> intro h <;> nlinarith

end EntiersQuadratiques

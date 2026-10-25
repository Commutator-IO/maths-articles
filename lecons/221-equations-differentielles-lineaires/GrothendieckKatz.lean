import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.NoncommRing

/-!
# La $p$-courbure, et la conjecture de Grothendieck–Katz dans deux cas simples

Formalisation d'une partie de la section 8 de la note « Crochet de Lie et équations
différentielles linéaires » (M. Hua, octobre 2026), fichier `crochet-lie-edo.tex` du même
dossier. La conjecture elle-même est ouverte ; on vérifie ici les calculs en caractéristique `p`
et les deux cas simples de la note : les coefficients constants, et l'équation `y' = (λ/x) y`.

## Modèles

* **Dérivations en caractéristique `p`** (lemme 8.1). Un anneau commutatif `R` avec `CharP R p`,
  et une dérivation `D : Derivation ℤ R R`, vue comme application `R → R` que l'on itère. Sur
  les polynômes, `Polynomial.derivative`.
* **Le crochet en caractéristique `p`** (lemme 8.2). Un anneau quelconque `A` avec `CharP A p` ;
  `ad X` est l'application `Y ↦ X * Y - Y * X`.
* **Coefficients constants** (proposition 8.8, théorème 8.11). Deux éléments qui commutent dans
  un anneau de caractéristique `p`, et des matrices à coefficients entiers réduites modulo `p`
  par `Matrix.map` et `Int.castRingHom (ZMod p)`. Les matrices de la note sont rationnelles ; on
  se ramène aux entiers en multipliant par un dénominateur commun, ce qui ne change ni la
  nilpotence ni la nullité de `A^p` modulo presque tout `p`.
* **L'ordre 1, avec l'opérateur d'Euler** (théorème 8.15 pour `a = λ/x`, exemple 8.16). D'abord
  dans un anneau `A` quelconque (non commutatif) : deux éléments `x` et `D` avec `[D, x] = 1`,
  et `θ = xD`. On montre `xⁿ Dⁿ = θ(θ − 1)⋯(θ − n + 1)`, d'où `xᵖ Dᵖ = θᵖ − θ` en
  caractéristique `p`, puisque `t(t − 1)⋯(t − p + 1) = tᵖ − t` dans `𝔽_p[t]`. Pour
  `L = D − c x⁻¹`, avec `c` qui commute à `x` et à `D`, le couple `(x, L)` vérifie encore
  `[L, x] = 1` et `xL = θ − c` : la même formule donne `(D − c/x)ᵖ = Dᵖ − (cᵖ − c)/xᵖ`.
  Ensuite dans un modèle concret : les opérateurs `ℤ`-linéaires sur les séries de Laurent
  `K((x))` (`LaurentSeries K`), pour un anneau commutatif `K` de caractéristique `p`, avec la
  dérivée `LaurentSeries.derivative` et les multiplications par `x`, `x⁻¹` et `λ ∈ K`.

## Écarts avec la note

* La note travaille sur le corps `𝔽_p(x)` des fractions rationnelles. Mathlib n'y définit pas de
  dérivation ; on se place sur les séries de Laurent `K((x))`, qui contiennent les fractions
  rationnelles sans pôle en dehors de `0`, en particulier `λ/x` et `x⁻ᵖ`. C'est assez pour
  l'équation `y' = (λ/x) y`.
* Pour l'ordre 1, la note passe par la formule de Jacobson (proposition 8.12) et le calcul de
  `Ψ` sur les éléments simples (lemme 8.14). Ici, pour `a = λ/x`, on calcule directement avec
  l'opérateur d'Euler : `xᵖ (D − λ/x)ᵖ = (θ − λ)ᵖ − (θ − λ) = θᵖ − θ − (λᵖ − λ)`. On retrouve
  `ψ_p = −Ψ(λ/x) = −(λᵖ − λ)/xᵖ`, nulle quand `λ ∈ 𝔽_p` (petit théorème de Fermat), donc pour
  presque tout `p` quand `λ` est rationnel.
* La note compte `Dᵖ = 0` dans la `p`-courbure ; les énoncés abstraits gardent le terme `Dᵖ`,
  et le modèle de Laurent l'annule (`Dx_pow_char`).
* Les autres énoncés vérifiés ici sont corrects tels qu'écrits.

## Omis

Le théorème de descente de Cartier (admis dans la note) ; le lemme 8.10 (`e^{λx}` n'est pas
algébrique), qui demande une comparaison de croissances à l'infini, et donc le sens 1 ⇔ 2 du
théorème 8.11 ; la formule de Jacobson générale (proposition 8.12) et le lemme 8.14 sur les
pôles multiples, donc le théorème 8.15 au-delà de `a = λ/x` ; la conjecture générale. Ce sont
les ouvertures naturelles de ce fichier.
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
  have key : (⇑D)^[n] (f * g) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : R) * ((⇑D)^[ij.1] f * (⇑D)^[ij.2] g) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_antidiagonal_choose_succ_mul (fun i j => (⇑D)^[i] f * (⇑D)^[j] g),
        Function.iterate_succ_apply', ih, map_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ij hij => ?_
      have h : n.choose ij.2 = n.choose ij.1 :=
        (Nat.choose_symm_of_eq_add (Finset.HasAntidiagonal.mem_antidiagonal.mp hij).symm).symm
      simp only [Function.iterate_succ_apply', h]
      rw [← nsmul_eq_mul, map_nsmul, Derivation.leibniz, nsmul_eq_mul, smul_eq_mul, smul_eq_mul]
      ring
  rw [key, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

variable (p : ℕ) [hp : Fact p.Prime] [CharP R p]

/-- **Lemme 8.1 (2)** : en caractéristique `p`, `Dᵖ` est encore une dérivation. -/
theorem iterate_char_leibniz (D : Derivation ℤ R R) (f g : R) :
    (⇑D)^[p] (f * g) = f * (⇑D)^[p] g + g * (⇑D)^[p] f := by
  rw [iterate_leibniz, Finset.sum_eq_add_of_mem 0 p (by simp) (by simp) (Nat.Prime.ne_zero hp.out).symm]
  · simp only [Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_zero,
      Nat.sub_self, Function.iterate_zero, id_eq]
    ring
  · intro k hk hk'
    have : (p.choose k : R) = 0 :=
      (CharP.cast_eq_zero_iff R p _).mpr
        (Nat.Prime.dvd_choose_self hp.out hk'.1 (by simp at hk; omega))
    rw [this, zero_mul]

end Derivations

/-- **Lemme 8.1 (3)**, sur les polynômes : la dérivée `p`-ième est nulle sur `𝔽_p[x]`. -/
theorem iterate_derivative_char_eq_zero (p : ℕ) [hp : Fact p.Prime] (f : (ZMod p)[X]) :
    derivative^[p] f = 0 := by
  ext m
  rw [coeff_iterate_derivative, coeff_zero, nsmul_eq_mul]
  have : ((m + p).descFactorial p : ZMod p) = 0 :=
    (CharP.cast_eq_zero_iff (ZMod p) p _).mpr
      ((Nat.dvd_factorial (Nat.Prime.pos hp.out) le_rfl).trans (Nat.factorial_dvd_descFactorial _ _))
  rw [this, zero_mul]

/-! ## Le crochet en caractéristique `p` -/

section Bracket

variable {A : Type*} [Ring A] (p : ℕ) [Fact p.Prime] [CharP A p]

omit [Fact p.Prime] in
/-- Les endomorphismes du groupe additif d'un anneau de caractéristique `p` forment encore un
anneau de caractéristique `p`. -/
theorem charP_end (M : Type*) [Ring M] [CharP M p] : CharP (Module.End ℤ M) p :=
  ⟨fun k => by
    rw [← CharP.cast_eq_zero_iff M p k]
    constructor
    · intro h
      simpa using LinearMap.congr_fun h 1
    · intro h
      ext Y
      simp [Module.End.natCast_apply, nsmul_eq_mul, h]⟩

/-- `ad X : Y ↦ XY − YX`. -/
def ad (X : A) : A → A := fun Y => X * Y - Y * X

/-- **Lemme 8.2** : `ad_Xᵖ (Y) = [Xᵖ, Y]` en caractéristique `p`. -/
theorem ad_iterate_char (X Y : A) : (ad X)^[p] Y = X ^ p * Y - Y * X ^ p := by
  have := charP_end p A
  have h : ad X = ⇑(LinearMap.mulLeft ℤ X - LinearMap.mulRight ℤ X) := by
    funext Y
    simp [ad]
  rw [h, ← Module.End.coe_pow,
    sub_pow_char_of_commute p (LinearMap.commute_mulLeft_right X X),
    LinearMap.pow_mulLeft, LinearMap.pow_mulRight]
  simp

/-- **Proposition 8.4**, forme abstraite : si `ad_∇ᵖ (M) = 0`, alors `∇ᵖ` commute avec `M`. C'est
l'argument qui rend la `p`-courbure linéaire (avec `ad_∇ (M_f) = M_{f'}` et `Dᵖ f = 0`). -/
theorem commute_pow_of_ad_iterate_eq_zero (X Y : A) (h : (ad X)^[p] Y = 0) :
    Commute (X ^ p) Y :=
  sub_eq_zero.mp ((ad_iterate_char p X Y).symm.trans h)

/-- **Proposition 8.8** : si `D` et `A` commutent, `(D − A)ᵖ = Dᵖ − Aᵖ` en caractéristique `p`.
Avec `Dᵖ = 0`, la `p`-courbure d'un système à coefficients constants est `−Aᵖ`. -/
theorem sub_pow_of_commute (D M : A) (h : Commute D M) : (D - M) ^ p = D ^ p - M ^ p :=
  sub_pow_char_of_commute p h

end Bracket

/-! ## 8.3. Coefficients constants -/

section Constant

variable {n : ℕ}

/-- La réduction modulo `p` d'une matrice à coefficients entiers. -/
abbrev red (p : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) (ZMod p) :=
  A.map (Int.castRingHom (ZMod p))

/-- Sur un anneau intègre, une matrice nilpotente a pour polynôme caractéristique `tⁿ`. -/
theorem charpoly_eq_X_pow {K : Type*} [CommRing K] [IsDomain K]
    {M : Matrix (Fin n) (Fin n) K} (hM : IsNilpotent M) : M.charpoly = X ^ n := by
  simpa [sub_eq_zero] using (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hM).eq_zero

/-- Et donc, par Cayley–Hamilton, `Mⁿ = 0`. -/
theorem pow_eq_zero_of_isNilpotent {K : Type*} [CommRing K] [IsDomain K]
    {M : Matrix (Fin n) (Fin n) K} (hM : IsNilpotent M) : M ^ n = 0 := by
  simpa [charpoly_eq_X_pow hM] using Matrix.aeval_self_charpoly M

/-- **Théorème 8.11, 2 ⇒ 3** : si `A` est nilpotente, `(A mod p)ᵖ = 0` pour tout `p ≥ n`. -/
theorem red_pow_eq_zero_of_isNilpotent (A : Matrix (Fin n) (Fin n) ℤ) (hA : IsNilpotent A)
    (p : ℕ) (hp : n ≤ p) : red p A ^ p = 0 := by
  have hn : red p A ^ n = 0 := by
    rw [red, ← RingHom.mapMatrix_apply, ← map_pow, RingHom.mapMatrix_apply,
      pow_eq_zero_of_isNilpotent hA]
    simp
  calc red p A ^ p = red p A ^ n * red p A ^ (p - n) := by rw [← pow_add, Nat.add_sub_cancel' hp]
    _ = 0 := by rw [hn, zero_mul]

/-- **Théorème 8.11, 4 ⇒ 2** : si `(A mod p)ᵖ = 0` pour une infinité de nombres premiers `p`,
alors `A` est nilpotente. Preuve de la note : le polynôme caractéristique de `A mod p` est `tⁿ`,
c'est la réduction de celui de `A`, dont les coefficients non dominants sont donc divisibles par
une infinité de nombres premiers, donc nuls ; puis Cayley–Hamilton. -/
theorem isNilpotent_of_frequently (A : Matrix (Fin n) (Fin n) ℤ)
    (h : ∀ N : ℕ, ∃ p, N < p ∧ p.Prime ∧ red p A ^ p = 0) : IsNilpotent A := by
  have key : A.charpoly - X ^ n = 0 := by
    ext i
    rw [coeff_zero]
    obtain ⟨p, hNp, hp, hpow⟩ := h ((A.charpoly - X ^ n).coeff i).natAbs
    have := Fact.mk hp
    have hred := charpoly_eq_X_pow (⟨p, hpow⟩ : IsNilpotent (red p A))
    rw [red, Matrix.charpoly_map] at hred
    have hc : ((A.charpoly - X ^ n).map (Int.castRingHom (ZMod p))).coeff i = 0 := by
      rw [Polynomial.map_sub, hred, Polynomial.map_pow, map_X, sub_self, coeff_zero]
    rw [coeff_map, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at hc
    exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hc (by simpa using hNp)
  refine ⟨n, ?_⟩
  simpa [sub_eq_zero.mp key] using Matrix.aeval_self_charpoly A

/-- **Théorème 8.11, 2 ⇔ 4** : nilpotence et annulation de `(A mod p)ᵖ` pour une infinité
de `p`. -/
theorem isNilpotent_iff_frequently (A : Matrix (Fin n) (Fin n) ℤ) :
    IsNilpotent A ↔ ∀ N : ℕ, ∃ p, N < p ∧ p.Prime ∧ red p A ^ p = 0 := by
  refine ⟨fun hA N => ?_, isNilpotent_of_frequently A⟩
  obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes (max N n + 1)
  exact ⟨p, by omega, hp2, red_pow_eq_zero_of_isNilpotent A hA p (by omega)⟩

/-- **Exemple 8.9** : pour `y' = y`, `A = (1)` et `(A mod p)ᵖ = 1 ≠ 0` pour tout `p` premier. -/
theorem exp_pCurvature_ne_zero (p : ℕ) [Fact p.Prime] :
    red p (1 : Matrix (Fin 1) (Fin 1) ℤ) ^ p ≠ 0 := by
  simp [red, Matrix.map_one]

/-- **Exercice 6** : pour `y'' + y = 0`, `A = [[0,1],[-1,0]]` vérifie `A² = −1`, donc `Aᵖ = ± A`
n'est jamais nul modulo un premier impair. -/
theorem rotation_pCurvature_ne_zero (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    red p !![0, 1; -1, 0] ^ p ≠ 0 := by
  set M := red p !![0, 1; -1, 0]
  have hM : M * M = -1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [M, Matrix.mul_apply, Fin.sum_univ_two]
  have h01 : M 0 1 = 1 := by simp [M]
  obtain ⟨k, hk⟩ := (Nat.Prime.eq_two_or_odd' hp.out).resolve_left hp2
  intro h
  replace h : M ^ (2 * k + 1) = 0 := by rwa [← hk]
  rw [pow_succ, pow_mul, sq, hM] at h
  rcases neg_one_pow_eq_or (Matrix (Fin 2) (Fin 2) (ZMod p)) k with h1 | h1 <;>
    · have := congrFun (congrFun h 0) 1
      simp [h1, h01] at this

end Constant

/-! ## 8.4. L'ordre 1 : l'opérateur d'Euler -/

/-- En caractéristique `p`, `x(x − 1)⋯(x − p + 1) = xᵖ − x` : les racines sont les `p`
éléments de `𝔽_p` (petit théorème de Fermat). -/
theorem descPochhammer_zmod (p : ℕ) [hp : Fact p.Prime] :
    descPochhammer (ZMod p) p = X ^ p - X := by
  set q := descPochhammer (ZMod p) p - (X ^ p - X)
  have hdeg : q.natDegree < p := by
    refine IsMonicOfDegree.natDegree_sub_lt (Nat.Prime.ne_zero hp.out)
      ⟨descPochhammer_natDegree _ _, monic_descPochhammer _ _⟩ ?_
    rw [sub_eq_add_neg]
    exact (isMonicOfDegree_X_pow (ZMod p) p).add_right (by simpa using Nat.Prime.one_lt hp.out)
  have hq : q = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' q Finset.univ
      (fun a _ => ?_) (by simpa [ZMod.card] using hdeg)
    rw [eval_sub, descPochhammer_eval_eq_prod_range, Finset.prod_eq_zero
      (Finset.mem_range.2 (ZMod.val_lt a)) (by rw [ZMod.natCast_zmod_val, sub_self])]
    simp [ZMod.pow_card]
  exact sub_eq_zero.mp hq

section Euler

variable {A : Type*} [Ring A]

/-- Le crochet `[θ, x] = x`, sous la forme `xⁿ θ = (θ − n) xⁿ`, où `θ = xD`. -/
theorem pow_mul_euler {x D : A} (h : D * x - x * D = 1) (n : ℕ) :
    x ^ n * (x * D) = (x * D - n) * x ^ n := by
  have h1 : x * (x * D) = (x * D - 1) * x := by
    have : D * x = x * D + 1 := by rw [← h]; abel
    calc x * (x * D) = x * (D * x) - x := by rw [this]; noncomm_ring
      _ = (x * D - 1) * x := by noncomm_ring
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_assoc, ih, ← mul_assoc, mul_sub, h1, Nat.cast_succ,
      ← (Nat.cast_commute n x).eq]
    noncomm_ring

/-- `xⁿ Dⁿ = θ(θ − 1)⋯(θ − n + 1)` dès que `[D, x] = 1`. -/
theorem pow_mul_pow_eq_descPochhammer {x D : A} (h : D * x - x * D = 1) (n : ℕ) :
    x ^ n * D ^ n = aeval (x * D) (descPochhammer ℤ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [descPochhammer_succ_right, mul_comm (descPochhammer ℤ n), map_mul, ← ih, map_sub,
      aeval_X, map_natCast, pow_succ, pow_succ', mul_assoc, ← mul_assoc x D,
      ← mul_assoc (x ^ n), pow_mul_euler h n, mul_assoc]

variable (p : ℕ) [Fact p.Prime] [CharP A p]

/-- **En caractéristique `p`** : `xᵖ Dᵖ = θᵖ − θ` dès que `[D, x] = 1`. -/
theorem pow_mul_pow_char {x D : A} (h : D * x - x * D = 1) :
    x ^ p * D ^ p = (x * D) ^ p - x * D := by
  have hcomp : Int.castRingHom A = (ZMod.castHom (dvd_refl p) A).comp (Int.castRingHom (ZMod p)) :=
    RingHom.ext_int _ _
  rw [pow_mul_pow_eq_descPochhammer h, aeval_def, algebraMap_int_eq, hcomp, ← eval₂_map,
    descPochhammer_map, descPochhammer_zmod]
  simp

/-- Pour `L = D − c x⁻¹`, avec `c` qui commute à `x` et `D` : `xᵖ Lᵖ = xᵖ Dᵖ − (cᵖ − c)`.
Le couple `(x, L)` vérifie encore `[L, x] = 1`, et son opérateur d'Euler est `xL = θ − c`. -/
theorem pow_mul_pow_sub_char {x D xinv c : A} (h : D * x - x * D = 1) (hx : x * xinv = 1)
    (hx' : xinv * x = 1) (hcx : Commute c x) (hcD : Commute c D) :
    x ^ p * (D - c * xinv) ^ p = x ^ p * D ^ p - (c ^ p - c) := by
  have h1 : (D - c * xinv) * x - x * (D - c * xinv) = 1 := by
    rw [sub_mul, mul_sub, mul_assoc, hx', ← mul_assoc x, ← hcx.eq, mul_assoc, hx, ← h]
    noncomm_ring
  have h2 : x * (D - c * xinv) = x * D - c := by
    rw [mul_sub, ← mul_assoc, ← hcx.eq, mul_assoc, hx, mul_one]
  rw [pow_mul_pow_char p h1, h2, pow_mul_pow_char p h,
    sub_pow_char_of_commute p ((hcx.symm.mul_left hcD.symm))]
  abel

/-- **La `p`-courbure de `D − c/x`** : `(D − c x⁻¹)ᵖ = Dᵖ − x⁻ᵖ (cᵖ − c)`. Sur un corps où
`Dᵖ = 0`, elle vaut `−(cᵖ − c)/xᵖ`. -/
theorem pCurvature_euler {x D xinv c : A} (h : D * x - x * D = 1) (hx : x * xinv = 1)
    (hx' : xinv * x = 1) (hcx : Commute c x) (hcD : Commute c D) :
    (D - c * xinv) ^ p = D ^ p - xinv ^ p * (c ^ p - c) := by
  have hinv : xinv ^ p * x ^ p = 1 := by
    rw [← (show Commute xinv x from hx'.trans hx.symm).mul_pow, hx', one_pow]
  calc (D - c * xinv) ^ p = xinv ^ p * (x ^ p * (D - c * xinv) ^ p) := by
        rw [← mul_assoc, hinv, one_mul]
    _ = D ^ p - xinv ^ p * (c ^ p - c) := by
        rw [pow_mul_pow_sub_char p h hx hx' hcx hcD, mul_sub, ← mul_assoc, hinv, one_mul]

/-- **Théorème 8.15, sens 2 ⇒ 3, pour `a = λ/x`**, forme abstraite : pour `λ ∈ 𝔽_p`,
`(D − λ/x)ᵖ = Dᵖ` (petit théorème de Fermat, `λᵖ = λ`). -/
theorem pCurvature_euler_zmod {x D xinv : A} (h : D * x - x * D = 1) (hx : x * xinv = 1)
    (hx' : xinv * x = 1) (l : ZMod p) :
    (D - ZMod.castHom (dvd_refl p) A l * xinv) ^ p = D ^ p := by
  have hc : ∀ a : A, Commute (ZMod.castHom (dvd_refl p) A l) a := fun a => by
    rw [← ZMod.natCast_zmod_val l, map_natCast]
    exact Nat.cast_commute _ a
  rw [pCurvature_euler p h hx hx' (hc x) (hc D), ← map_pow, ZMod.pow_card, sub_self, mul_zero,
    sub_zero]

end Euler

/-! ### Le modèle : séries de Laurent en caractéristique `p` -/

section Laurent

variable (p : ℕ) [Fact p.Prime] (K : Type*) [CommRing K] [CharP K p]

/-- La multiplication par une série de Laurent `f`, vue comme opérateur. -/
abbrev mul (f : LaurentSeries K) : Module.End ℤ (LaurentSeries K) := LinearMap.mulLeft ℤ f

/-- La dérivation `D` des séries de Laurent `K((x))`. -/
abbrev Dx : Module.End ℤ (LaurentSeries K) := LaurentSeries.derivative ℤ

/-- La multiplication par `x`. -/
abbrev mulX : Module.End ℤ (LaurentSeries K) := mul K (HahnSeries.single 1 1)

/-- La multiplication par `x⁻¹`. -/
abbrev mulXinv : Module.End ℤ (LaurentSeries K) := mul K (HahnSeries.single (-1) 1)

/-- La relation fondamentale `[D, x] = 1` (proposition 2.3). -/
theorem Dx_mulX : Dx K * mulX K - mulX K * Dx K = 1 := by
  ext f n
  simp [HahnSeries.coeff_single_mul]
  ring

theorem mulX_mulXinv : mulX K * mulXinv K = 1 := by
  ext f : 1
  simp [← mul_assoc, HahnSeries.single_mul_single]

theorem mulXinv_mulX : mulXinv K * mulX K = 1 := by
  ext f : 1
  simp [← mul_assoc, HahnSeries.single_mul_single]

/-- Une constante `λ` commute avec `x`… -/
theorem commute_C_mulX (l : K) : Commute (mul K (HahnSeries.C l)) (mulX K) := by
  ext f : 1
  simp only [Module.End.mul_apply, LinearMap.mulLeft_apply]
  exact mul_left_comm _ _ _

/-- … et avec `D` : `(λf)' = λf'`. -/
theorem commute_C_Dx (l : K) : Commute (mul K (HahnSeries.C l)) (Dx K) := by
  ext f n
  simp [HahnSeries.C_apply]
  ring

omit [Fact p.Prime] in
theorem charP_laurent : CharP (LaurentSeries K) p :=
  charP_of_injective_ringHom HahnSeries.C_injective p

/-- **Lemme 8.1 (3)** pour les séries de Laurent : `Dᵖ = 0`, car `Dᵖ = p! · D^{[p]}`, où
`D^{[p]}` est la dérivée de Hasse (`LaurentSeries.derivative_iterate`). -/
theorem Dx_pow_char : Dx K ^ p = 0 := by
  have := charP_laurent p K
  ext f : 1
  rw [Module.End.pow_apply, LaurentSeries.derivative_iterate, nsmul_eq_mul,
    (CharP.cast_eq_zero_iff (LaurentSeries K) p _).mpr
      (Nat.dvd_factorial (Fact.out : p.Prime).pos le_rfl),
    zero_mul, LinearMap.zero_apply]

/-- **L'opérateur d'Euler en caractéristique `p`** : sur `K((x))`, `θᵖ = θ`. -/
theorem euler_pow_char : (mulX K * Dx K) ^ p = mulX K * Dx K := by
  have := charP_laurent p K
  have := charP_end p (LaurentSeries K)
  have h := pow_mul_pow_char p (Dx_mulX K)
  rw [Dx_pow_char p K, mul_zero] at h
  exact (sub_eq_zero.mp h.symm)

/-- **La `p`-courbure de `y' = (λ/x) y`** sur `K((x))` : `(D − λx⁻¹)ᵖ = −(λᵖ − λ) x⁻ᵖ`, soit
`ψ_p = −Ψ(λ/x)` avec les notations du §8.4. Elle n'est pas nulle si `λᵖ ≠ λ`, par exemple pour
`λ ∈ 𝔽_{p²} \ 𝔽_p`. -/
theorem pCurvature_laurent (l : K) :
    (Dx K - mul K (HahnSeries.single (-1) l)) ^ p =
      -mul K (HahnSeries.single (-(p : ℤ)) (l ^ p - l)) := by
  have := charP_laurent p K
  have := charP_end p (LaurentSeries K)
  have e : mul K (HahnSeries.single (-1) l) = mul K (HahnSeries.C l) * mulXinv K := by
    ext f : 1
    simp [← mul_assoc, HahnSeries.C_apply, HahnSeries.single_mul_single]
  rw [e, pCurvature_euler p (Dx_mulX K) (mulX_mulXinv K) (mulXinv_mulX K) (commute_C_mulX K l)
    (commute_C_Dx K l), Dx_pow_char p K, zero_sub, LinearMap.pow_mulLeft, LinearMap.pow_mulLeft]
  congr 1
  ext f : 1
  simp only [Module.End.mul_apply, LinearMap.mulLeft_apply, LinearMap.sub_apply]
  rw [← sub_mul, ← mul_assoc, HahnSeries.single_pow, ← map_pow, ← map_sub, HahnSeries.C_apply,
    HahnSeries.single_mul_single]
  congr 2 <;> simp

/-- **Théorème 8.15, sens 2 ⇒ 3, pour `a = λ/x`, et exemple 8.16** : si `λ ∈ 𝔽_p`, la
`p`-courbure de `y' = (λ/x) y` est nulle (petit théorème de Fermat). Pour `λ = r/s` rationnel,
on l'applique à `λ mod p` pour tout `p` qui ne divise pas `s` : `ψ_p = 0` pour presque tout `p`,
et en effet `x^λ` est algébrique. -/
theorem pCurvature_laurent_zmod (l : ZMod p) :
    (Dx (ZMod p) - mul (ZMod p) (HahnSeries.single (-1) l)) ^ p = 0 := by
  rw [pCurvature_laurent p, ZMod.pow_card, sub_self, HahnSeries.single_eq_zero]
  simp

end Laurent

end GrothendieckKatz

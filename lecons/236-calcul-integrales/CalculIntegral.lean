import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Real.Irrational

/-!
# Méthodes de calcul d'intégrales

Formalisation de la fiche « Méthodes de calcul d'intégrales. Que faire quand on ne connaît pas de
primitive ? » (M. Hua, octobre 2026, leçon 236). Les numéros cités (exemple 1.1, théorème 1.3…)
sont ceux de la fiche.

## Modèles

* **Intégrales.** Toutes les intégrales de la fiche sont sur un segment ; elles sont écrites
  comme intégrales orientées `∫ x in a..b, f x` (`intervalIntegral`). Les intégrales généralisées
  de la fiche (`∫₀¹ t^s ln^k t`, `∫₀¹ x^{−x}`) sont aussi écrites ainsi : leur intégrande se
  prolonge par continuité en `0`, et Mathlib pose `log 0 = 0` et `0 ^ 0 = 1`, ce qui donne
  directement la bonne valeur au point `0`.
* **Suites.** Les suites de la fiche sont des fonctions `ℕ → ℝ` : `W` (Wallis, §1), `I` (§3),
  `fD n` (la somme `f_n` du §4), `R` (§6). Une série `Σ_{n ≥ 1}` est écrite `HasSum` sur `ℕ`,
  indexée à partir de `0` (terme `n + 1`).
* **Équivalents et limites.** `u ~ v` est `Asymptotics.IsEquivalent atTop u v`, et une limite est
  un `Tendsto … atTop (𝓝 ℓ)`.
* **Lien avec Mathlib.** Mathlib connaît déjà le produit de Wallis (`Real.Wallis`,
  `Real.tendsto_prod_pi_div_two`), la formule de Stirling (`Stirling.factorial_isEquivalent_stirling`)
  et `ζ(2) = π²/6` (`hasSum_zeta_two`). Le fichier réutilise les deux premiers pour le
  théorème 1.3, 4 et la proposition 1.5, et les relie aux énoncés de la fiche
  (`wallis_W_eq`, `stirling_constant`). Pour `ζ(2)`, il donne une preuve indépendante qui suit la
  fiche (noyau de Dirichlet, Riemann–Lebesgue), puis constate qu'elle établit l'énoncé de Mathlib
  (`zeta_two_eq_mathlib`). L'irrationalité de `e` est démontrée par l'argument de la fiche.

## Écarts avec la fiche

* **Proposition 2.3** : seul le cas `s = m ∈ ℕ`, `k ≤ m` est démontré (`moments_log`), par
  intégrations par parties successives et non par dérivation sous l'intégrale. C'est le cas qui
  sert au théorème 2.5. Le cas d'un réel `s > −1` quelconque n'est pas formalisé.
* **Théorème 2.5** : l'interversion série-intégrale est justifiée par convergence dominée
  (`intervalIntegral.hasSum_integral_of_dominated_convergence`), avec la majoration
  `|x ln x| ≤ 1` au lieu de `|x ln x| ≤ 1/e` ; la fiche invoque la convergence normale. Les deux
  arguments sont valables.
* **Lemme 4.4** : la fonction `h` est supposée dérivable au sens de `HasDerivAt` en tout point de
  `[α, β]`, de dérivée continue sur `[α, β]`. C'est un peu plus que « `C¹` sur le segment » (la
  dérivée aux bornes est bilatérale), et c'est ce que donne la preuve du théorème 4.5, où `h` est
  `C¹` sur `]−2π, 2π[`.
* **Théorème 4.5** : la fonction `h = φ/(2 sin(x/2))` est écrite
  `h(x) = (x − 2π)/(2π) / sinc(x/2)` avec le sinus cardinal de Mathlib, ce qui est la
  factorisation de la fiche et règle le prolongement en `0`.
* **Proposition 6.1**, 3 : l'encadrement strict est démontré pour tout `n ∈ ℕ`, y compris
  `n = 0`, alors que la fiche le demande pour `n ≥ 1`.
* Aucun énoncé de la fiche ne s'est révélé faux.

## Omis

La proposition 5.2 (erreur des méthodes des trapèzes et du point milieu) et la remarque 5.3
(Simpson) ; la remarque 3.4 (stabilité numérique), qui porte sur l'arithmétique flottante ; la
remarque 1.6 (`binom(2p, p) ~ 4^p/√(πp)`) ; la remarque 4.6 (lecture par les séries de Fourier) ;
la proposition 2.3 pour `s` réel ; les exercices et leurs corrigés.
-/

open Real Filter Topology Finset intervalIntegral Asymptotics
open scoped Nat

noncomputable section

namespace CalculIntegral

/-! ## §1. Calculs directs, intégrales de Wallis, constante de Stirling -/

/-- Intégrale d'une fonction affine (outil pour les exemples 1.1 et la proposition 5.1). -/
theorem integral_affine (a b u v : ℝ) :
    ∫ x in u..v, (a + b * x) = a * (v - u) + b * (v ^ 2 - u ^ 2) / 2 := by
  have hd : ∀ x ∈ Set.uIcc u v, HasDerivAt (fun x => a * x + b * x ^ 2 / 2) (a + b * x) x := by
    intro x _
    convert ((hasDerivAt_id' x).const_mul a).add
      (((hasDerivAt_pow 2 x).const_mul b).div_const 2) using 1
    norm_num; ring
  rw [integral_eq_sub_of_hasDerivAt hd (by apply Continuous.intervalIntegrable; fun_prop)]; ring

/-- **Exemple 1.1** : `∫₀⁴ (|x − 1| + |x − 2|) dx = 9`. -/
theorem exemple_1_1 : ∫ x in (0:ℝ)..4, (|x - 1| + |x - 2|) = 9 := by
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun x => |x - 1| + |x - 2|) MeasureTheory.volume a b :=
    fun a b => (by fun_prop : Continuous fun x : ℝ => |x - 1| + |x - 2|).intervalIntegrable a b
  have h01 : ∫ x in (0:ℝ)..1, (|x - 1| + |x - 2|) = ∫ x in (0:ℝ)..1, (3 + (-2) * x) := by
    refine integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hx
    rw [abs_of_nonpos (by linarith [hx.2]), abs_of_nonpos (by linarith [hx.2])]; ring
  have h12 : ∫ x in (1:ℝ)..2, (|x - 1| + |x - 2|) = ∫ x in (1:ℝ)..2, (1 + 0 * x) := by
    refine integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hx
    rw [abs_of_nonneg (by linarith [hx.1]), abs_of_nonpos (by linarith [hx.2])]; ring
  have h24 : ∫ x in (2:ℝ)..4, (|x - 1| + |x - 2|) = ∫ x in (2:ℝ)..4, (-3 + 2 * x) := by
    refine integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hx
    rw [abs_of_nonneg (by linarith [hx.1]), abs_of_nonneg (by linarith [hx.1])]; ring
  rw [← integral_add_adjacent_intervals (hi 0 2) (hi 2 4),
    ← integral_add_adjacent_intervals (hi 0 1) (hi 1 2), h01, h12, h24]
  rw [integral_affine, integral_affine, integral_affine]; norm_num

/-- **Exemple 1.2** (linéarisation) : `∫₀^π sin⁴ x dx = 3π/8`. -/
theorem exemple_1_2 : ∫ x in (0:ℝ)..π, sin x ^ 4 = 3 * π / 8 := by
  rw [show (4:ℕ) = 2 * 2 from rfl, integral_sin_pow_even]
  norm_num [Finset.prod_range_succ]; ring

/-- Les intégrales de Wallis `W n = ∫₀^{π/2} sinⁿ x dx` (§1). -/
def W (n : ℕ) : ℝ := ∫ x in (0:ℝ)..π / 2, sin x ^ n

/-- §1 : `W n = ∫₀^{π/2} cosⁿ x dx` (changement de variable `x ↦ π/2 − x`). -/
theorem W_eq_integral_cos_pow (n : ℕ) : W n = ∫ x in (0:ℝ)..π / 2, cos x ^ n := by
  have h := integral_comp_sub_left (fun x => sin x ^ n) (a := 0) (b := π / 2) (π / 2)
  simp only [sub_self, sub_zero, sin_pi_div_two_sub] at h
  rw [W, ← h]

/-- §1 : `∫₀^π sinⁿ x dx = 2 W n` (changement de variable `x ↦ π − x`). -/
theorem two_mul_W (n : ℕ) : 2 * W n = ∫ x in (0:ℝ)..π, sin x ^ n := by
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun x => sin x ^ n) MeasureTheory.volume a b :=
    fun a b => (continuous_sin.pow n).intervalIntegrable a b
  have h := integral_comp_sub_left (fun x => sin x ^ n) (a := π / 2) (b := π) π
  simp only [sub_self, sin_pi_sub] at h
  rw [show π - π / 2 = π / 2 by ring] at h
  rw [← integral_add_adjacent_intervals (b := π / 2) (hi _ _) (hi _ _), h, W, two_mul]

/-- **Théorème 1.3**, 1 : `W 0 = π/2`. -/
theorem W_zero : W 0 = π / 2 := by simp [W]

/-- **Théorème 1.3**, 1 : `W 1 = 1`. -/
theorem W_one : W 1 = 1 := by simp [W]

/-- **Théorème 1.3**, 1 : la récurrence, sous la forme `(n + 2) W (n + 2) = (n + 1) W n`. -/
theorem W_succ_succ (n : ℕ) : ((n : ℝ) + 2) * W (n + 2) = (n + 1) * W n := by
  rw [W, integral_sin_pow, ← W]
  simp only [sin_zero, cos_pi_div_two, mul_zero, sub_zero, zero_pow (Nat.succ_ne_zero n),
    zero_mul, zero_div, zero_add]
  field_simp

/-- **Théorème 1.3**, 1 : `n W n = (n − 1) W (n − 2)` pour `n ≥ 2`, comme dans la fiche. -/
theorem W_rec {n : ℕ} (hn : 2 ≤ n) : (n : ℝ) * W n = (n - 1) * W (n - 2) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [Nat.add_sub_cancel]; push_cast; rw [W_succ_succ]; ring

/-- **Théorème 1.3**, 1 : formule close de `W (2p)`. -/
theorem W_even (p : ℕ) : W (2 * p) = (2 * p)! / (2 ^ (2 * p) * (p !) ^ 2) * (π / 2) := by
  induction p with
  | zero => simp [W_zero]
  | succ p ih =>
    have h := W_succ_succ (2 * p)
    push_cast at h
    rw [show 2 * (p + 1) = 2 * p + 1 + 1 by ring, Nat.factorial_succ (2 * p + 1),
      Nat.factorial_succ (2 * p), Nat.factorial_succ p]
    have e : W (2 * p + 1 + 1) = (2 * p + 1) / (2 * p + 2) * W (2 * p) := by
      field_simp; linarith
    rw [e, ih]; push_cast; field_simp; ring

/-- **Théorème 1.3**, 1 : formule close de `W (2p + 1)`. -/
theorem W_odd (p : ℕ) : W (2 * p + 1) = 2 ^ (2 * p) * (p !) ^ 2 / (2 * p + 1)! := by
  induction p with
  | zero => simp [W_one]
  | succ p ih =>
    have h := W_succ_succ (2 * p + 1)
    push_cast at h
    rw [show 2 * (p + 1) + 1 = 2 * p + 1 + 1 + 1 by ring, Nat.factorial_succ (2 * p + 1 + 1),
      Nat.factorial_succ (2 * p + 1), Nat.factorial_succ p]
    have e : W (2 * p + 1 + 1 + 1) = (2 * p + 2) / (2 * p + 3) * W (2 * p + 1) := by
      field_simp; linarith
    rw [e, ih, show 2 * (p + 1) = 2 * p + 2 by ring]; push_cast; field_simp; ring

/-- **Théorème 1.3**, 2, décalé d'un cran : `(n + 1) W (n + 1) W n = π/2`. -/
theorem W_mul_aux (n : ℕ) : ((n : ℝ) + 1) * W (n + 1) * W n = π / 2 := by
  induction n with
  | zero => simp [W_zero, W_one]
  | succ n ih =>
    have h := W_succ_succ n
    push_cast
    calc ((n : ℝ) + 1 + 1) * W (n + 1 + 1) * W (n + 1) = ((n : ℝ) + 2) * W (n + 2) * W (n + 1) := by
          ring_nf
      _ = π / 2 := by rw [h, ← ih]; ring

/-- **Théorème 1.3**, 2 : `n W n W (n − 1) = π/2` pour `n ≥ 1`. -/
theorem W_mul {n : ℕ} (hn : 1 ≤ n) : (n : ℝ) * W n * W (n - 1) = π / 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [Nat.add_sub_cancel]; push_cast; exact W_mul_aux m

/-- §1 : `W n > 0`. -/
theorem W_pos (n : ℕ) : 0 < W n := by
  linarith [two_mul_W n, integral_sin_pow_pos (n := n)]

/-- **Théorème 1.3**, 3 : `W (n + 1) < W n`. -/
theorem W_succ_lt (n : ℕ) : W (n + 1) < W n := by
  apply integral_lt_integral_of_continuousOn_of_le_of_exists_lt (by positivity)
  · exact (continuous_sin.pow _).continuousOn
  · exact (continuous_sin.pow _).continuousOn
  · intro x hx
    have h0 : 0 ≤ sin x := sin_nonneg_of_nonneg_of_le_pi hx.1.le (by linarith [hx.2, pi_pos])
    exact pow_le_pow_of_le_one h0 (sin_le_one x) (Nat.le_succ n)
  · refine ⟨π / 6, ⟨by positivity, by linarith [pi_pos]⟩, ?_⟩
    rw [sin_pi_div_six]
    exact pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (Nat.lt_succ_self n)

/-- **Théorème 1.3**, 3 : la suite `(W n)` est strictement décroissante. -/
theorem W_strictAnti : StrictAnti W := strictAnti_nat_of_succ_lt W_succ_lt

/-- **Théorème 1.3**, 3 : `W n ~ √(π/(2n))`. -/
theorem W_isEquivalent : W ~[atTop] fun n : ℕ => √(π / (2 * n)) := by
  have hg : Tendsto (fun n : ℕ => W n ^ 2 * (2 * n / π)) atTop (𝓝 1) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_natCast_div_add_atTop (1 : ℝ))
      tendsto_const_nhds (Eventually.of_forall fun n => ?_) ?_
    · have h1 := W_mul_aux n
      have h2 := mul_le_mul_of_nonneg_left (W_succ_lt n).le (W_pos n).le
      have key : π / (2 * (n + 1)) ≤ W n ^ 2 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
      calc (n : ℝ) / (n + 1) = π / (2 * (n + 1)) * (2 * n / π) := by
            field_simp
        _ ≤ W n ^ 2 * (2 * n / π) := by gcongr
    · filter_upwards [eventually_ge_atTop 1] with n hn
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
      have h1 := W_mul_aux m
      have h2 := mul_le_mul_of_nonneg_left (W_succ_lt m).le (W_pos (m + 1)).le
      push_cast
      rw [mul_div_assoc', div_le_one pi_pos]
      nlinarith
  refine isEquivalent_of_tendsto_one ?_
  have hs := hg.sqrt
  rw [sqrt_one] at hs
  refine hs.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp only [Pi.div_apply]
  rw [sqrt_mul (sq_nonneg _), sqrt_sq (W_pos n).le, div_eq_mul_inv (W n), ← sqrt_inv, inv_div]

/-- **Théorème 1.3**, 4 (produit de Wallis) : `∏_{k=1}^p (2k)²/((2k−1)(2k+1)) → π/2`.
Déduit de `Real.tendsto_prod_pi_div_two` de Mathlib, dont le produit est indexé à partir de 0. -/
theorem wallis_product :
    Tendsto (fun p : ℕ => ∏ k ∈ Icc 1 p, ((2 * k : ℝ) ^ 2 / ((2 * k - 1) * (2 * k + 1))))
      atTop (𝓝 (π / 2)) := by
  convert Real.tendsto_prod_pi_div_two using 1
  funext p
  induction p with
  | zero => simp
  | succ p ih =>
    rw [prod_Icc_succ_top (by omega), prod_range_succ, ih, div_mul_div_comm]
    push_cast
    congr 1
    ring

/-- Lien avec Mathlib : `Real.Wallis.W k` (le produit partiel de Mathlib) vaut
`π/2 · W (2k+1) / W (2k)`, ce qui est le quotient de la preuve du théorème 1.3, 4. -/
theorem wallis_W_eq (k : ℕ) : Real.Wallis.W k = π / 2 * (W (2 * k + 1) / W (2 * k)) := by
  have h := Real.Wallis.W_eq_integral_sin_pow_div_integral_sin_pow k
  rw [← two_mul_W, ← two_mul_W, mul_div_mul_left _ _ two_ne_zero] at h
  rw [← h]; field_simp

/-- **Exemple 1.4** : `2 W 4 = 3π/8`, en accord avec l'exemple 1.2. -/
theorem exemple_1_4 : 2 * W 4 = 3 * π / 8 := by
  rw [two_mul_W, exemple_1_2]

/-- **Proposition 1.5** (constante de Stirling) : si `n! ~ C √n (n/e)ⁿ` avec `C > 0`, alors
`C = √(2π)`. La preuve s'appuie sur la formule de Stirling de Mathlib
(`Stirling.factorial_isEquivalent_stirling`, démontrée elle-même par Wallis). -/
theorem stirling_constant {C : ℝ} (hC : 0 < C)
    (h : (fun n : ℕ => (n ! : ℝ)) ~[atTop] fun n => C * √n * (n / exp 1) ^ n) :
    C = √(2 * π) := by
  have h2 := h.symm.trans Stirling.factorial_isEquivalent_stirling
  have hz : ∀ᶠ n : ℕ in atTop, √(2 * n * π) * (n / exp 1) ^ n ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have ht := (isEquivalent_iff_tendsto_one hz).1 h2
  have hc : Tendsto (fun _ : ℕ => C / √(2 * π)) atTop (𝓝 1) := by
    refine ht.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [Pi.div_apply]
    rw [show (2 : ℝ) * n * π = 2 * π * n by ring, sqrt_mul (by positivity)]
    have : (0 : ℝ) < √n := sqrt_pos.2 this
    have : (0 : ℝ) < √(2 * π) := sqrt_pos.2 (by positivity)
    field_simp
  exact (div_eq_one_iff_eq (sqrt_pos.2 (by positivity)).ne').1
    (tendsto_nhds_unique tendsto_const_nhds hc)

/-- **Proposition 1.5**, forme finale : `n! ~ √(2πn) (n/e)ⁿ`. -/
theorem stirling : (fun n : ℕ => (n ! : ℝ)) ~[atTop] fun n => √(2 * π * n) * (n / exp 1) ^ n := by
  convert Stirling.factorial_isEquivalent_stirling using 3; ring_nf

/-! ## §2. Intégration par parties et rêve du bachelier -/

/-- **Proposition 2.1** : `I_n(x) = ∫₁ˣ tⁿ ln t dt = x^{n+1} ln x/(n+1) − (x^{n+1} − 1)/(n+1)²`
pour `n ∈ ℤ`, `n ≠ −1`, `x > 0`. -/
theorem ipp_log_I {n : ℤ} (hn : n ≠ -1) {x : ℝ} (hx : 0 < x) :
    ∫ t in (1:ℝ)..x, t ^ n * log t =
      x ^ (n + 1) * log x / (n + 1) - (x ^ (n + 1) - 1) / (n + 1) ^ 2 := by
  have hn' : (n : ℝ) + 1 ≠ 0 := by exact_mod_cast (show n + 1 ≠ 0 by omega)
  have hpos : ∀ t ∈ Set.uIcc 1 x, 0 < t := fun t ht => lt_of_lt_of_le (lt_min one_pos hx) ht.1
  have hd : ∀ t ∈ Set.uIcc 1 x, HasDerivAt
      (fun t : ℝ => t ^ (n + 1) * log t / (n + 1) - t ^ (n + 1) / (n + 1) ^ 2) (t ^ n * log t) t := by
    intro t ht
    have t0 := hpos t ht
    have h1 := hasDerivAt_zpow (n + 1) t (Or.inl t0.ne')
    have h2 := ((h1.mul (hasDerivAt_log t0.ne')).div_const ((n : ℝ) + 1)).sub
      (h1.div_const (((n : ℝ) + 1) ^ 2))
    convert h2 using 1
    simp only [add_sub_cancel_right]; push_cast
    rw [zpow_add_one₀ t0.ne']
    field_simp; ring
  have hc : ContinuousOn (fun t : ℝ => t ^ n * log t) (Set.uIcc 1 x) := by
    intro t ht
    have t0 := (hpos t ht).ne'
    exact ((continuousAt_zpow₀ t n (Or.inl t0)).mul (continuousAt_log t0)).continuousWithinAt
  rw [integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  simp; ring

/-- **Proposition 2.1** : `J_n(x) = x^{n+1} ln² x/(n+1) − 2 I_n(x)/(n+1)`. -/
theorem ipp_log_J {n : ℤ} (hn : n ≠ -1) {x : ℝ} (hx : 0 < x) :
    ∫ t in (1:ℝ)..x, t ^ n * log t ^ 2 =
      x ^ (n + 1) * log x ^ 2 / (n + 1) - 2 / (n + 1) * ∫ t in (1:ℝ)..x, t ^ n * log t := by
  have hn' : (n : ℝ) + 1 ≠ 0 := by exact_mod_cast (show n + 1 ≠ 0 by omega)
  have hpos : ∀ t ∈ Set.uIcc 1 x, 0 < t := fun t ht => lt_of_lt_of_le (lt_min one_pos hx) ht.1
  rw [ipp_log_I hn hx]
  have hd : ∀ t ∈ Set.uIcc 1 x, HasDerivAt
      (fun t : ℝ => t ^ (n + 1) * log t ^ 2 / (n + 1) -
        2 / (n + 1) * (t ^ (n + 1) * log t / (n + 1) - t ^ (n + 1) / (n + 1) ^ 2))
      (t ^ n * log t ^ 2) t := by
    intro t ht
    have t0 := hpos t ht
    have h1 := hasDerivAt_zpow (n + 1) t (Or.inl t0.ne')
    have hl := hasDerivAt_log t0.ne'
    have h2 := ((h1.mul (hl.pow 2)).div_const ((n : ℝ) + 1)).sub
      ((((h1.mul hl).div_const ((n : ℝ) + 1)).sub
      (h1.div_const (((n : ℝ) + 1) ^ 2))).const_mul (2 / ((n : ℝ) + 1)))
    convert h2 using 1
    simp only [add_sub_cancel_right, Pi.pow_apply]; push_cast
    rw [zpow_add_one₀ t0.ne']
    field_simp; ring
  have hc : ContinuousOn (fun t : ℝ => t ^ n * log t ^ 2) (Set.uIcc 1 x) := by
    intro t ht
    have t0 := (hpos t ht).ne'
    exact ((continuousAt_zpow₀ t n (Or.inl t0)).mul
      ((continuousAt_log t0).pow 2)).continuousWithinAt
  rw [integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  simp; ring

/-- **Proposition 2.1**, cas `n = −1` : `I_{−1}(x) = ln² x / 2`. -/
theorem ipp_log_I_neg_one {x : ℝ} (hx : 0 < x) :
    ∫ t in (1:ℝ)..x, t ^ (-1 : ℤ) * log t = log x ^ 2 / 2 := by
  have hpos : ∀ t ∈ Set.uIcc 1 x, 0 < t := fun t ht => lt_of_lt_of_le (lt_min one_pos hx) ht.1
  have hd : ∀ t ∈ Set.uIcc 1 x, HasDerivAt (fun t : ℝ => log t ^ 2 / 2) (t ^ (-1 : ℤ) * log t) t := by
    intro t ht
    convert ((hasDerivAt_log (hpos t ht).ne').pow 2).div_const 2 using 1
    simp only [zpow_neg_one]; push_cast; ring
  have hc : ContinuousOn (fun t : ℝ => t ^ (-1 : ℤ) * log t) (Set.uIcc 1 x) := by
    intro t ht
    have t0 := (hpos t ht).ne'
    exact ((continuousAt_zpow₀ t (-1) (Or.inl t0)).mul (continuousAt_log t0)).continuousWithinAt
  rw [integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  simp

/-- **Proposition 2.1**, cas `n = −1` : `J_{−1}(x) = ln³ x / 3`. -/
theorem ipp_log_J_neg_one {x : ℝ} (hx : 0 < x) :
    ∫ t in (1:ℝ)..x, t ^ (-1 : ℤ) * log t ^ 2 = log x ^ 3 / 3 := by
  have hpos : ∀ t ∈ Set.uIcc 1 x, 0 < t := fun t ht => lt_of_lt_of_le (lt_min one_pos hx) ht.1
  have hd : ∀ t ∈ Set.uIcc 1 x, HasDerivAt (fun t : ℝ => log t ^ 3 / 3)
      (t ^ (-1 : ℤ) * log t ^ 2) t := by
    intro t ht
    convert ((hasDerivAt_log (hpos t ht).ne').pow 3).div_const 3 using 1
    simp only [zpow_neg_one]; push_cast; ring
  have hc : ContinuousOn (fun t : ℝ => t ^ (-1 : ℤ) * log t ^ 2) (Set.uIcc 1 x) := by
    intro t ht
    have t0 := (hpos t ht).ne'
    exact ((continuousAt_zpow₀ t (-1) (Or.inl t0)).mul
      ((continuousAt_log t0).pow 2)).continuousWithinAt
  rw [integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  simp

/-- `t ↦ t^m ln^j t` est continue sur `ℝ` (Mathlib pose `log 0 = 0`) dès que `j ≤ m`. -/
theorem continuous_pow_mul_log_pow {m j : ℕ} (hj : j ≤ m) :
    Continuous fun t : ℝ => t ^ m * log t ^ j := by
  have e : (fun t : ℝ => t ^ m * log t ^ j) = fun t => t ^ (m - j) * (t * log t) ^ j := by
    funext t; rw [mul_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hj]
  rw [e]; exact (continuous_pow _).mul (continuous_mul_log.pow _)

/-- **Proposition 2.3**, cas `s = m ∈ ℕ` et `k = j ≤ m` :
`∫₀¹ t^m ln^j t dt = (−1)^j j!/(m+1)^{j+1}`. Démontrée par intégrations par parties successives
et non par dérivation sous l'intégrale (voir « Écarts »). -/
theorem moments_log {m j : ℕ} (hj : j ≤ m) :
    ∫ t in (0:ℝ)..1, t ^ m * log t ^ j = (-1) ^ j * j ! / ((m : ℝ) + 1) ^ (j + 1) := by
  induction j with
  | zero => simp [integral_pow]
  | succ j ih =>
    have ih := ih (by omega)
    have hm : (m : ℝ) + 1 ≠ 0 := by positivity
    have hG : ContinuousOn (fun t : ℝ => t ^ (m + 1) * log t ^ (j + 1) / (m + 1))
        (Set.Icc 0 1) :=
      ((continuous_pow_mul_log_pow (by omega)).div_const _).continuousOn
    have hd : ∀ t ∈ Set.Ioo (0:ℝ) 1, HasDerivAt
        (fun t : ℝ => t ^ (m + 1) * log t ^ (j + 1) / (m + 1))
        (t ^ m * log t ^ (j + 1) + (j + 1) / (m + 1) * (t ^ m * log t ^ j)) t := by
      intro t ht
      have t0 : t ≠ 0 := ht.1.ne'
      convert ((hasDerivAt_pow (m + 1) t).mul ((hasDerivAt_log t0).pow (j + 1))).div_const
        ((m : ℝ) + 1) using 1
      simp only [Nat.add_sub_cancel, Pi.pow_apply]; push_cast
      field_simp; ring
    have hi1 := (continuous_pow_mul_log_pow (m := m) (j := j + 1) (by omega)).intervalIntegrable
      (μ := MeasureTheory.volume) 0 1
    have hi2 := ((continuous_pow_mul_log_pow (m := m) (j := j) (by omega)).intervalIntegrable
      (μ := MeasureTheory.volume) 0 1).const_mul (((j : ℝ) + 1) / (m + 1))
    have h := integral_eq_sub_of_hasDerivAt_of_le zero_le_one hG hd (hi1.add hi2)
    rw [integral_add hi1 hi2, integral_const_mul, ih] at h
    simp at h
    rw [eq_neg_of_add_eq_zero_left h, Nat.factorial_succ]; push_cast
    field_simp
    ring

/-- Cœur du **théorème 2.5** : pour `|c| ≤ 1`, intégration terme à terme de
`exp(c · x ln x) = Σ (c x ln x)^k / k!` sur `[0, 1]` (convergence dominée). -/
theorem hasSum_integral_exp_mul_mul_log {c : ℝ} (hc : |c| ≤ 1) :
    HasSum (fun k : ℕ => c ^ k * (-1) ^ k / ((k : ℝ) + 1) ^ (k + 1))
      (∫ x in (0:ℝ)..1, exp (c * (x * log x))) := by
  have hF : ∀ k : ℕ, ∫ x in (0:ℝ)..1, (c * (x * log x)) ^ k / k ! =
      c ^ k * (-1) ^ k / ((k : ℝ) + 1) ^ (k + 1) := by
    intro k
    simp_rw [mul_pow, integral_div, integral_const_mul]
    rw [moments_log le_rfl]
    have : (k ! : ℝ) ≠ 0 := by positivity
    field_simp
  simp_rw [← hF]
  refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun k _ => 1 / (k ! : ℝ))
    (fun k => (((continuous_const.mul continuous_mul_log).pow k).div_const _).aestronglyMeasurable)
    (fun k => Eventually.of_forall fun t ht => ?_)
    (Eventually.of_forall fun _ _ => by simpa using Real.summable_pow_div_factorial 1)
    intervalIntegrable_const
    (Eventually.of_forall fun t _ => ?_)
  · rw [Set.uIoc_of_le zero_le_one] at ht
    have hl : log t ≤ 0 := log_nonpos ht.1.le ht.2
    have hl' := one_sub_inv_le_log_of_pos ht.1
    have h1 : |t * log t| ≤ 1 := by
      rw [abs_le]; constructor
      · have : t * (1 - t⁻¹) ≤ t * log t := mul_le_mul_of_nonneg_left hl' ht.1.le
        rw [mul_sub, mul_one, mul_inv_cancel₀ ht.1.ne'] at this
        linarith [ht.1]
      · nlinarith [ht.1]
    rw [norm_div, norm_pow, Real.norm_eq_abs, abs_mul, RCLike.norm_natCast]
    gcongr
    exact pow_le_one₀ (by positivity) (by nlinarith [abs_nonneg c, abs_nonneg (t * log t)])
  · have := NormedSpace.expSeries_div_hasSum_exp (c * (t * log t))
    rwa [← Real.exp_eq_exp_ℝ] at this

/-- **Théorème 2.5** (rêve du bachelier) : `∫₀¹ x^{−x} dx = Σ_{n ≥ 1} n^{−n}`
(série indexée à partir de `0`, terme `1/(n+1)^{n+1}`). -/
theorem sophomore_dream_neg :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (n + 1)) (∫ x in (0:ℝ)..1, x ^ (-x)) := by
  have h := hasSum_integral_exp_mul_mul_log (c := -1) (by norm_num)
  have e : ∫ x in (0:ℝ)..1, x ^ (-x) = ∫ x in (0:ℝ)..1, exp (-1 * (x * log x)) := by
    refine integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le zero_le_one] at hx
    rcases hx.1.eq_or_lt with h0 | h0
    · subst h0; simp
    · rw [rpow_def_of_pos h0]; ring_nf
  rw [e]
  convert h using 2 with k
  rw [← mul_pow]; norm_num

/-- **Théorème 2.5** : `∫₀¹ x^x dx = Σ_{n ≥ 1} (−1)^{n+1} n^{−n}`
(série indexée à partir de `0`, terme `(−1)^n/(n+1)^{n+1}`). -/
theorem sophomore_dream :
    HasSum (fun n : ℕ => (-1) ^ n / ((n : ℝ) + 1) ^ (n + 1)) (∫ x in (0:ℝ)..1, x ^ x) := by
  have h := hasSum_integral_exp_mul_mul_log (c := 1) (by norm_num)
  have e : ∫ x in (0:ℝ)..1, x ^ x = ∫ x in (0:ℝ)..1, exp (1 * (x * log x)) := by
    refine integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le zero_le_one] at hx
    rcases hx.1.eq_or_lt with h0 | h0
    · subst h0; simp
    · rw [rpow_def_of_pos h0]; ring_nf
  rw [e]
  convert h using 2 with k
  simp

/-! ## §3. Relations de récurrence et irrationalité de `e` -/

/-- Les intégrales `I n = ∫₀¹ xⁿ e^{−x} dx` du §3. -/
def I (n : ℕ) : ℝ := ∫ x in (0:ℝ)..1, x ^ n * exp (-x)

/-- **Proposition 3.1**, 1 : `I 0 = 1 − 1/e`. -/
theorem I_zero : I 0 = 1 - 1 / exp 1 := by
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun x => -exp (-x)) (x ^ 0 * exp (-x)) x := by
    intro x _
    convert ((hasDerivAt_neg x).exp).neg using 1; ring
  rw [I, integral_eq_sub_of_hasDerivAt hd (by apply Continuous.intervalIntegrable; fun_prop)]
  simp [exp_neg]; ring

/-- **Proposition 3.1**, 1 : `I (n + 1) = −1/e + (n + 1) I n`. -/
theorem I_succ (n : ℕ) : I (n + 1) = -(1 / exp 1) + (n + 1) * I n := by
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun x => -(x ^ (n + 1) * exp (-x)))
      (x ^ (n + 1) * exp (-x) - (n + 1) * (x ^ n * exp (-x))) x := by
    intro x _
    convert ((hasDerivAt_pow (n + 1) x).mul (hasDerivAt_neg x).exp).neg using 1
    simp only [Nat.add_sub_cancel]; push_cast; ring
  have hi : ∀ k : ℕ, IntervalIntegrable (fun x : ℝ => x ^ k * exp (-x)) MeasureTheory.volume 0 1 :=
    fun k => (by fun_prop : Continuous fun x : ℝ => x ^ k * exp (-x)).intervalIntegrable 0 1
  have h := integral_eq_sub_of_hasDerivAt hd ((hi (n + 1)).sub ((hi n).const_mul _))
  rw [integral_sub (hi (n + 1)) ((hi n).const_mul _), integral_const_mul] at h
  rw [I, I, one_div, ← exp_neg]
  norm_num at h
  linarith

/-- **Proposition 3.1**, 2 : `I n = n! (1 − e^{−1} Σ_{k ≤ n} 1/k!)`. -/
theorem I_closed (n : ℕ) :
    I n = n ! * (1 - 1 / exp 1 * ∑ k ∈ range (n + 1), 1 / (k ! : ℝ)) := by
  induction n with
  | zero => simp [I_zero]
  | succ n ih =>
    rw [I_succ, ih, sum_range_succ _ (n + 1), Nat.factorial_succ]; push_cast
    field_simp; ring

/-- **Proposition 3.1**, 3 : `0 < I n`. -/
theorem I_pos (n : ℕ) : 0 < I n :=
  intervalIntegral_pos_of_pos_on
    ((by fun_prop : Continuous fun x : ℝ => x ^ n * exp (-x)).intervalIntegrable 0 1)
    (fun x hx => mul_pos (pow_pos hx.1 n) (exp_pos _)) one_pos

/-- **Proposition 3.1**, 3 : `I n ≤ 1/(n + 1)`. -/
theorem I_le (n : ℕ) : I n ≤ 1 / (n + 1) := by
  have h : ∫ x in (0:ℝ)..1, x ^ n = 1 / (n + 1) := by rw [integral_pow]; simp
  rw [← h, I]
  apply integral_mono_on zero_le_one
    ((by fun_prop : Continuous fun x : ℝ => x ^ n * exp (-x)).intervalIntegrable 0 1)
    ((continuous_pow n).intervalIntegrable 0 1)
  exact fun x hx =>
    mul_le_of_le_one_right (pow_nonneg hx.1 n) (exp_le_one_iff.2 (by linarith [hx.1]))

/-- **Proposition 3.1**, 3 : `I n → 0`. -/
theorem I_tendsto : Tendsto I atTop (𝓝 0) :=
  squeeze_zero (fun n => (I_pos n).le) I_le tendsto_one_div_add_atTop_nhds_zero_nat

/-- **Exemple 3.2** : `I 1 = 1 − 2/e`. -/
theorem I_one : I 1 = 1 - 2 / exp 1 := by rw [I_succ, I_zero]; ring
/-- **Exemple 3.2** : `I 2 = 2 − 5/e`. -/
theorem I_two : I 2 = 2 - 5 / exp 1 := by rw [I_succ, I_one]; push_cast; ring
/-- **Exemple 3.2** : `I 3 = 6 − 16/e`. -/
theorem I_three : I 3 = 6 - 16 / exp 1 := by rw [I_succ, I_two]; push_cast; ring

/-- **Exemple 3.2** : `∫₀¹ (−x³ + 2x² − x) e^{−x} dx = −3 + 8/e`. -/
theorem exemple_3_2 : ∫ x in (0:ℝ)..1, (-x ^ 3 + 2 * x ^ 2 - x) * exp (-x) = -3 + 8 / exp 1 := by
  have hi : ∀ k : ℕ, IntervalIntegrable (fun x : ℝ => x ^ k * exp (-x)) MeasureTheory.volume 0 1 :=
    fun k => (by fun_prop : Continuous fun x : ℝ => x ^ k * exp (-x)).intervalIntegrable 0 1
  have e : (fun x : ℝ => (-x ^ 3 + 2 * x ^ 2 - x) * exp (-x)) =
      fun x => -(x ^ 3 * exp (-x)) + 2 * (x ^ 2 * exp (-x)) - x ^ 1 * exp (-x) := by
    funext x; ring
  rw [e, integral_sub, integral_add, integral_neg, integral_const_mul]
  rotate_left
  all_goals try (apply Continuous.intervalIntegrable; fun_prop)
  change -I 3 + 2 * I 2 - I 1 = _
  rw [I_three, I_two, I_one]; ring

/-- **Corollaire 3.3** : `e` est irrationnel, par l'argument de la fiche
(`e · I n = n! e − a_n` avec `a_n` entier et `0 < e · I n < 1`). -/
theorem irrational_exp_one : Irrational (exp 1) := by
  rintro ⟨r, hr⟩
  set n := max r.den 2 with hn
  have hden : r.den ≤ n := le_max_left _ _
  have h2 : 2 ≤ n := le_max_right _ _
  obtain ⟨z, hz⟩ : ∃ z : ℤ, (n ! : ℝ) * exp 1 = z := by
    obtain ⟨k, hk⟩ := Nat.dvd_factorial r.den_pos hden
    refine ⟨k * r.num, ?_⟩
    have hd : (r.den : ℝ) ≠ 0 := by positivity
    rw [← hr, Rat.cast_def, hk]
    push_cast
    field_simp
  have hsum : (n ! : ℝ) * ∑ k ∈ range (n + 1), 1 / (k ! : ℝ) =
      ((∑ k ∈ range (n + 1), n ! / k ! : ℕ) : ℝ) := by
    push_cast [mul_sum]
    refine sum_congr rfl fun k hk => ?_
    rw [Nat.cast_div (Nat.factorial_dvd_factorial (by simpa [Nat.lt_succ_iff] using hk))
      (by positivity)]
    ring
  set m : ℤ := z - ((∑ k ∈ range (n + 1), n ! / k ! : ℕ) : ℤ)
  have hm : exp 1 * I n = m := by
    have he : exp 1 * (1 / exp 1) = 1 := mul_one_div_cancel (exp_pos 1).ne'
    rw [I_closed]
    simp only [m, Int.cast_sub, Int.cast_natCast]
    rw [← hz, ← hsum]
    linear_combination (-(n ! : ℝ) * ∑ k ∈ range (n + 1), 1 / (k ! : ℝ)) * he
  have h0 : (0 : ℝ) < m := hm ▸ mul_pos (exp_pos 1) (I_pos n)
  have h1 : (m : ℝ) < 1 := by
    rw [← hm]
    have h3 : (3 : ℝ) ≤ n + 1 := by exact_mod_cast (by omega : 3 ≤ n + 1)
    calc exp 1 * I n ≤ exp 1 * (1 / (n + 1)) :=
          mul_le_mul_of_nonneg_left (I_le n) (exp_pos 1).le
      _ < 1 := by
        rw [mul_one_div, div_lt_one (by positivity)]; linarith [exp_one_lt_three]
  have : (1 : ℝ) ≤ m := by exact_mod_cast (show (0 : ℤ) < m by exact_mod_cast h0)
  linarith

/-! ## §4. Le problème de Bâle par le noyau de Dirichlet -/

/-- La somme `f_n(x) = 1/2 + Σ_{k=1}^n cos(kx)` du §4. -/
def fD (n : ℕ) (x : ℝ) : ℝ := 1 / 2 + ∑ k ∈ Icc 1 n, cos (k * x)

/-- **Lemme 4.1**, forme sans division : `2 sin(x/2) f_n(x) = sin((n + 1/2) x)`. -/
theorem two_sin_mul_fD (n : ℕ) (x : ℝ) : 2 * sin (x / 2) * fD n x = sin ((n + 1 / 2) * x) := by
  induction n with
  | zero => simp [fD]; ring_nf
  | succ n ih =>
    have e : fD (n + 1) x = fD n x + cos (((n : ℝ) + 1) * x) := by
      simp only [fD]; rw [sum_Icc_succ_top (by omega)]; push_cast; ring
    rw [e, mul_add, ih]
    have key : sin (((n : ℝ) + 1) * x + x / 2) - sin (((n : ℝ) + 1) * x - x / 2) =
        2 * sin (x / 2) * cos (((n : ℝ) + 1) * x) := by
      rw [sin_add, sin_sub]; ring
    rw [show ((n : ℝ) + 1) * x + x / 2 = ((n : ℝ) + 1 + 1 / 2) * x by ring,
      show ((n : ℝ) + 1) * x - x / 2 = ((n : ℝ) + 1 / 2) * x by ring] at key
    push_cast; linarith

/-- **Lemme 4.1** (noyau de Dirichlet) : `f_n(x) = sin((n+1/2)x)/(2 sin(x/2))` sur `]0, π]`. -/
theorem dirichlet_kernel (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ioc 0 π) :
    fD n x = sin ((n + 1 / 2) * x) / (2 * sin (x / 2)) := by
  have hs : 0 < sin (x / 2) := sin_pos_of_pos_of_lt_pi (by linarith [hx.1])
    (by linarith [hx.2, pi_pos])
  rw [eq_div_iff (by positivity), mul_comm]
  exact two_sin_mul_fD n x

/-- **Lemme 4.2** : `∫₀^π x cos(nx) dx = ((−1)ⁿ − 1)/n²` pour `n ≥ 1`. -/
theorem integral_x_cos {n : ℕ} (hn : 1 ≤ n) :
    ∫ x in (0:ℝ)..π, x * cos (n * x) = ((-1) ^ n - 1) / (n : ℝ) ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hd : ∀ x ∈ Set.uIcc 0 π, HasDerivAt
      (fun x : ℝ => x * sin (n * x) / n + cos (n * x) / n ^ 2) (x * cos (n * x)) x := by
    intro x _
    have hs := ((hasDerivAt_id' x).const_mul (n : ℝ)).sin
    have hc := ((hasDerivAt_id' x).const_mul (n : ℝ)).cos
    convert (((hasDerivAt_id' x).mul hs).div_const (n : ℝ)).add (hc.div_const ((n : ℝ) ^ 2))
      using 1
    field_simp; ring
  rw [integral_eq_sub_of_hasDerivAt hd (by apply Continuous.intervalIntegrable; fun_prop)]
  simp [sin_nat_mul_pi, cos_nat_mul_pi]
  field_simp

/-- **Lemme 4.2** : `∫₀^π x² cos(nx) dx = 2π(−1)ⁿ/n²` pour `n ≥ 1`. -/
theorem integral_x_sq_cos {n : ℕ} (hn : 1 ≤ n) :
    ∫ x in (0:ℝ)..π, x ^ 2 * cos (n * x) = 2 * π * (-1) ^ n / (n : ℝ) ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hd : ∀ x ∈ Set.uIcc 0 π, HasDerivAt
      (fun x : ℝ => x ^ 2 * sin (n * x) / n + 2 * x * cos (n * x) / n ^ 2 - 2 * sin (n * x) / n ^ 3)
      (x ^ 2 * cos (n * x)) x := by
    intro x _
    have hs := ((hasDerivAt_id' x).const_mul (n : ℝ)).sin
    have hc := ((hasDerivAt_id' x).const_mul (n : ℝ)).cos
    convert ((((hasDerivAt_pow 2 x).mul hs).div_const (n : ℝ)).add
      ((((hasDerivAt_id' x).const_mul 2).mul hc).div_const ((n : ℝ) ^ 2))).sub
      ((hs.const_mul 2).div_const ((n : ℝ) ^ 3)) using 1
    field_simp; ring
  rw [integral_eq_sub_of_hasDerivAt hd (by apply Continuous.intervalIntegrable; fun_prop)]
  simp [sin_nat_mul_pi, cos_nat_mul_pi]

/-- La fonction `φ(x) = x²/(2π) − x` du lemme 4.2. -/
def phi (x : ℝ) : ℝ := x ^ 2 / (2 * π) - x

/-- `φ` est continue. -/
theorem continuous_phi : Continuous phi := by unfold phi; fun_prop

/-- **Lemme 4.2** : `∫₀^π φ(x) cos(nx) dx = 1/n²` pour `n ≥ 1`. -/
theorem integral_phi_cos {n : ℕ} (hn : 1 ≤ n) :
    ∫ x in (0:ℝ)..π, phi x * cos (n * x) = 1 / (n : ℝ) ^ 2 := by
  have e : (fun x => phi x * cos (n * x)) =
      fun x => (2 * π)⁻¹ * (x ^ 2 * cos (n * x)) - x * cos (n * x) := by
    funext x; simp only [phi]; ring
  rw [e, integral_sub ((Continuous.intervalIntegrable (by fun_prop) _ _))
    (Continuous.intervalIntegrable (by fun_prop) _ _), integral_const_mul, integral_x_sq_cos hn,
    integral_x_cos hn]
  have := pi_pos.ne'
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  field_simp; ring

/-- **Lemme 4.2** : `∫₀^π φ(x) dx = −π²/3`. -/
theorem integral_phi : ∫ x in (0:ℝ)..π, phi x = -π ^ 2 / 3 := by
  have := pi_pos.ne'
  have hd : ∀ x ∈ Set.uIcc 0 π, HasDerivAt (fun x : ℝ => x ^ 3 / (6 * π) - x ^ 2 / 2) (phi x) x := by
    intro x _
    convert ((hasDerivAt_pow 3 x).div_const (6 * π)).sub ((hasDerivAt_pow 2 x).div_const 2)
      using 1
    simp only [phi]; field_simp; ring
  rw [integral_eq_sub_of_hasDerivAt hd (continuous_phi.intervalIntegrable _ _)]
  field_simp; ring

/-- **Théorème 4.5**, l'égalité : `∫₀^π φ f_n = u_n − π²/6`. -/
theorem integral_phi_fD (n : ℕ) :
    ∫ x in (0:ℝ)..π, phi x * fD n x = (∑ k ∈ Icc 1 n, 1 / (k : ℝ) ^ 2) - π ^ 2 / 6 := by
  have e : (fun x => phi x * fD n x) =
      fun x => 1 / 2 * phi x + ∑ k ∈ Icc 1 n, phi x * cos (k * x) := by
    funext x; simp only [fD]; rw [mul_add, mul_sum]; ring
  have hk : ∀ k ∈ Icc 1 n, IntervalIntegrable (fun x => phi x * cos (k * x))
      MeasureTheory.volume 0 π :=
    fun k _ => (continuous_phi.mul (by fun_prop)).intervalIntegrable _ _
  have hs : IntervalIntegrable (fun x => ∑ k ∈ Icc 1 n, phi x * cos (k * x))
      MeasureTheory.volume 0 π :=
    (continuous_finsetSum _ fun k _ => continuous_phi.mul (by fun_prop)).intervalIntegrable _ _
  rw [e, integral_add ((continuous_phi.const_mul _).intervalIntegrable _ _) hs,
    integral_const_mul, integral_finsetSum hk, integral_phi,
    sum_congr rfl fun k hk => integral_phi_cos (n := k) (mem_Icc.1 hk).1]
  ring

/-- **Lemme 4.4** (Riemann–Lebesgue, cas `C¹`) : `∫_α^β h(x) sin(λx) dx → 0` quand `λ → +∞`.
La dérivabilité est demandée au sens de `HasDerivAt` en tout point de `[α, β]`. -/
theorem riemann_lebesgue {h h' : ℝ → ℝ} {α β : ℝ} (hab : α ≤ β)
    (hd : ∀ x ∈ Set.Icc α β, HasDerivAt h (h' x) x) (hc : ContinuousOn h' (Set.Icc α β)) :
    Tendsto (fun l : ℝ => ∫ x in α..β, h x * sin (l * x)) atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  set K := |h α| + |h β| + (β - α) * M with hK
  have key : ∀ l > 0, |∫ x in α..β, h x * sin (l * x)| ≤ K / l := by
    intro l hl
    have hv : ∀ x ∈ Set.uIcc α β, HasDerivAt (fun x => -cos (l * x) / l) (sin (l * x)) x := by
      intro x _
      convert (((hasDerivAt_id' x).const_mul l).cos.neg).div_const l using 1
      field_simp
    have hu : ∀ x ∈ Set.uIcc α β, HasDerivAt h (h' x) x := by
      intro x hx; rw [Set.uIcc_of_le hab] at hx; exact hd x hx
    rw [integral_mul_deriv_eq_deriv_mul hu hv (hc.intervalIntegrable_of_Icc hab)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    have hI : |∫ x in α..β, h' x * (-cos (l * x) / l)| ≤ M / l * (β - α) := by
      have := norm_integral_le_of_norm_le_const (a := α) (b := β) (C := M / l)
        (f := fun x => h' x * (-cos (l * x) / l)) (fun x hx => by
          rw [Set.uIoc_of_le hab] at hx
          rw [norm_mul, norm_div, norm_neg, Real.norm_eq_abs l, abs_of_pos hl]
          calc ‖h' x‖ * (‖cos (l * x)‖ / l) ≤ M * (1 / l) := by
                gcongr
                all_goals first
                  | exact (norm_nonneg _).trans (hM α ⟨le_rfl, hab⟩)
                  | exact hM x (Set.Ioc_subset_Icc_self hx)
                  | exact (Real.norm_eq_abs _).trans_le (abs_cos_le_one _)
            _ = M / l := by ring)
      rwa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hab)] at this
    have hA : ∀ y, |h y * (-cos (l * y) / l)| ≤ |h y| / l := by
      intro y
      rw [abs_mul, abs_div, abs_neg, abs_of_pos hl]
      calc |h y| * (|cos (l * y)| / l) ≤ |h y| * (1 / l) := by
            gcongr; exact abs_cos_le_one _
        _ = |h y| / l := by ring
    have hKl : K / l = |h α| / l + |h β| / l + M / l * (β - α) := by rw [hK]; ring
    rw [hKl]
    calc _ ≤ |h β * (-cos (l * β) / l) - h α * (-cos (l * α) / l)| +
          |∫ x in α..β, h' x * (-cos (l * x) / l)| := abs_sub _ _
      _ ≤ |h β * (-cos (l * β) / l)| + |h α * (-cos (l * α) / l)| +
          |∫ x in α..β, h' x * (-cos (l * x) / l)| := by gcongr; exact abs_sub _ _
      _ ≤ _ := by linarith [hA α, hA β]
  refine squeeze_zero_norm' ?_
    ((tendsto_const_nhds : Tendsto (fun _ : ℝ => K) atTop (𝓝 K)).div_atTop tendsto_id)
  filter_upwards [eventually_gt_atTop 0] with l hl
  rw [Real.norm_eq_abs]; exact key l hl

/-- Le sinus cardinal (`Real.sinc`, prolongé par `1` en `0`) est `C¹` sur `ℝ`. -/
theorem contDiffAt_sinc (x : ℝ) : ContDiffAt ℝ 1 sinc x := by
  rcases eq_or_ne x 0 with rfl | hx
  · obtain ⟨p, hp⟩ := analyticAt_sin (x := (0 : ℝ))
    rw [sinc_eq_dslope]
    exact hp.has_fpower_series_dslope_fslope.analyticAt.contDiffAt
  · refine (contDiff_sin.contDiffAt.div contDiffAt_id hx).congr_of_eventuallyEq ?_
    filter_upwards [eventually_ne_nhds hx] with y hy using sinc_of_ne_zero hy

/-- La fonction `h` de la preuve du théorème 4.5, écrite `h(x) = (x − 2π)/(2π) / sinc(x/2)`, ce qui
est la forme de la fiche et donne directement son prolongement en `0`. -/
def hB (x : ℝ) : ℝ := (x - 2 * π) / (2 * π) / sinc (x / 2)

/-- Preuve du **théorème 4.5** : `h` est de classe `C¹` sur `]−2π, 2π[`, donc sur `[0, π]`. -/
theorem contDiffAt_hB {x : ℝ} (hx : x ∈ Set.Ioo (-(2 * π)) (2 * π)) : ContDiffAt ℝ 1 hB x := by
  have hs : sinc (x / 2) ≠ 0 := (sinc_pos (by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2])).ne'
  exact ((contDiffAt_id.sub contDiffAt_const).div_const (2 * π)).div
    ((contDiffAt_sinc (x / 2)).comp x (contDiffAt_id.div_const 2)) hs

/-- Preuve du **théorème 4.5** : `φ(x) f_n(x) = h(x) sin((n + 1/2)x)` sur `[0, π]`. -/
theorem phi_mul_fD_eq (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc 0 π) :
    phi x * fD n x = hB x * sin ((n + 1 / 2) * x) := by
  rcases hx.1.eq_or_lt with h0 | h0
  · subst h0; simp [phi]
  · have hs : 0 < sin (x / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hx.2, pi_pos])
    rw [dirichlet_kernel n ⟨h0, hx.2⟩, hB, sinc_of_ne_zero (by positivity), phi]
    have := pi_pos.ne'
    field_simp

/-- **Théorème 4.5**, la limite : `∫₀^π φ f_n → 0`. -/
theorem tendsto_integral_phi_fD :
    Tendsto (fun n : ℕ => ∫ x in (0:ℝ)..π, phi x * fD n x) atTop (𝓝 0) := by
  have hopen : ∀ x ∈ Set.Icc 0 π, x ∈ Set.Ioo (-(2 * π)) (2 * π) := fun x hx =>
    ⟨by linarith [hx.1, pi_pos], by linarith [hx.2, pi_pos]⟩
  have hc : ContinuousOn (deriv hB) (Set.Icc 0 π) := by
    have h1 : ContDiffOn ℝ 1 hB (Set.Ioo (-(2 * π)) (2 * π)) :=
      fun x hx => (contDiffAt_hB hx).contDiffWithinAt
    exact (h1.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).mono hopen
  have hRL := riemann_lebesgue pi_pos.le
    (fun x hx => ((contDiffAt_hB (hopen x hx)).differentiableAt one_ne_zero).hasDerivAt) hc
  have hl : Tendsto (fun n : ℕ => (n : ℝ) + 1 / 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  refine (hRL.comp hl).congr fun n => ?_
  simp only [Function.comp]
  refine integral_congr fun x hx => ?_
  rw [Set.uIcc_of_le pi_pos.le] at hx
  exact (phi_mul_fD_eq n hx).symm

/-- **Théorème 4.5** : `Σ_{k ≥ 1} 1/k² = π²/6`, démontré par la méthode de la fiche
(série indexée à partir de `0`, terme `1/(k+1)²`). -/
theorem basel : HasSum (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
  have hu : ∀ n : ℕ, ∑ k ∈ range n, 1 / ((k : ℝ) + 1) ^ 2 = ∑ k ∈ Icc 1 n, 1 / (k : ℝ) ^ 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, ih, sum_Icc_succ_top (by omega)]; push_cast; ring
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => by positivity)]
  have h := tendsto_integral_phi_fD.add_const (π ^ 2 / 6)
  rw [zero_add] at h
  refine h.congr fun n => ?_
  rw [integral_phi_fD, hu]; ring

/-- **Théorème 4.5** sous la forme `Σ_{n ≥ 0} 1/n² = π²/6` (le terme `n = 0` vaut `0` en Lean). -/
theorem zeta_two : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2) (π ^ 2 / 6) := by
  rw [← hasSum_nat_add_iff' 1]
  simpa using basel

/-- Lien avec Mathlib : c'est exactement l'énoncé de `hasSum_zeta_two`, démontré dans Mathlib par
les polynômes de Bernoulli et la théorie de Fourier ; `zeta_two` en donne une seconde preuve. -/
theorem zeta_two_eq_mathlib : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2) (π ^ 2 / 6) :=
  hasSum_zeta_two


/-! ## §5. Encadrement par convexité -/

/-- La fonction `f(x) = 1/(1 + x + x²)` du §5. -/
def f5 (x : ℝ) : ℝ := 1 / (1 + x + x ^ 2)

/-- `1 + x + x² > 0`. -/
theorem q_pos (x : ℝ) : 0 < 1 + x + x ^ 2 := by nlinarith [sq_nonneg (x + 1 / 2)]

/-- **Proposition 5.1**, 1 : `f'(x) = −(2x + 1)/(1 + x + x²)²`. -/
theorem hasDerivAt_f5 (x : ℝ) : HasDerivAt f5 (-(2 * x + 1) / (1 + x + x ^ 2) ^ 2) x := by
  have h := (((hasDerivAt_id' x).const_add 1).add (hasDerivAt_pow 2 x)).inv (q_pos x).ne'
  convert h using 1
  · funext y; rw [f5, one_div]; rfl
  · norm_num; ring

/-- **Proposition 5.1**, 1 : la dérivée de `f`. -/
theorem deriv_f5 : deriv f5 = fun x => -(2 * x + 1) / (1 + x + x ^ 2) ^ 2 :=
  funext fun x => (hasDerivAt_f5 x).deriv

/-- **Proposition 5.1**, 1 : `f''(x) = 6x(1 + x)/(1 + x + x²)³`. -/
theorem deriv2_f5 (x : ℝ) : deriv (deriv f5) x = 6 * x * (1 + x) / (1 + x + x ^ 2) ^ 3 := by
  rw [deriv_f5]
  have hq := (q_pos x).ne'
  have hq1 := ((hasDerivAt_id' x).const_add 1).add (hasDerivAt_pow 2 x)
  have h : HasDerivAt (fun x => -(2 * x + 1) / (1 + x + x ^ 2) ^ 2)
      (6 * x * (1 + x) / (1 + x + x ^ 2) ^ 3) x := by
    refine ((((hasDerivAt_id' x).const_mul 2).add_const 1).neg.div (hq1.pow 2)
      (pow_ne_zero 2 hq)).congr_deriv ?_
    simp only [Pi.add_apply, Pi.pow_apply, Pi.neg_apply, Nat.cast_ofNat]
    field_simp
    ring
  exact h.deriv

/-- **Proposition 5.1**, 1 : `f` est strictement décroissante sur `[0, 1]`. -/
theorem f5_strictAntiOn : StrictAntiOn f5 (Set.Icc 0 1) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc 0 1)
    (fun x _ => (hasDerivAt_f5 x).continuousAt.continuousWithinAt) fun x hx => ?_
  rw [interior_Icc] at hx
  rw [(hasDerivAt_f5 x).deriv]
  exact div_neg_of_neg_of_pos (by linarith [hx.1]) (pow_pos (q_pos x) 2)

/-- **Proposition 5.1**, 1 : `f` est convexe sur `[0, 1]`. -/
theorem f5_convexOn : ConvexOn ℝ (Set.Icc 0 1) f5 := by
  refine convexOn_of_deriv2_nonneg (convex_Icc 0 1)
    (fun x _ => (hasDerivAt_f5 x).continuousAt.continuousWithinAt)
    (fun x _ => (hasDerivAt_f5 x).differentiableAt.differentiableWithinAt) ?_ ?_
  · rw [deriv_f5]
    intro x _
    exact (((((hasDerivAt_id' x).const_mul 2).add_const 1).neg.div
      ((((hasDerivAt_id' x).const_add 1).add (hasDerivAt_pow 2 x)).pow 2)
      (pow_ne_zero 2 (q_pos x).ne')).differentiableAt).differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [Function.iterate_succ, Function.iterate_one, Function.comp_apply, deriv2_f5]
    have := hx.1
    have := q_pos x
    positivity

/-- **Proposition 5.1**, 2 : `f(0) = 1`, `f(1) = 1/3`, `f'(0) = −1`, `f'(1) = −1/3`, d'où les
équations de la corde et des tangentes. -/
theorem f5_values : f5 0 = 1 ∧ f5 1 = 1 / 3 ∧ deriv f5 0 = -1 ∧ deriv f5 1 = -1 / 3 := by
  refine ⟨by norm_num [f5], by norm_num [f5], ?_, ?_⟩ <;> rw [deriv_f5] <;> norm_num

/-- `f` est continue. -/
theorem continuous_f5 : Continuous f5 :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_f5 x).continuousAt

/-- **Proposition 5.1**, 3 : `∫₀¹ f < 8/12` (corde). -/
theorem integral_f5_lt : ∫ x in (0:ℝ)..1, f5 x < 8 / 12 := by
  have h : ∫ x in (0:ℝ)..1, f5 x < ∫ x in (0:ℝ)..1, (1 + (-2 / 3) * x) := by
    apply integral_lt_integral_of_continuousOn_of_le_of_exists_lt zero_lt_one
      continuous_f5.continuousOn (by fun_prop)
    · intro x hx
      rw [f5, div_le_iff₀ (q_pos x)]
      nlinarith [mul_nonneg (mul_nonneg hx.1.le (sub_nonneg.2 hx.2)) (by linarith [hx.1] :
        (0:ℝ) ≤ 1 + 2 * x)]
    · exact ⟨1 / 2, ⟨by norm_num, by norm_num⟩, by norm_num [f5]⟩
  rw [integral_affine] at h
  linarith

/-- **Proposition 5.1**, 3 : `7/12 < ∫₀¹ f` (tangentes en `0` et en `1`, qui se coupent en `1/2`). -/
theorem lt_integral_f5 : 7 / 12 < ∫ x in (0:ℝ)..1, f5 x := by
  have hi : ∀ a b : ℝ, IntervalIntegrable f5 MeasureTheory.volume a b :=
    fun a b => continuous_f5.intervalIntegrable a b
  have h1 : ∫ x in (0:ℝ)..1 / 2, (1 + (-1) * x) < ∫ x in (0:ℝ)..1 / 2, f5 x := by
    apply integral_lt_integral_of_continuousOn_of_le_of_exists_lt (by norm_num)
      (by fun_prop) continuous_f5.continuousOn
    · intro x hx
      rw [f5, le_div_iff₀ (q_pos x)]
      nlinarith [mul_nonneg (mul_nonneg hx.1.le hx.1.le) hx.1.le]
    · exact ⟨1 / 4, ⟨by norm_num, by norm_num⟩, by norm_num [f5]⟩
  have h2 : ∫ x in (1 / 2 : ℝ)..1, (2 / 3 + (-1 / 3) * x) ≤ ∫ x in (1 / 2 : ℝ)..1, f5 x := by
    apply integral_mono_on (by norm_num) (Continuous.intervalIntegrable (by fun_prop) _ _) (hi _ _)
    intro x hx
    rw [f5, le_div_iff₀ (q_pos x)]
    nlinarith [mul_nonneg (sq_nonneg (x - 1)) (by linarith [hx.1] : (0:ℝ) ≤ x + 1)]
  rw [integral_affine] at h1 h2
  rw [← integral_add_adjacent_intervals (hi 0 (1 / 2)) (hi (1 / 2) 1)]
  linarith

/-- **Proposition 5.1**, 3 : `∫₀¹ f = π/(3√3)`. -/
theorem integral_f5 : ∫ x in (0:ℝ)..1, f5 x = π / (3 * √3) := by
  have h3 : √3 ^ 2 = 3 := sq_sqrt (by norm_num)
  have hs : 0 < √3 := by positivity
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun x => 2 / √3 * arctan ((2 * x + 1) / √3)) (f5 x) x := by
    intro x _
    convert ((((hasDerivAt_id' x).const_mul 2).add_const 1).div_const √3).arctan.const_mul
      (2 / √3) using 1
    have := q_pos x
    rw [f5, div_pow, h3]
    field_simp
    nlinarith [h3]
  rw [integral_eq_sub_of_hasDerivAt hd (continuous_f5.intervalIntegrable _ _)]
  have e1 : arctan ((2 * 1 + 1) / √3) = π / 3 := by
    rw [show (2 * 1 + 1 : ℝ) / √3 = √3 by
      field_simp; rw [h3]; norm_num, ← tan_pi_div_three]
    exact arctan_tan (by linarith [pi_pos]) (by linarith [pi_pos])
  have e0 : arctan ((2 * 0 + 1) / √3) = π / 6 := by
    rw [show (2 * 0 + 1 : ℝ) / √3 = 1 / √3 by norm_num, ← tan_pi_div_six]
    exact arctan_tan (by linarith [pi_pos]) (by linarith [pi_pos])
  rw [e1, e0]
  field_simp; ring

/-! ## §6. Reste intégral de la formule de Taylor -/

/-- Le reste `R n = (1/n!) ∫₀¹ (1 − x)ⁿ eˣ dx` du §6. -/
def R (n : ℕ) : ℝ := 1 / n ! * ∫ x in (0:ℝ)..1, (1 - x) ^ n * exp x

/-- §6 : `R 0 = ∫₀¹ eˣ dx`, comme dans la définition de la fiche. -/
theorem R_zero_eq : R 0 = ∫ x in (0:ℝ)..1, exp x := by simp [R]

/-- **Proposition 6.1**, 1 : `∫₀¹ (1 − x)ⁿ dx = 1/(n + 1)`. -/
theorem integral_one_sub_pow (n : ℕ) : ∫ x in (0:ℝ)..1, (1 - x) ^ n = 1 / (n + 1) := by
  have h := integral_comp_sub_left (fun x : ℝ => x ^ n) (a := 0) (b := 1) 1
  simp only [sub_self, sub_zero] at h
  rw [h, integral_pow]; simp

/-- Intégration par parties de la preuve de la proposition 6.1, 2. -/
theorem integral_one_sub_pow_exp_succ (n : ℕ) :
    ∫ x in (0:ℝ)..1, (1 - x) ^ (n + 1) * exp x =
      -1 + (n + 1) * ∫ x in (0:ℝ)..1, (1 - x) ^ n * exp x := by
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun x => (1 - x) ^ (n + 1) * exp x)
      ((1 - x) ^ (n + 1) * exp x - (n + 1) * ((1 - x) ^ n * exp x)) x := by
    intro x _
    have h1 := (hasDerivAt_pow (n + 1) (1 - x)).comp x ((hasDerivAt_id' x).const_sub 1)
    refine (h1.mul (hasDerivAt_exp x)).congr_deriv ?_
    simp only [Function.comp_apply, Nat.add_sub_cancel]; push_cast; ring
  have hi : ∀ k : ℕ, IntervalIntegrable (fun x : ℝ => (1 - x) ^ k * exp x)
      MeasureTheory.volume 0 1 :=
    fun k => (by fun_prop : Continuous fun x : ℝ => (1 - x) ^ k * exp x).intervalIntegrable 0 1
  have h := integral_eq_sub_of_hasDerivAt hd ((hi (n + 1)).sub ((hi n).const_mul _))
  rw [integral_sub (hi (n + 1)) ((hi n).const_mul _), integral_const_mul] at h
  norm_num at h
  linarith

/-- **Proposition 6.1**, 2 : `R n = e − Σ_{k ≤ n} 1/k!`. -/
theorem R_eq (n : ℕ) : R n = exp 1 - ∑ k ∈ range (n + 1), 1 / (k ! : ℝ) := by
  induction n with
  | zero =>
    rw [R_zero_eq, integral_exp]; simp
  | succ n ih =>
    have h := integral_one_sub_pow_exp_succ n
    have e : R (n + 1) = R n - 1 / (n + 1)! := by
      rw [R, R, h, Nat.factorial_succ]; push_cast; field_simp; ring
    rw [e, ih, sum_range_succ _ (n + 1)]; ring

/-- **Proposition 6.1**, 3 : `1/(n+1)! < R n < e/(n+1)!` (vrai aussi pour `n = 0`). -/
theorem R_bounds (n : ℕ) : 1 / ((n + 1)! : ℝ) < R n ∧ R n < exp 1 / (n + 1)! := by
  have hc : Continuous fun x : ℝ => (1 - x) ^ n * exp x := by fun_prop
  have hc' : Continuous fun x : ℝ => (1 - x) ^ n := by fun_prop
  have hc'' : Continuous fun x : ℝ => (1 - x) ^ n * exp 1 := by fun_prop
  have hlo : ∫ x in (0:ℝ)..1, (1 - x) ^ n < ∫ x in (0:ℝ)..1, (1 - x) ^ n * exp x := by
    apply integral_lt_integral_of_continuousOn_of_le_of_exists_lt zero_lt_one hc'.continuousOn
      hc.continuousOn
    · intro x hx
      have : 0 ≤ (1 - x) ^ n := pow_nonneg (by linarith [hx.2]) n
      nlinarith [one_le_exp hx.1.le]
    · refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
      have : (0 : ℝ) < (1 - 1 / 2) ^ n := by positivity
      nlinarith [one_lt_exp_iff.2 (by norm_num : (0 : ℝ) < 1 / 2)]
  have hhi : ∫ x in (0:ℝ)..1, (1 - x) ^ n * exp x < ∫ x in (0:ℝ)..1, (1 - x) ^ n * exp 1 := by
    apply integral_lt_integral_of_continuousOn_of_le_of_exists_lt zero_lt_one hc.continuousOn
      hc''.continuousOn
    · intro x hx
      exact mul_le_mul_of_nonneg_left (exp_le_exp.2 hx.2) (pow_nonneg (by linarith [hx.2]) n)
    · refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
      have : (0 : ℝ) < (1 - 1 / 2) ^ n := by positivity
      exact mul_lt_mul_of_pos_left (exp_lt_exp.2 (by norm_num)) this
  rw [integral_mul_const, integral_one_sub_pow] at hhi
  rw [integral_one_sub_pow] at hlo
  have hf : (0 : ℝ) < n ! := by positivity
  rw [R, Nat.factorial_succ]; push_cast
  constructor
  · rw [one_div_mul_eq_div, lt_div_iff₀ hf]
    calc 1 / (((n : ℝ) + 1) * n !) * n ! = 1 / (n + 1) := by field_simp
      _ < _ := hlo
  · rw [one_div_mul_eq_div, div_lt_iff₀ hf]
    calc _ < 1 / ((n : ℝ) + 1) * exp 1 := hhi
      _ = _ := by field_simp

/-- **Proposition 6.1**, 3 : `R n → 0`. -/
theorem R_tendsto : Tendsto R atTop (𝓝 0) := by
  refine squeeze_zero (fun n => (R_bounds n).1.le.trans' (by positivity)) (fun n => ?_)
    ((tendsto_const_div_atTop_nhds_zero_nat (exp 1)).comp (tendsto_add_atTop_nat 1))
  refine (R_bounds n).2.le.trans ?_
  simp only [Function.comp]
  apply div_le_div_of_nonneg_left (exp_pos 1).le (by positivity)
  exact_mod_cast Nat.self_le_factorial (n + 1)

/-- **Proposition 6.1**, 3 : `e = Σ_{k ≥ 0} 1/k!`. -/
theorem hasSum_inv_factorial : HasSum (fun k : ℕ => 1 / (k ! : ℝ)) (exp 1) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => by positivity), ← tendsto_add_atTop_iff_nat 1]
  have h := R_tendsto.const_sub (exp 1)
  rw [sub_zero] at h
  refine h.congr fun n => ?_
  rw [R_eq]; ring

end CalculIntegral

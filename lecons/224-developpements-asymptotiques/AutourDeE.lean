import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.Order.Floor

/-!
# Autour du nombre e

Formalisation de la fiche « Autour du nombre e — ce qu'on peut tirer de l'inégalité
`e^x ≥ 1 + x` » (M. Hua, octobre 2026), `autour-de-e.tex`. Les numéros des énoncés sont ceux
de la fiche.

## Modèles

* Tout est réel : `exp`, `log`, `n !` vu dans `ℝ`. Les énoncés « pour tout `n ≥ 1` » portent
  une hypothèse `1 ≤ n`.
* **Section 2.** `u n = n^n / n!` ; `w n = ln n! - (n + 1/2) ln n + n`. La suite de Mathlib
  `Stirling.stirlingSeq n = n! / (√(2n) (n/e)^n)` vérifie `w n = ln (stirlingSeq n) + (ln 2)/2`
  (`w_eq`) : on réutilise ainsi la limite `√π` de Mathlib (`Stirling.tendsto_stirlingSeq_sqrt_pi`,
  démontrée avec le produit de Wallis) et la borne de Robbins `Stirling.log_stirlingSeq_sdiff_le`.
* **Section 3.** Pour une famille finie `s` non vide et `a : ι → ℝ` strictement positive :
  `moyA` = `m`, `moyG` = `g`, écrite `∏ aᵢ^{1/n}`, `moyH` = `h`, `moyP p` = `M_p` pour `p ≠ 0`.
  Les inégalités viennent des inégalités de moyennes pondérées de Mathlib, avec les poids `1/n`.
  L'exemple `(4, 10, 25)` est la famille `![4, 10, 25]` indexée par `Fin 3`.
* **Section 4.** `U n = ∑_{k ≤ n} 1/k!` et `V n = U n + 1/(n · n!)` sont les suites `u_n`, `v_n`
  de la fiche (renommées pour ne pas les confondre avec la suite `u` de la section 2).
  Leur limite est identifiée à `exp 1` par la série exponentielle de Mathlib
  (`NormedSpace.expSeries_div_hasSum_exp`).

## Écarts avec la fiche

* Aucun énoncé de la fiche ne s'est révélé faux.
* Prop. 4.3 : l'encadrement `1/(n+1)! < e - u_n < e/(n+1)!` est démontré sans la formule de
  Taylor avec reste intégral, à partir de `u_{n+1} < e < v_n` (prop. 4.1) et de
  `(n+1)/n ≤ 2 < e`. Il est énoncé pour tout `n ≥ 0`.
* Th. 2.7 : l'équivalent est celui de Mathlib ; l'existence de `θ_n ∈ ]0, 1]` est démontrée ici,
  par la même méthode que la fiche (suites adjacentes `w_n` et `w_n - 1/(12n)`).
* Th. 3.6 : seule la croissance de `p ↦ M_p` sur `]0, +∞[` est démontrée (`moyP_mono`), avec
  `M_1 = m` ; le cas d'égalité de `h ≤ g` n'est pas démontré (celui de `g ≤ m` l'est).

## Omis

La formule intégrale `e - u_n = (1/n!) ∫₀¹ (1-t)^n e^t dt` (prop. 4.3) ; le lemme de Wallis 2.6,
utilisé par Mathlib mais non énoncé ici ; les cas `p ≤ 0`, la continuité en `0` et les limites en
`±∞` du théorème 3.6 ; l'exemple 3.4 (croissance de `(1 + 1/n)^n`) ; le développement
asymptotique de `ln n!` et les remarques (Pierce, Liouville, Hermite) ; les exercices.
-/

open Real Filter Topology Finset Asymptotics
open scoped Nat

noncomputable section

namespace AutourDeE

/-! ## §1. L'inégalité de la tangente -/

/-- **Lemme 1.1** : `e^x ≥ 1 + x` pour tout réel `x`. -/
theorem tangente (x : ℝ) : 1 + x ≤ exp x := by linarith [add_one_le_exp x]

/-- **Lemme 1.1** (cas d'égalité) : `e^x > 1 + x` pour `x ≠ 0`. -/
theorem tangente_strict {x : ℝ} (hx : x ≠ 0) : 1 + x < exp x := by linarith [add_one_lt_exp hx]

/-- **Lemme 1.1** (forme logarithmique) : `ln y ≤ y - 1` pour `y > 0`, la méthode de la fiche
pour l'inégalité arithmético-géométrique (`Real.log_le_sub_one_of_pos`). -/
theorem log_le_sub_one (y : ℝ) (hy : 0 < y) : log y ≤ y - 1 := Real.log_le_sub_one_of_pos hy

/-! ## §2. Factorielles et formule de Stirling -/

/-- **Lemme 2.1** (minoration) : `2 ≤ (1 + 1/n)^n` (inégalité de Bernoulli). -/
theorem two_le_one_add_inv_pow (n : ℕ) (hn : 1 ≤ n) : 2 ≤ (1 + 1 / (n : ℝ)) ^ n := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h := one_add_mul_le_pow (a := 1 / (n : ℝ)) (by have : (0 : ℝ) ≤ 1 / n := by positivity
                                                      linarith) n
  have : (n : ℝ) * (1 / n) = 1 := by field_simp
  linarith

/-- **Lemme 2.1** (majoration) : `(1 + 1/n)^n < e`. -/
theorem one_add_inv_pow_lt_exp (n : ℕ) (hn : 1 ≤ n) : (1 + 1 / (n : ℝ)) ^ n < exp 1 := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : 1 + 1 / (n : ℝ) < exp (1 / n) := by
    have := add_one_lt_exp (x := 1 / (n : ℝ)) (by positivity)
    linarith
  calc (1 + 1 / (n : ℝ)) ^ n < (exp (1 / n)) ^ n :=
        pow_lt_pow_left₀ h1 (by positivity) (by omega)
    _ = exp 1 := by rw [← exp_nat_mul]; congr 1; field_simp

/-- La suite `u n = n^n / n!` de la section 2. -/
def u (n : ℕ) : ℝ := (n : ℝ) ^ n / n !

lemma u_nonneg (n : ℕ) : 0 ≤ u n := by unfold u; positivity

/-- **Prop. 2.2** : `u (n+1) / u n = (1 + 1/n)^n`. -/
theorem u_succ (n : ℕ) (hn : 1 ≤ n) : u (n + 1) = u n * (1 + 1 / (n : ℝ)) ^ n := by
  have hpos : (n : ℝ) ≠ 0 := by have : (0 : ℝ) < n := by exact_mod_cast hn
                                exact this.ne'
  unfold u
  rw [show (1 + 1 / (n : ℝ)) = ((n : ℝ) + 1) / n by field_simp, div_pow, Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- **Prop. 2.2** : `2^(n-1) ≤ u n ≤ e^(n-1)` pour `n ≥ 1`. -/
theorem u_bounds (n : ℕ) (hn : 1 ≤ n) : (2 : ℝ) ^ (n - 1) ≤ u n ∧ u n ≤ exp 1 ^ (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => simp [u]
  | succ n hn ih =>
    rw [u_succ n hn]
    obtain ⟨h1, h2⟩ := ih
    have a := two_le_one_add_inv_pow n hn
    have b := (one_add_inv_pow_lt_exp n hn).le
    have : n + 1 - 1 = (n - 1) + 1 := by omega
    rw [this, pow_succ, pow_succ]
    exact ⟨mul_le_mul h1 a (by norm_num) (u_nonneg n),
      mul_le_mul h2 b (by positivity) (by positivity)⟩

/-- **Prop. 2.2** : `n^n / e^(n-1) ≤ n! ≤ n^n / 2^(n-1)` pour `n ≥ 1`. -/
theorem factorial_bounds (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) ^ n / exp 1 ^ (n - 1) ≤ n ! ∧ (n ! : ℝ) ≤ (n : ℝ) ^ n / 2 ^ (n - 1) := by
  obtain ⟨h1, h2⟩ := u_bounds n hn
  unfold u at h1 h2
  have hf : (0 : ℝ) < n ! := by positivity
  rw [le_div_iff₀ hf] at h1
  rw [div_le_iff₀ hf] at h2
  constructor
  · rw [div_le_iff₀ (by positivity)]; linarith
  · rw [le_div_iff₀ (by positivity)]; linarith

/-- **Prop. 2.2** : `2^n ≤ u n` pour `n ≥ 6`. -/
theorem two_pow_le_u (n : ℕ) (hn : 6 ≤ n) : (2 : ℝ) ^ n ≤ u n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [u, Nat.factorial]
  | succ n hn ih =>
    rw [u_succ n (by omega), pow_succ]
    exact mul_le_mul ih (two_le_one_add_inv_pow n (by omega)) (by norm_num) (u_nonneg n)

/-- **Prop. 2.2** : `n! ≤ (n/2)^n` pour `n ≥ 6`. -/
theorem factorial_le_half_pow (n : ℕ) (hn : 6 ≤ n) : (n ! : ℝ) ≤ ((n : ℝ) / 2) ^ n := by
  have h := two_pow_le_u n hn
  unfold u at h
  rw [le_div_iff₀ (by positivity)] at h
  rw [div_pow, le_div_iff₀ (by positivity)]
  linarith

/-- **Prop. 2.2** : l'inégalité `n! ≤ (n/2)^n` est fausse pour `n = 5`. -/
theorem u_five_lt : u 5 < 2 ^ 5 := by norm_num [u, Nat.factorial]

/-- **Cor. 2.4** : `n! / a^n → +∞` pour tout `a > 0`. -/
theorem tendsto_factorial_div_pow (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ => (n ! : ℝ) / a ^ n) atTop atTop := by
  have h := FloorSemiring.tendsto_pow_div_factorial_atTop a
  have h' : Tendsto (fun n : ℕ => a ^ n / n !) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨h, Eventually.of_forall fun n => Set.mem_Ioi.2 (by positivity)⟩
  convert h'.inv_tendsto_nhdsGT_zero using 1
  ext n
  simp [inv_div]

/-- **Théorème 2.7** (équivalent) : `n! ~ √(2πn) (n/e)^n`. C'est l'énoncé de Mathlib
`Stirling.factorial_isEquivalent_stirling`, au réordonnancement `2πn = 2nπ` près. -/
theorem stirling :
    (fun n : ℕ => (n ! : ℝ)) ~[atTop] fun n => √(2 * π * n) * ((n : ℝ) / exp 1) ^ n := by
  have e : (fun n : ℕ => √(2 * π * n) * ((n : ℝ) / exp 1) ^ n) =
      fun n : ℕ => √(2 * (n : ℝ) * π) * ((n : ℝ) / exp 1) ^ n := by
    funext n; rw [mul_right_comm]
  rw [e]
  exact Stirling.factorial_isEquivalent_stirling

/-- La suite `w n = ln n! - (n + 1/2) ln n + n` de la fiche. -/
def w (n : ℕ) : ℝ := log n ! - (n + 1 / 2) * log n + n

/-- Lien avec Mathlib : `w n = ln (stirlingSeq n) + (ln 2)/2` pour `n ≥ 1`, où
`stirlingSeq n = n! / (√(2n) (n/e)^n)`. -/
theorem w_eq (n : ℕ) (hn : 1 ≤ n) : w n = log (Stirling.stirlingSeq n) + log 2 / 2 := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Stirling.log_stirlingSeq_formula, w, log_mul (by norm_num) hpos.ne',
    log_div hpos.ne' (exp_pos 1).ne', log_exp]
  ring

/-- **Lemme 2.5** : `1/(3(2n+1)²) ≤ w n - w (n+1) ≤ 1/(12 n (n+1))` pour `n ≥ 1`. La majoration
est la borne de Robbins `Stirling.log_stirlingSeq_sdiff_le` de Mathlib ; la minoration est le
premier terme de la série `Stirling.log_stirlingSeq_sdiff_hasSum`. -/
theorem w_sub_bounds (n : ℕ) (hn : 1 ≤ n) :
    1 / (3 * (2 * (n : ℝ) + 1) ^ 2) ≤ w n - w (n + 1) ∧
      w n - w (n + 1) ≤ 1 / (12 * n * (n + 1)) := by
  rw [w_eq n hn, w_eq (n + 1) (by omega)]
  refine ⟨?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hs := Stirling.log_stirlingSeq_sdiff_hasSum m
    have h0 := le_hasSum hs 0 (fun j _ => by positivity)
    have : (m + 1 + 1 : ℕ) = m + 2 := rfl
    rw [this]
    convert h0 using 1
    · push_cast; field_simp; ring
    · ring
  · have := Stirling.log_stirlingSeq_sdiff_le n
    linarith

/-- **Théorème 2.7** (avec reste) : pour `n ≥ 1`, il existe `θ ∈ ]0, 1]` tel que
`n! = √(2πn) (n/e)^n e^{θ/(12n)}`. -/
theorem stirling_remainder (n : ℕ) (hn : 1 ≤ n) :
    ∃ θ ∈ Set.Ioc (0 : ℝ) 1,
      (n ! : ℝ) = √(2 * π * n) * ((n : ℝ) / exp 1) ^ n * exp (θ / (12 * n)) := by
  set L : ℕ → ℝ := fun k => log (Stirling.stirlingSeq k) with hL
  have hspos : ∀ k : ℕ, 1 ≤ k → 0 < Stirling.stirlingSeq k := fun k hk => by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact Stirling.stirlingSeq'_pos j
  have hpi : 0 < √π := by positivity
  have hLlim : Tendsto L atTop (𝓝 (log √π)) :=
    (Stirling.tendsto_stirlingSeq_sqrt_pi).log hpi.ne'
  -- minoration stricte : `L n > L (n+1) ≥ ln √π`
  have hlow : log √π < L n := by
    have h1 : √π ≤ Stirling.stirlingSeq (n + 1) := Stirling.sqrt_pi_le_stirlingSeq (by omega)
    have h2 := (w_sub_bounds n hn).1
    rw [w_eq n hn, w_eq (n + 1) (by omega)] at h2
    have h3 : 0 < 1 / (3 * (2 * (n : ℝ) + 1) ^ 2) := by positivity
    have h4 := log_le_log hpi h1
    simp only [hL]
    linarith
  -- majoration : `k ↦ L (k+1) - 1/(12(k+1))` est croissante, de limite `ln √π`
  set G : ℕ → ℝ := fun k => L (k + 1) - 1 / (12 * ((k : ℝ) + 1)) with hG
  have hGmono : Monotone G := by
    refine monotone_nat_of_le_succ fun k => ?_
    have h := (w_sub_bounds (k + 1) (by omega)).2
    rw [w_eq (k + 1) (by omega), w_eq (k + 1 + 1) (by omega)] at h
    simp only [hG, hL]
    push_cast at h ⊢
    have e : 1 / (12 * ((k : ℝ) + 1) * ((k : ℝ) + 1 + 1)) =
        1 / (12 * ((k : ℝ) + 1)) - 1 / (12 * ((k : ℝ) + 1 + 1)) := by
      field_simp; ring
    linarith
  have hGlim : Tendsto G atTop (𝓝 (log √π)) := by
    have h1 : Tendsto (fun k : ℕ => L (k + 1)) atTop (𝓝 (log √π)) :=
      hLlim.comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun k : ℕ => 1 / (12 * ((k : ℝ) + 1))) atTop (𝓝 0) := by
      refine tendsto_const_nhds.div_atTop ?_
      exact Tendsto.const_mul_atTop (by norm_num)
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    have := h1.sub h2
    rw [sub_zero] at this
    exact this
  have hup : L n - 1 / (12 * (n : ℝ)) ≤ log √π := by
    have := hGmono.ge_of_tendsto hGlim (n - 1)
    simp only [hG] at this
    have e : n - 1 + 1 = n := by omega
    rw [e] at this
    have e' : ((n - 1 : ℕ) : ℝ) + 1 = n := by
      rw [Nat.cast_sub hn]; push_cast; ring
    rw [e'] at this
    exact this
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨12 * n * (L n - log √π), ⟨by positivity, ?_⟩, ?_⟩
  · have : L n - log √π ≤ 1 / (12 * n) := by linarith
    calc 12 * n * (L n - log √π) ≤ 12 * n * (1 / (12 * n)) := by gcongr
      _ = 1 := by field_simp
  · have hθ : 12 * n * (L n - log √π) / (12 * n) = L n - log √π := by field_simp
    rw [hθ, exp_sub, exp_log (hspos n hn), exp_log hpi]
    simp only [Stirling.stirlingSeq]
    have h2 : √(2 * π * n) = √π * √(2 * n) := by
      rw [← sqrt_mul (by positivity)]; ring_nf
    rw [h2]
    have : 0 < √(2 * (n : ℝ)) := by positivity
    have : 0 < ((n : ℝ) / exp 1) ^ n := by positivity
    field_simp

/-! ## §3. Inégalités entre moyennes -/

section Moyennes

variable {ι : Type*} (s : Finset ι) (a : ι → ℝ)

/-- Moyenne arithmétique `m`. -/
def moyA : ℝ := (∑ i ∈ s, a i) / s.card
/-- Moyenne géométrique `g = (∏ aᵢ)^{1/n}`, écrite `∏ aᵢ^{1/n}`. -/
def moyG : ℝ := ∏ i ∈ s, a i ^ ((1 : ℝ) / s.card)
/-- Moyenne harmonique `h`, définie par `1/h = (1/n) ∑ 1/aᵢ`. -/
def moyH : ℝ := s.card / ∑ i ∈ s, 1 / a i

variable {s a}

lemma sum_weights (hs : s.Nonempty) : ∑ _i ∈ s, (1 : ℝ) / s.card = 1 := by
  have : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  rw [sum_const, nsmul_eq_mul]; field_simp

lemma moyA_eq : moyA s a = ∑ i ∈ s, (1 : ℝ) / s.card * a i := by
  rw [moyA, ← mul_sum]; ring

/-- **Théorème 3.2** : `g ≤ m` (inégalité arithmético-géométrique, `Real.geom_mean_le_arith_mean_weighted`
de Mathlib, avec les poids `1/n`). -/
theorem moyG_le_moyA (hs : s.Nonempty) (ha : ∀ i ∈ s, 0 < a i) : moyG s a ≤ moyA s a := by
  rw [moyA_eq, moyG]
  exact Real.geom_mean_le_arith_mean_weighted s _ a (fun _ _ => by positivity)
    (sum_weights hs) (fun i hi => (ha i hi).le)

/-- **Théorème 3.2** (cas d'égalité) : `g = m` si et seulement si les `aᵢ` sont tous égaux. -/
theorem moyG_eq_moyA_iff (hs : s.Nonempty) (ha : ∀ i ∈ s, 0 < a i) :
    moyG s a = moyA s a ↔ ∀ j ∈ s, ∀ k ∈ s, a j = a k := by
  rw [moyA_eq, moyG]
  have : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  exact Real.geom_mean_eq_arith_mean_weighted_iff_of_pos s _ a (fun _ _ => by positivity)
    (sum_weights hs) (fun i hi => (ha i hi).le)

/-- **Théorème 3.2** : `h ≤ g` (`Real.harm_mean_le_geom_mean_weighted` de Mathlib). -/
theorem moyH_le_moyG (hs : s.Nonempty) (ha : ∀ i ∈ s, 0 < a i) : moyH s a ≤ moyG s a := by
  have : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have h := Real.harm_mean_le_geom_mean_weighted s (fun _ => (1 : ℝ) / s.card) a hs
    (fun _ _ => by positivity) (sum_weights hs) ha
  have e : moyH s a = (∑ i ∈ s, (1 : ℝ) / s.card / a i)⁻¹ := by
    rw [moyH, ← inv_div, sum_div]
    congr 1
    exact sum_congr rfl fun i _ => div_right_comm _ _ _
  rw [e, moyG]
  exact h

variable (s a) in
/-- Moyenne d'ordre `p ≠ 0` : `M_p = ((1/n) ∑ aᵢ^p)^{1/p}`. -/
def moyP (p : ℝ) : ℝ := ((∑ i ∈ s, a i ^ p) / s.card) ^ (1 / p)

/-- `M_1 = m`. -/
theorem moyP_one : moyP s a 1 = moyA s a := by simp [moyP, moyA]

/-- **Théorème 3.6**, cas `0 < p ≤ q` : `M_p ≤ M_q` (Jensen pour `x ↦ x^{q/p}`, via
`Real.rpow_arith_mean_le_arith_mean_rpow`). -/
theorem moyP_mono (hs : s.Nonempty) (ha : ∀ i ∈ s, 0 < a i) {p q : ℝ} (hp : 0 < p)
    (hpq : p ≤ q) : moyP s a p ≤ moyP s a q := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hq : 0 < q := hp.trans_le hpq
  have key := Real.rpow_arith_mean_le_arith_mean_rpow s (fun _ => (1 : ℝ) / s.card)
    (fun i => a i ^ p) (fun _ _ => by positivity) (sum_weights hs)
    (fun i hi => (rpow_pos_of_pos (ha i hi) p).le) (p := q / p) (by rw [le_div_iff₀ hp]; linarith)
  have hA : ∑ i ∈ s, (1 : ℝ) / s.card * a i ^ p = (∑ i ∈ s, a i ^ p) / s.card := by
    rw [← mul_sum]; ring
  have hB : ∑ i ∈ s, (1 : ℝ) / s.card * (a i ^ p) ^ (q / p) = (∑ i ∈ s, a i ^ q) / s.card := by
    rw [← mul_sum, one_div_mul_eq_div]
    congr 1
    refine sum_congr rfl fun i hi => ?_
    rw [← rpow_mul (ha i hi).le]
    congr 1
    field_simp
  rw [hA, hB] at key
  have hA0 : 0 ≤ (∑ i ∈ s, a i ^ p) / s.card :=
    div_nonneg (sum_nonneg fun i hi => (rpow_pos_of_pos (ha i hi) p).le) hc.le
  have := rpow_le_rpow (rpow_nonneg hA0 _) key (by positivity : (0 : ℝ) ≤ 1 / q)
  rw [← rpow_mul hA0] at this
  unfold moyP
  convert this using 2
  field_simp

end Moyennes

/-- **Exemple 3.1** : pour `(4, 10, 25)`, `m = 13`. -/
theorem ex_moyA : moyA univ ![(4 : ℝ), 10, 25] = 13 := by
  simp [moyA, Fin.sum_univ_three]; norm_num

/-- **Exemple 3.1** : `g = 10`. -/
theorem ex_moyG : moyG univ ![(4 : ℝ), 10, 25] = 10 := by
  simp only [moyG, Fin.prod_univ_three, card_univ, Fintype.card_fin]
  rw [← mul_rpow (by norm_num) (by norm_num), ← mul_rpow (by norm_num) (by norm_num)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  rw [show (4 : ℝ) * 10 * 25 = 10 ^ (3 : ℝ) by norm_num, ← rpow_mul (by norm_num)]
  norm_num

/-- **Exemple 3.1** : `h = 100/13`. -/
theorem ex_moyH : moyH univ ![(4 : ℝ), 10, 25] = 100 / 13 := by
  simp [moyH, Fin.sum_univ_three]; norm_num

/-- **Exemple 3.1** : pour une progression géométrique `(a, ar, ar²)`, `m h = g²`. -/
theorem geom_prog_mul (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    (a + a * r + a * r ^ 2) / 3 * (3 / (1 / a + 1 / (a * r) + 1 / (a * r ^ 2))) = (a * r) ^ 2 := by
  have : 0 < 1 + r + r ^ 2 := by positivity
  field_simp
  ring

/-- **Exemple 3.1** : contre-exemple `(1, 1, 4)` : `m h = 8/3` mais `g² = 4^{2/3} ≠ 8/3`. -/
theorem ex_114 : (1 + 1 + 4 : ℝ) / 3 * (3 / (1 / 1 + 1 / 1 + 1 / 4)) = 8 / 3 ∧
    ((4 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 ≠ 8 / 3 := by
  refine ⟨by norm_num, fun h => ?_⟩
  have h3 : (((4 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2) ^ 3 = 16 := by
    rw [← pow_mul, ← rpow_natCast, ← rpow_mul (by norm_num)]
    norm_num
  rw [h] at h3
  norm_num at h3

/-! ## §4. Deux suites adjacentes de limite e -/

/-- `U n = ∑_{k ≤ n} 1/k!` (la suite `u_n` de la section 4). -/
def U (n : ℕ) : ℝ := ∑ k ∈ range (n + 1), 1 / (k ! : ℝ)

/-- `V n = U n + 1/(n · n!)` (la suite `v_n` de la section 4). -/
def V (n : ℕ) : ℝ := U n + 1 / (n * n ! : ℝ)

lemma U_succ (n : ℕ) : U (n + 1) = U n + 1 / ((n + 1) ! : ℝ) := by
  rw [U, sum_range_succ, ← U]

/-- **Prop. 4.1** : `(U n)` est strictement croissante. -/
theorem U_strictMono : StrictMono U := by
  refine strictMono_nat_of_lt_succ (f := U) fun n => ?_
  rw [U_succ]
  have : (0 : ℝ) < (n + 1) ! := by positivity
  linarith [one_div_pos.2 this]

/-- **Prop. 4.1** : `V (n+1) - V n = -1/(n (n+1) (n+1)!)` pour `n ≥ 1`. -/
theorem V_succ_sub (n : ℕ) (hn : 1 ≤ n) :
    V (n + 1) - V n = -1 / (n * (n + 1) * ((n + 1) ! : ℝ)) := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [V, V, U_succ, Nat.factorial_succ]
  push_cast
  have : (0 : ℝ) < n ! := by positivity
  field_simp
  ring

/-- **Prop. 4.1** : `(V n)_{n ≥ 1}` est strictement décroissante. -/
theorem V_strictAnti : StrictAnti fun n => V (n + 1) :=
  strictAnti_nat_of_succ_lt fun n => by
    have h := V_succ_sub (n + 1) (by omega)
    have : 0 < ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) + 1) * ((n + 1 + 1) ! : ℝ) := by positivity
    have : -1 / (((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) + 1) * ((n + 1 + 1) ! : ℝ)) < 0 :=
      div_neg_of_neg_of_pos (by norm_num) this
    linarith

/-- **Prop. 4.3** : `U n → e`, c'est-à-dire `e = ∑ 1/k!` (série exponentielle de Mathlib,
`NormedSpace.expSeries_div_hasSum_exp`). -/
theorem tendsto_U : Tendsto U atTop (𝓝 (exp 1)) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (1 : ℝ)
  rw [← Real.exp_eq_exp_ℝ] at h
  refine (h.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).congr fun n => ?_
  simp [U]

/-- **Prop. 4.1** : `V n - U n → 0`. -/
theorem tendsto_V_sub_U : Tendsto (fun n => V n - U n) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) * n !)) atTop (𝓝 0) := by
    refine tendsto_const_nhds.div_atTop ?_
    refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
    have : (1 : ℝ) ≤ n ! := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero n)
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  simpa [V] using h

/-- **Prop. 4.1** et **prop. 4.3** : `U n < e < V n` pour `n ≥ 1` ; la limite commune
`ℓ` des deux suites adjacentes est `e`. -/
theorem U_lt_e_lt_V (n : ℕ) (hn : 1 ≤ n) : U n < exp 1 ∧ exp 1 < V n := by
  constructor
  · exact (U_strictMono (Nat.lt_succ_self n)).trans_le
      (U_strictMono.monotone.ge_of_tendsto tendsto_U (n + 1))
  · have hV : Tendsto (fun n => V (n + 1)) atTop (𝓝 (exp 1)) := by
      have := (tendsto_V_sub_U.add tendsto_U).comp (tendsto_add_atTop_nat 1)
      simpa [Function.comp_def] using this
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact (V_strictAnti.antitone.le_of_tendsto hV (m + 1)).trans_lt
      (V_strictAnti (Nat.lt_succ_self m))

/-- **Prop. 4.3** : `1/(n+1)! < e - U n < e/(n+1)!`. La preuve n'utilise pas la formule de
Taylor : la minoration vient de `U (n+1) < e`, la majoration de `e < V n` et de `(n+1)/n ≤ 2 < e`. -/
theorem e_sub_U_bounds (n : ℕ) :
    1 / ((n + 1) ! : ℝ) < exp 1 - U n ∧ exp 1 - U n < exp 1 / ((n + 1) ! : ℝ) := by
  have he : (2 : ℝ) < exp 1 := lt_trans (by norm_num) exp_one_gt_d9
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hU0 : U 0 = 1 := by simp [U]
    have hf0 : ((0 + 1) ! : ℝ) = 1 := by norm_num
    rw [hU0, hf0, div_one, div_one]
    exact ⟨by linarith, by linarith⟩
  have h1 := (U_lt_e_lt_V (n + 1) (by omega)).1
  have h2 := (U_lt_e_lt_V n hn).2
  rw [U_succ] at h1
  refine ⟨by linarith, ?_⟩
  rw [V] at h2
  have hnpos : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hf : (0 : ℝ) < n ! := by positivity
  have : 1 / ((n : ℝ) * n !) ≤ exp 1 / ((n + 1) ! : ℝ) := by
    rw [Nat.factorial_succ]; push_cast
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : (n : ℝ) + 1 ≤ exp 1 * n := by nlinarith
    have h4 : ((n : ℝ) + 1) * n ! ≤ exp 1 * n * n ! := mul_le_mul_of_nonneg_right h3 hf.le
    linarith
  linarith

/-- `q! · U q` est un entier. -/
lemma factorial_mul_U (q : ℕ) :
    (q ! : ℝ) * U q = ((∑ k ∈ range (q + 1), q ! / k ! : ℕ) : ℝ) := by
  rw [U, mul_sum, Nat.cast_sum]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ q := Nat.lt_succ_iff.1 (mem_range.1 hk)
  rw [Nat.cast_div (Nat.factorial_dvd_factorial hk') (by positivity)]
  ring

/-- **Théorème 4.5** (cœur de la preuve) : `e ≠ p/q` pour `p ∈ ℤ`, `q ≥ 1`. Si `e = p/q`, l'entier
`p q! - q (q! U q)` serait strictement compris entre `0` et `1`. -/
theorem exp_one_ne_div (p : ℤ) (q : ℕ) (hq : 1 ≤ q) : exp 1 ≠ p / q := by
  intro h
  obtain ⟨h1, h2⟩ := U_lt_e_lt_V q hq
  obtain ⟨M, hM⟩ : ∃ M : ℕ, (q ! : ℝ) * U q = M := ⟨_, factorial_mul_U q⟩
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hf : (0 : ℝ) < q ! := by positivity
  set X : ℤ := p * (q ! : ℤ) - (q : ℤ) * M with hX
  have hXr : (X : ℝ) = q * q ! * exp 1 - q * ((q ! : ℝ) * U q) := by
    rw [hX, hM, h]; push_cast; field_simp
  have hlo : (0 : ℝ) < X := by
    rw [hXr]
    have : q * q ! * U q < q * q ! * exp 1 := by gcongr
    nlinarith
  have hhi : (X : ℝ) < 1 := by
    rw [hXr]; rw [V] at h2
    have : q * q ! * exp 1 < q * q ! * (U q + 1 / (q * q ! : ℝ)) := by gcongr
    have e : (q : ℝ) * q ! * (U q + 1 / (q * q ! : ℝ)) = q * q ! * U q + 1 := by field_simp
    nlinarith
  have a : (0 : ℤ) < X := by exact_mod_cast hlo
  have b : X < 1 := by exact_mod_cast hhi
  omega

/-- **Théorème 4.5** : `e` est irrationnel. -/
theorem irrational_exp_one : Irrational (exp 1) := by
  rw [irrational_iff_ne_rational]
  intro a b hb h
  rcases lt_or_gt_of_ne hb with hneg | hpos
  · apply exp_one_ne_div (-a) b.natAbs (by omega)
    rw [h, Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast hneg)]
    push_cast; rw [neg_div_neg_eq]
  · apply exp_one_ne_div a b.natAbs (by omega)
    rw [h, Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hpos)]

end AutourDeE

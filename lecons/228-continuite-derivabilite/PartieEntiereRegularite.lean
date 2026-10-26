import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Darboux
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Algebra.Order.Floor

/-!
# Partie entière et régularité

Formalisation de la fiche « Partie entière et régularité » (M. Hua, octobre 2026),
leçon 228.

## Modèles

* La partie entière `E(x)` est `(⌊x⌋ : ℝ)` (`Int.floor`, vu dans `ℝ`).
* Les limites à gauche et à droite `g(a⁻)`, `g(a⁺)` sont des `Tendsto g (𝓝[<] a) (𝓝 ℓ)` et
  `Tendsto g (𝓝[>] a) (𝓝 ℓ)`. La dérivée à gauche (resp. à droite) `φ'_g(a) = d` est
  `HasDerivWithinAt φ d (Iio a) a` (resp. `Ioi a`).
* La fonction de l'exercice d'origine est étudiée sur `ℝ` tout entier (`F`) ; sa restriction à
  `[-1, 2]` hérite de toutes les propriétés énoncées.
* « `f` est `m` fois dérivable » est traduit, pour `m = 2`, par la dérivabilité de `deriv f`.

## Écarts avec la fiche

Aucun énoncé de la fiche ne s'est révélé faux. Pour la dérivée de `sin (π x)`, Lean écrit
`cos (π x) * π` au lieu de `π cos (π x)`, et `cos (π k) = (-1)^k` est remplacé par le fait
que `cos (π k) ≠ 0`, qui suffit.

## Omis

Le lemme de troncature 3.2 et le théorème de recollement 3.3 dans leur généralité (classe
`C^{r-1}` exacte pour un ordre d'annulation `r` quelconque), le lemme 3.5 (ordre d'annulation de
`sin^m (π x)`) et le corollaire 3.6 pour `m ≥ 3` : seuls les cas `m = 1` et `m = 2` sont
traités, directement. Sont aussi omis l'exemple `x² sin (1/x)`, l'exercice 3 (recollement de
`exp` et de son polynôme de Taylor) et le calcul de l'intégrale `∫₀ˣ E` dans l'exercice 5, dont
on formalise la formule close `G(x) = n x - n(n+1)/2` comme définition, ainsi que
l'exercice 5.3 (points de dérivabilité de `G`). Dans l'exercice 1, seuls la discontinuité aux
entiers `k ≠ 1` et le comportement en `1` sont formalisés. La proposition 4.1 (limite de la
dérivée) et le théorème de Darboux 4.4 ne sont pas redémontrés : on utilise
`hasDerivWithinAt_Iic_of_tendsto_deriv`, `hasDerivWithinAt_Ici_of_tendsto_deriv` et
`exists_hasDerivWithinAt_eq_of_gt_of_lt` de mathlib.

Les numéros d'énoncés sont ceux de la fiche.
-/

open Real
open Filter Topology Set

noncomputable section

namespace PartieEntiereRegularite

/-! ## §1. Produit d'une fonction à sauts par une fonction qui s'annule -/

/-- **Prop. 2.1 (1)** : si `g` a des limites finies à gauche et à droite en `a` et si `h` est
continue en `a` avec `h(a) = 0`, alors `g h` est continue en `a`. -/
theorem continuousAt_mul_of_jump {g h : ℝ → ℝ} {a gl gr : ℝ}
    (hgl : Tendsto g (𝓝[<] a) (𝓝 gl)) (hgr : Tendsto g (𝓝[>] a) (𝓝 gr))
    (hh : ContinuousAt h a) (ha : h a = 0) : ContinuousAt (fun x => g x * h x) a := by
  have h0 : Tendsto h (𝓝 a) (𝓝 0) := by simpa [ha] using hh.tendsto
  rw [continuousAt_iff_continuous_left'_right']
  constructor
  · simpa [ContinuousWithinAt, ha] using hgl.mul (h0.mono_left nhdsWithin_le_nhds)
  · simpa [ContinuousWithinAt, ha] using hgr.mul (h0.mono_left nhdsWithin_le_nhds)

/-- **Prop. 2.1 (2)**, à gauche : `(g h)'_g(a) = g(a⁻) h'(a)`. -/
theorem hasDerivWithinAt_Iio_mul {g h : ℝ → ℝ} {a gl h' : ℝ}
    (hgl : Tendsto g (𝓝[<] a) (𝓝 gl)) (hh : HasDerivAt h h' a) (ha : h a = 0) :
    HasDerivWithinAt (fun x => g x * h x) (gl * h') (Iio a) a := by
  rw [hasDerivWithinAt_iff_tendsto_slope' (by simp : a ∉ Iio a)]
  have hs : Tendsto (slope h a) (𝓝[<] a) (𝓝 h') :=
    (hasDerivAt_iff_tendsto_slope.1 hh).mono_left
      (nhdsWithin_mono _ fun x hx => (ne_of_lt (show x < a from hx) : x ≠ a))
  refine Tendsto.congr' ?_ (hgl.mul hs)
  filter_upwards with x
  simp [slope_def_field, ha, mul_div_assoc]

/-- **Prop. 2.1 (2)**, à droite : `(g h)'_d(a) = g(a⁺) h'(a)`. -/
theorem hasDerivWithinAt_Ioi_mul {g h : ℝ → ℝ} {a gr h' : ℝ}
    (hgr : Tendsto g (𝓝[>] a) (𝓝 gr)) (hh : HasDerivAt h h' a) (ha : h a = 0) :
    HasDerivWithinAt (fun x => g x * h x) (gr * h') (Ioi a) a := by
  rw [hasDerivWithinAt_iff_tendsto_slope' (by simp : a ∉ Ioi a)]
  have hs : Tendsto (slope h a) (𝓝[>] a) (𝓝 h') :=
    (hasDerivAt_iff_tendsto_slope.1 hh).mono_left
      (nhdsWithin_mono _ fun x hx => (ne_of_gt (show a < x from hx) : x ≠ a))
  refine Tendsto.congr' ?_ (hgr.mul hs)
  filter_upwards with x
  simp [slope_def_field, ha, mul_div_assoc]

/-- Une fonction qui a la même dérivée `d` à gauche et à droite en `a` est dérivable en `a`,
de dérivée `d`. -/
lemma hasDerivAt_of_Iio_Ioi {f : ℝ → ℝ} {a d : ℝ} (hL : HasDerivWithinAt f d (Iio a) a)
    (hR : HasDerivWithinAt f d (Ioi a) a) : HasDerivAt f d a := by
  have := hL.Iic_of_Iio.union hR.Ici_of_Ioi
  rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this

/-- **Prop. 2.1 (3)** : `g h` est dérivable en `a` si et seulement si `h'(a) = 0` ou
`g(a⁻) = g(a⁺)`. -/
theorem differentiableAt_mul_iff {g h : ℝ → ℝ} {a gl gr h' : ℝ}
    (hgl : Tendsto g (𝓝[<] a) (𝓝 gl)) (hgr : Tendsto g (𝓝[>] a) (𝓝 gr))
    (hh : HasDerivAt h h' a) (ha : h a = 0) :
    DifferentiableAt ℝ (fun x => g x * h x) a ↔ h' = 0 ∨ gl = gr := by
  have hL := hasDerivWithinAt_Iio_mul hgl hh ha
  have hR := hasDerivWithinAt_Ioi_mul hgr hh ha
  constructor
  · intro hd
    have e1 := UniqueDiffWithinAt.eq_deriv _ (uniqueDiffWithinAt_Iio a)
      hd.hasDerivAt.hasDerivWithinAt hL
    have e2 := UniqueDiffWithinAt.eq_deriv _ (uniqueDiffWithinAt_Ioi a)
      hd.hasDerivAt.hasDerivWithinAt hR
    have : (gl - gr) * h' = 0 := by linear_combination e2 - e1
    exact (mul_eq_zero.1 this).symm.imp_right sub_eq_zero.1
  · intro H
    have e : gr * h' = gl * h' := by rcases H with H | H <;> simp [H]
    exact (hasDerivAt_of_Iio_Ioi hL (hR.congr_deriv e)).differentiableAt

/-! ### La partie entière -/

/-- `E(k⁻) = k - 1`. -/
lemma floor_left (k : ℤ) : Tendsto (fun x : ℝ => (⌊x⌋ : ℝ)) (𝓝[<] (k : ℝ)) (𝓝 ((k : ℝ) - 1)) :=
  tendsto_floor_left' k

/-- `E(k⁺) = k`. -/
lemma floor_right (k : ℤ) : Tendsto (fun x : ℝ => (⌊x⌋ : ℝ)) (𝓝[>] (k : ℝ)) (𝓝 (k : ℝ)) :=
  (tendsto_floor_right' k).mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)

/-- Hors des entiers, `E` est localement constante. -/
lemma floor_eventuallyEq {x : ℝ} (hx : ∀ k : ℤ, x ≠ k) :
    ∀ᶠ y in 𝓝 x, (⌊y⌋ : ℝ) = ⌊x⌋ := by
  have h1 : (⌊x⌋ : ℝ) < x := lt_of_le_of_ne (Int.floor_le x) (hx _).symm
  have h2 : x < ⌊x⌋ + 1 := Int.lt_floor_add_one x
  filter_upwards [Ioo_mem_nhds h1 h2] with y hy
  exact_mod_cast Int.floor_eq_iff.2 ⟨hy.1.le, hy.2⟩

/-- Si `h` est continue et nulle sur `ℤ`, alors `x ↦ E(x) h(x)` est continue sur `ℝ`
(**cor. 2.3**, continuité, pour un `h` quelconque). -/
theorem continuous_floor_mul {h : ℝ → ℝ} (hc : Continuous h) (h0 : ∀ k : ℤ, h k = 0) :
    Continuous (fun x => (⌊x⌋ : ℝ) * h x) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : ∃ k : ℤ, x = k
  · obtain ⟨k, rfl⟩ := hx
    exact continuousAt_mul_of_jump (floor_left k) (floor_right k) hc.continuousAt (h0 k)
  · simp only [not_exists] at hx
    have hc' : ContinuousAt (fun y => (⌊x⌋ : ℝ) * h y) x := continuousAt_const.mul hc.continuousAt
    refine hc'.congr ?_
    filter_upwards [floor_eventuallyEq hx] with y hy
    rw [hy]

/-- Hors des entiers, `(E h)' = E h'`. -/
theorem hasDerivAt_floor_mul {h : ℝ → ℝ} {x h' : ℝ} (hx : ∀ k : ℤ, x ≠ k)
    (hh : HasDerivAt h h' x) : HasDerivAt (fun y => (⌊y⌋ : ℝ) * h y) (⌊x⌋ * h') x := by
  refine (hh.const_mul (⌊x⌋ : ℝ)).congr_of_eventuallyEq ?_
  filter_upwards [floor_eventuallyEq hx] with y hy
  rw [hy]

/-! ### La fonction `F(x) = E(x) sin(π x)` -/

/-- `F(x) = E(x) sin(π x)`. -/
def F (x : ℝ) : ℝ := ⌊x⌋ * sin (π * x)

lemma hasDerivAt_sin_pi (x : ℝ) : HasDerivAt (fun y => sin (π * y)) (cos (π * x) * π) x := by
  simpa using ((hasDerivAt_id x).const_mul π).sin

lemma sin_pi_int (k : ℤ) : sin (π * k) = 0 := by rw [mul_comm]; exact sin_int_mul_pi k

lemma cos_pi_int_ne_zero (k : ℤ) : cos (π * k) ≠ 0 := by
  rw [mul_comm, cos_int_mul_pi]; exact zpow_ne_zero _ (by norm_num)

/-- **Cor. 2.3** : `F` est continue sur `ℝ`. -/
theorem continuous_F : Continuous F :=
  continuous_floor_mul (by fun_prop) sin_pi_int

/-- **Cor. 2.3** : `F'_g(k) = (k - 1) π cos(π k)`. -/
theorem F_left (k : ℤ) : HasDerivWithinAt F (((k : ℝ) - 1) * (cos (π * k) * π)) (Iio k) k :=
  hasDerivWithinAt_Iio_mul (floor_left k) (hasDerivAt_sin_pi k) (sin_pi_int k)

/-- **Cor. 2.3** : `F'_d(k) = k π cos(π k)`. -/
theorem F_right (k : ℤ) : HasDerivWithinAt F ((k : ℝ) * (cos (π * k) * π)) (Ioi k) k :=
  hasDerivWithinAt_Ioi_mul (floor_right k) (hasDerivAt_sin_pi k) (sin_pi_int k)

/-- **Cor. 2.3** : `F` n'est dérivable en aucun entier. -/
theorem not_differentiableAt_F (k : ℤ) : ¬ DifferentiableAt ℝ F k := by
  have := differentiableAt_mul_iff (floor_left k) (floor_right k) (hasDerivAt_sin_pi k)
    (sin_pi_int k)
  change ¬ DifferentiableAt ℝ (fun x : ℝ => (⌊x⌋ : ℝ) * sin (π * x)) k
  rw [this]
  rintro (h | h)
  · exact mul_ne_zero (cos_pi_int_ne_zero k) pi_ne_zero h
  · linarith

/-- **Cor. 2.3** : `F` est dérivable hors des entiers. -/
theorem differentiableAt_F {x : ℝ} (hx : ∀ k : ℤ, x ≠ k) : DifferentiableAt ℝ F x :=
  (hasDerivAt_floor_mul hx (hasDerivAt_sin_pi x)).differentiableAt

/-! ## §2. L'exercice d'origine -/

/-- **Exemple 1.1** : `f'_g(0) = -π`. -/
theorem F_left_zero : HasDerivWithinAt F (-π) (Iio 0) 0 := by
  simpa using F_left 0

/-- **Exemple 1.1** : `f'_d(0) = 0`. -/
theorem F_right_zero : HasDerivWithinAt F 0 (Ioi 0) 0 := by
  simpa using F_right 0

/-- **Exemple 1.1** : `f'_g(1) = 0`. -/
theorem F_left_one : HasDerivWithinAt F 0 (Iio 1) 1 := by
  simpa using F_left 1

/-- **Exemple 1.1** : `f'_d(1) = -π`. -/
theorem F_right_one : HasDerivWithinAt F (-π) (Ioi 1) 1 := by
  simpa using F_right 1

/-- **Exemple 1.1** : `f` n'est dérivable ni en `0` ni en `1`. -/
theorem not_differentiableAt_F_zero_one :
    ¬ DifferentiableAt ℝ F 0 ∧ ¬ DifferentiableAt ℝ F 1 := by
  constructor
  · simpa using not_differentiableAt_F 0
  · simpa using not_differentiableAt_F 1

/-- **Exemple 1.1** : sur `[1, 2]`, `f(x) = sin(π x)` (y compris en `2`, où `f(2) = 2 sin 2π = 0`). -/
theorem F_eqOn : EqOn F (fun x => sin (π * x)) (Icc 1 2) := by
  intro x hx
  rcases eq_or_lt_of_le hx.2 with h | h
  · subst h
    simp [F, show π * 2 = 2 * π by ring]
  · have : ⌊x⌋ = 1 := Int.floor_eq_iff.2 ⟨by exact_mod_cast hx.1, by norm_num [h]⟩
    simp [F, this]

/-- **Exemple 1.1** : `f` est strictement décroissante sur `[1, 3/2]`. -/
theorem F_strictAntiOn : StrictAntiOn F (Icc 1 (3 / 2)) := by
  intro a ha b hb hab
  have ha' : a ∈ Icc (1 : ℝ) 2 := ⟨ha.1, by linarith [ha.2]⟩
  have hb' : b ∈ Icc (1 : ℝ) 2 := ⟨hb.1, by linarith [hb.2]⟩
  rw [F_eqOn ha', F_eqOn hb']
  simp only
  have key : sin (π * a - π) < sin (π * b - π) := by
    apply strictMonoOn_sin
    · constructor <;> nlinarith [pi_pos, ha.1, ha.2]
    · constructor <;> nlinarith [pi_pos, hb.1, hb.2]
    · nlinarith [pi_pos]
  rw [sin_sub_pi, sin_sub_pi] at key
  linarith

/-- **Exemple 1.1** : `f` est strictement croissante sur `[3/2, 2]`. -/
theorem F_strictMonoOn : StrictMonoOn F (Icc (3 / 2) 2) := by
  intro a ha b hb hab
  have ha' : a ∈ Icc (1 : ℝ) 2 := ⟨by linarith [ha.1], ha.2⟩
  have hb' : b ∈ Icc (1 : ℝ) 2 := ⟨by linarith [hb.1], hb.2⟩
  rw [F_eqOn ha', F_eqOn hb']
  simp only
  have key : sin (π * a - 2 * π) < sin (π * b - 2 * π) := by
    apply strictMonoOn_sin
    · constructor <;> nlinarith [pi_pos, ha.1, ha.2]
    · constructor <;> nlinarith [pi_pos, hb.1, hb.2]
    · nlinarith [pi_pos]
  rwa [sin_sub_two_pi, sin_sub_two_pi] at key

/-- **Exemple 1.1** : le minimum de `f` sur `[1, 2]` vaut `f(3/2) = -1`. -/
theorem F_three_halves : F (3 / 2) = -1 := by
  rw [F_eqOn ⟨by norm_num, by norm_num⟩]
  show sin (π * (3 / 2)) = -1
  rw [show π * (3 / 2) = π / 2 + π by ring, sin_add_pi, sin_pi_div_two]

/-! ## §3. Régularité exacte : les cas `m = 1` et `m = 2` -/

/-- **Cor. 3.6, `m = 1`** : `f₁ = F` est `C⁰` et n'est dérivable en aucun entier. -/
theorem f1_regularity : Continuous F ∧ ∀ k : ℤ, ¬ DifferentiableAt ℝ F k :=
  ⟨continuous_F, not_differentiableAt_F⟩

/-- `f₂(x) = E(x) sin²(π x)`. -/
def f2 (x : ℝ) : ℝ := ⌊x⌋ * sin (π * x) ^ 2

/-- La dérivée de `f₂` (**exercice 2**) : `f₂'(x) = π E(x) sin(2π x)`, écrite `E(x) (π sin(2π x))`. -/
def f2' (x : ℝ) : ℝ := ⌊x⌋ * (π * sin (2 * π * x))

lemma hasDerivAt_sin_pi_sq (x : ℝ) :
    HasDerivAt (fun y => sin (π * y) ^ 2) (π * sin (2 * π * x)) x := by
  have := (hasDerivAt_sin_pi x).pow 2
  convert this using 1
  rw [show 2 * π * x = 2 * (π * x) by ring, sin_two_mul]
  push_cast
  ring

lemma sin_two_pi_int (k : ℤ) : sin (2 * π * k) = 0 := by
  rw [show 2 * π * (k : ℝ) = ((2 * k : ℤ) : ℝ) * π by push_cast; ring]
  exact sin_int_mul_pi _

lemma cos_two_pi_int (k : ℤ) : cos (2 * π * k) = 1 := by
  rw [show 2 * π * (k : ℝ) = k * (2 * π) by ring]
  exact cos_int_mul_two_pi k

/-- **Exercice 2** : `f₂` est dérivable sur `ℝ`, de dérivée `π E(x) sin(2π x)`. -/
theorem hasDerivAt_f2 (x : ℝ) : HasDerivAt f2 (f2' x) x := by
  by_cases hx : ∃ k : ℤ, x = k
  · obtain ⟨k, rfl⟩ := hx
    have h0 : sin (π * k) ^ 2 = 0 := by rw [sin_pi_int]; ring
    have hd := hasDerivAt_sin_pi_sq (k : ℝ)
    rw [sin_two_pi_int] at hd
    have hL := hasDerivWithinAt_Iio_mul (floor_left k) hd h0
    have hR := hasDerivWithinAt_Ioi_mul (floor_right k) hd h0
    have e : f2' k = 0 := by simp [f2', sin_two_pi_int]
    rw [e]
    exact hasDerivAt_of_Iio_Ioi (hL.congr_deriv (by ring)) (hR.congr_deriv (by ring))
  · simp only [not_exists] at hx
    exact hasDerivAt_floor_mul hx (hasDerivAt_sin_pi_sq x)

theorem deriv_f2 : deriv f2 = f2' := funext fun x => (hasDerivAt_f2 x).deriv

/-- **Cor. 3.6, `m = 2`** : `f₂` est de classe `C¹` sur `ℝ`. -/
theorem contDiff_one_f2 : ContDiff ℝ 1 f2 := by
  rw [contDiff_one_iff_deriv, deriv_f2]
  refine ⟨fun x => (hasDerivAt_f2 x).differentiableAt, ?_⟩
  exact continuous_floor_mul (by fun_prop) fun k => by rw [sin_two_pi_int]; ring

/-- **Cor. 3.6, `m = 2`**, et **exercice 2** : `f₂'` a pour dérivées à gauche et à droite
`2π²(k - 1)` et `2π² k` en `k ∈ ℤ`. -/
theorem f2'_left_right (k : ℤ) :
    HasDerivWithinAt f2' (((k : ℝ) - 1) * (2 * π ^ 2)) (Iio k) k ∧
    HasDerivWithinAt f2' ((k : ℝ) * (2 * π ^ 2)) (Ioi k) k := by
  have hd : HasDerivAt (fun y => π * sin (2 * π * y)) (2 * π ^ 2) k := by
    convert (((hasDerivAt_id (k : ℝ)).const_mul (2 * π)).sin).const_mul π using 1
    · simp
    · simp [cos_two_pi_int]
      ring
  have h0 : π * sin (2 * π * k) = 0 := by rw [sin_two_pi_int]; ring
  exact ⟨hasDerivWithinAt_Iio_mul (floor_left k) hd h0,
    hasDerivWithinAt_Ioi_mul (floor_right k) hd h0⟩

/-- **Cor. 3.6, `m = 2`** : `f₂'` n'est dérivable en aucun entier, donc `f₂` n'est deux fois
dérivable en aucun entier. -/
theorem not_differentiableAt_deriv_f2 (k : ℤ) : ¬ DifferentiableAt ℝ (deriv f2) k := by
  rw [deriv_f2]
  intro hd
  obtain ⟨hL, hR⟩ := f2'_left_right k
  have e1 := UniqueDiffWithinAt.eq_deriv _ (uniqueDiffWithinAt_Iio _)
    hd.hasDerivAt.hasDerivWithinAt hL
  have e2 := UniqueDiffWithinAt.eq_deriv _ (uniqueDiffWithinAt_Ioi _)
    hd.hasDerivAt.hasDerivWithinAt hR
  have : 2 * π ^ 2 = 0 := by linear_combination e1 - e2
  exact absurd this (by positivity)

/-- **Cor. 3.6, `m = 2`** : `f₂` n'est pas de classe `C²`. -/
theorem not_contDiff_two_f2 : ¬ ContDiff ℝ 2 f2 := by
  intro h
  have h1 : ContDiff ℝ 1 (deriv f2) := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv] at h
    exact h.2.2
  exact not_differentiableAt_deriv_f2 0 (h1.differentiable (by norm_num) _)

/-! ## §4. Sauts de la dérivée : théorème de Darboux -/

/-- **Cor. 4.2** (pas de saut pour une dérivée) : si `φ` est dérivable sur `ℝ` et si `φ'` a des
limites `ℓ⁻` et `ℓ⁺` à gauche et à droite de `a`, alors `ℓ⁻ = φ'(a) = ℓ⁺`. La preuve passe par
la **prop. 4.1** (limite de la dérivée), qui est `hasDerivWithinAt_Iic_of_tendsto_deriv` de
mathlib. -/
theorem no_jump {φ : ℝ → ℝ} (hφ : Differentiable ℝ φ) {a lm lp : ℝ}
    (hm : Tendsto (deriv φ) (𝓝[<] a) (𝓝 lm)) (hp : Tendsto (deriv φ) (𝓝[>] a) (𝓝 lp)) :
    lm = deriv φ a ∧ lp = deriv φ a := by
  have hL : HasDerivWithinAt φ lm (Iio a) a :=
    (hasDerivWithinAt_Iic_of_tendsto_deriv hφ.differentiableOn hφ.continuous.continuousWithinAt
      univ_mem hm).Iio_of_Iic
  have hR : HasDerivWithinAt φ lp (Ioi a) a :=
    (hasDerivWithinAt_Ici_of_tendsto_deriv hφ.differentiableOn hφ.continuous.continuousWithinAt
      univ_mem hp).Ioi_of_Ici
  exact ⟨UniqueDiffWithinAt.eq_deriv _ (uniqueDiffWithinAt_Iio a) hL
      (hφ a).hasDerivAt.hasDerivWithinAt,
    UniqueDiffWithinAt.eq_deriv _ (uniqueDiffWithinAt_Ioi a) hR
      (hφ a).hasDerivAt.hasDerivWithinAt⟩

/-- **Exercice 4** : `E` n'est la dérivée d'aucune fonction dérivable sur `ℝ` (par le théorème
de Darboux 4.4, `exists_hasDerivWithinAt_eq_of_gt_of_lt` de mathlib). -/
theorem floor_not_deriv : ¬ ∃ G : ℝ → ℝ, ∀ x, HasDerivAt G (⌊x⌋ : ℝ) x := by
  rintro ⟨G, hG⟩
  obtain ⟨x, hx, hx2⟩ := exists_hasDerivWithinAt_eq_of_gt_of_lt (a := 0) (b := 1)
    (f' := fun x : ℝ => (⌊x⌋ : ℝ)) zero_le_one (fun x _ => (hG x).hasDerivWithinAt)
    (m := 1 / 2) (by norm_num) (by norm_num)
  have : ⌊x⌋ = 0 := Int.floor_eq_iff.2 ⟨by simpa using hx.1.le, by simpa using hx.2⟩
  simp [this] at hx2

/-! ## Exercices -/

/-- **Exercice 1** : `g(x) = E(x) (x - E(x))` n'est continue en aucun entier `k ≠ 1`. -/
theorem ex1_not_continuousAt (k : ℤ) (hk : k ≠ 1) :
    ¬ ContinuousAt (fun x : ℝ => (⌊x⌋ : ℝ) * (x - ⌊x⌋)) k := by
  intro hc
  have hlim : Tendsto (fun x : ℝ => (⌊x⌋ : ℝ) * (x - ⌊x⌋)) (𝓝[<] (k : ℝ))
      (𝓝 (((k : ℝ) - 1) * ((k : ℝ) - ((k : ℝ) - 1)))) :=
    (floor_left k).mul ((tendsto_id.mono_left nhdsWithin_le_nhds).sub (floor_left k))
  have hval := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio (k : ℝ)))
  have := tendsto_nhds_unique hlim hval
  simp at this
  apply hk
  exact_mod_cast (by linarith : (k : ℝ) = 1)

/-- **Exercice 1** : `g` est continue en `1`, avec `g'_g(1) = 0 ≠ 1 = g'_d(1)`. -/
theorem ex1_at_one :
    ContinuousAt (fun x : ℝ => (⌊x⌋ : ℝ) * (x - ⌊x⌋)) 1 ∧
    HasDerivWithinAt (fun x : ℝ => (⌊x⌋ : ℝ) * (x - ⌊x⌋)) 0 (Iio 1) 1 ∧
    HasDerivWithinAt (fun x : ℝ => (⌊x⌋ : ℝ) * (x - ⌊x⌋)) 1 (Ioi 1) 1 := by
  -- Sur `]0, 2[`, `g(x) = E(x) (x - 1) + E(x) (1 - E(x))`, et le second terme est nul :
  -- `E(x) ∈ {0, 1}`. On écrit donc `g = E · (x - 1)` près de `1`.
  have heq : ∀ᶠ x in 𝓝 (1 : ℝ), (⌊x⌋ : ℝ) * (x - ⌊x⌋) = (⌊x⌋ : ℝ) * (x - 1) := by
    filter_upwards [Ioo_mem_nhds (show (0 : ℝ) < 1 by norm_num) (show (1 : ℝ) < 2 by norm_num)]
      with x hx
    rcases lt_or_ge x 1 with h | h
    · have : ⌊x⌋ = 0 := Int.floor_eq_iff.2 ⟨by simpa using hx.1.le, by simpa using h⟩
      simp [this]
    · have : ⌊x⌋ = 1 := Int.floor_eq_iff.2 ⟨by simpa using h, by norm_num [hx.2]⟩
      simp [this]
  have hh : HasDerivAt (fun x : ℝ => x - 1) 1 1 := (hasDerivAt_id 1).sub_const 1
  have h1 : ((1 : ℤ) : ℝ) = 1 := by norm_num
  have hl := floor_left 1
  have hr := floor_right 1
  rw [h1] at hl hr
  refine ⟨(continuousAt_mul_of_jump hl hr hh.continuousAt (by norm_num)).congr
    (heq.mono fun x hx => hx.symm), ?_, ?_⟩
  · have := hasDerivWithinAt_Iio_mul hl hh (by norm_num)
    exact (this.congr_of_eventuallyEq (eventually_nhdsWithin_of_eventually_nhds heq)
      (by norm_num)).congr_deriv (by norm_num)
  · have := hasDerivWithinAt_Ioi_mul hr hh (by norm_num)
    exact (this.congr_of_eventuallyEq (eventually_nhdsWithin_of_eventually_nhds heq)
      (by norm_num)).congr_deriv (by norm_num)

/-- La primitive `G(x) = ∫₀ˣ E` de l'**exercice 5**, sous sa forme close
`G(x) = n x - n(n+1)/2` avec `n = E(x)`. -/
def G (x : ℝ) : ℝ := ⌊x⌋ * x - ⌊x⌋ * (⌊x⌋ + 1) / 2

/-- Les fonctions affines `ℓₙ(x) = n x - n(n+1)/2`. -/
def ell (n : ℤ) (x : ℝ) : ℝ := n * x - n * (n + 1) / 2

/-- **Exercice 5.2** : `ℓₙ ≤ G` pour tout `n ∈ ℤ`, avec égalité pour `n = E(x)` ; donc
`G = max_n ℓₙ`. -/
theorem ell_le_G (n : ℤ) (x : ℝ) : ell n x ≤ G x := by
  set N := ⌊x⌋ with hN
  have h1 : (N : ℝ) ≤ x := Int.floor_le x
  have h2 : x < N + 1 := Int.lt_floor_add_one x
  have key : G x - ell n x = ((N : ℝ) - n) * (x - ((N : ℝ) + n + 1) / 2) := by
    simp only [G, ell, ← hN]; ring
  rw [← sub_nonneg, key]
  rcases lt_trichotomy n N with h | h | h
  · have : (n : ℝ) + 1 ≤ N := by exact_mod_cast h
    apply mul_nonneg <;> linarith
  · simp [h]
  · have : (N : ℝ) + 1 ≤ n := by exact_mod_cast h
    apply mul_nonneg_of_nonpos_of_nonpos <;> linarith

theorem G_eq_ell (x : ℝ) : G x = ell ⌊x⌋ x := by simp [G, ell]

/-- **Exercice 5.2** : `G` est convexe sur `ℝ`. -/
theorem convexOn_G : ConvexOn ℝ univ G := by
  refine ⟨convex_univ, fun a _ b _ s t hs ht hst => ?_⟩
  obtain rfl : t = 1 - s := by linarith
  set z := s • a + (1 - s) • b
  rw [G_eq_ell z]
  have ha := ell_le_G ⌊z⌋ a
  have hb := ell_le_G ⌊z⌋ b
  have : ell ⌊z⌋ z = s * ell ⌊z⌋ a + (1 - s) * ell ⌊z⌋ b := by
    simp only [z, ell, smul_eq_mul]
    ring
  rw [this, smul_eq_mul, smul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left ha hs, mul_le_mul_of_nonneg_left hb ht]

end PartieEntiereRegularite

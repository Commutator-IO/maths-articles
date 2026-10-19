import Mathlib

/-!
# Crochet de Lie et équations différentielles linéaires

Formalisation de la note « Crochet de Lie et équations différentielles linéaires »
(M. Hua, octobre 2026).

## Modèles

* **Opérateurs** (§2–4, exercice 1). `Cinf 𝕜` est la `𝕜`-sous-algèbre de `ℝ → 𝕜` formée des
  fonctions `C^∞` (`𝕜 = ℝ` ou `ℂ`, tout corps `RCLike`). `D f = f'` est la dérivée, empaquetée
  comme `𝕜`-dérivation `Dder 𝕜` ; l'opérateur `𝔇 = Dop 𝕜 : Module.End 𝕜 (Cinf 𝕜)` est
  l'application linéaire sous-jacente, `M q = Algebra.lmul 𝕜 (Cinf 𝕜) q` est la multiplication
  par `q`, et `X` est la fonction coordonnée `x`.
  Les identités entre opérateurs différentiels sont des égalités dans l'anneau
  `Module.End 𝕜 (Cinf 𝕜)`, dont le crochet de Lie est le commutateur `⁅A, B⁆ = A * B - B * A`.
* **Ponctuel** (formules de résolution, exemples, §5, §7). Pour des coefficients qui ne sont pas
  lisses sur tout `ℝ` (par ex. `1/x` sur `]0, +∞[`) ou pour des formules intégrales, les énoncés
  sont ponctuels, avec des hypothèses `HasDerivAt` ou `deriv`, pour des fonctions à valeurs
  réelles. Un énoncé sur `]0,+∞[` est un énoncé en tout point `x > 0`.
* **Champs de vecteurs** (§5.4, exercice 4). Sur un espace normé réel `E` (le plan des phases
  `ℝ × ℝ` dans la note), le champ `ξ : E → E` agit sur `g : E → ℝ` par `g ↦ (p ↦ Dg(p) (ξ p))` ;
  les translations `X_φ` sont les champs constants `ξ = (φ(x), φ'(x))` à `x` fixé, la dilatation
  `S` est `ξ = id`.
* **Exponentielle** (§6). Dans une `ℝ`-algèbre normée complète (par ex. les matrices munies d'une
  norme d'opérateur), avec `NormedSpace.exp`.

## Écarts avec la note

* §7.1, remarque « Lien avec le lemme 2.5 » : la conjugaison `a(D + b/a) = a B⁻¹ ∘ D ∘ B` est le
  lemme avec `q = -b/a` et `e^{-Q} = B` (à une constante près), et non `e^{-Q} = B/a`
  (`B/a` est le multiplicateur `u`). Voir `exactDerivative`.
* La prop. 6.1 n'est démontrée que pour les familles commutantes de la forme `B(x) = β(x) • A₀`
  (`hasDerivAt_exp_scalar`) et dans le cas constant (Duhamel, `duhamel`) ; le cas commutant
  général n'est pas démontré.
* Tous les autres énoncés vérifiés ici sont corrects tels qu'écrits, en particulier la solution
  finale `-cos x / 5 + sin x / 10` de `y'' + 4y' + 3y = e^{-x} + sin x`, l'ordre des blocs du
  §7.2, et `(i - j)(i - j²) = i`.

## Omis

Le théorème 5.2 (admis dans la note), le développement de Magnus, le théorème général du facteur
intégrant de Lie (seul `y' + p y = f`, `μ = e^{∫p}` est énoncé : `integratingFactor`), la formule
`e^{-px} y = m + m' ∫ … ` du §7.2, le cas commutant général de la prop. 6.1.
-/

open scoped ContDiff
open Real

noncomputable section

namespace CrochetLieEDO

/-! ## §2. Opérateurs sur les fonctions lisses -/

section Operators

variable (𝕜 : Type*) [RCLike 𝕜]

/-- L'algèbre `C^∞(ℝ, 𝕜)`. -/
def Cinf : Subalgebra 𝕜 (ℝ → 𝕜) where
  carrier := {f | ContDiff ℝ ∞ f}
  mul_mem' ha hb := by simp only [Set.mem_ofPred_eq] at *; exact ha.mul hb
  add_mem' ha hb := by simp only [Set.mem_ofPred_eq] at *; exact ha.add hb
  algebraMap_mem' _ := by simp only [Set.mem_ofPred_eq]; exact contDiff_const

variable {𝕜}

lemma Cinf.contDiff (f : Cinf 𝕜) : ContDiff ℝ ∞ (f : ℝ → 𝕜) := f.2

lemma Cinf.diff (f : Cinf 𝕜) : Differentiable ℝ (f : ℝ → 𝕜) :=
  (contDiff_infty_iff_deriv.1 (Cinf.contDiff f)).1

/-- La dérivée `D f = f'` d'une fonction lisse. -/
def D (f : Cinf 𝕜) : Cinf 𝕜 := ⟨deriv f, (contDiff_infty_iff_deriv.1 (Cinf.contDiff f)).2⟩

@[simp] lemma coe_D (f : Cinf 𝕜) : ((D f : Cinf 𝕜) : ℝ → 𝕜) = deriv f := rfl

lemma D_mul (f g : Cinf 𝕜) : D (f * g) = f * D g + g * D f := Subtype.ext <| funext fun x => by
  change deriv (fun y => f.1 y * g.1 y) x = f.1 x * deriv g.1 x + g.1 x * deriv f.1 x
  rw [deriv_fun_mul (Cinf.diff f x) (Cinf.diff g x)]
  ring

variable (𝕜) in
/-- La dérivation comme dérivation de `C^∞(ℝ, 𝕜)` (règle de Leibniz). -/
def Dder : Derivation 𝕜 (Cinf 𝕜) (Cinf 𝕜) :=
  Derivation.mk'
    { toFun := D
      map_add' f g := Subtype.ext <| funext fun x => deriv_add (Cinf.diff f x) (Cinf.diff g x)
      map_smul' c f := Subtype.ext <| funext fun x => deriv_const_smul c (Cinf.diff f x) }
    D_mul

lemma Dder_apply (f : Cinf 𝕜) : Dder 𝕜 f = D f := rfl

lemma D_one : D (1 : Cinf 𝕜) = 0 := (Dder 𝕜).map_one_eq_zero

lemma D_pow (f : Cinf 𝕜) (n : ℕ) : D (f ^ n) = n • (f ^ (n - 1) * D f) := by
  rw [← Dder_apply, (Dder 𝕜).leibniz_pow, Dder_apply, smul_eq_mul]

lemma D_add (f g : Cinf 𝕜) : D (f + g) = D f + D g := (Dder 𝕜).map_add f g
lemma D_sub (f g : Cinf 𝕜) : D (f - g) = D f - D g := (Dder 𝕜).map_sub f g
lemma D_smul (c : 𝕜) (f : Cinf 𝕜) : D (c • f) = c • D f := (Dder 𝕜).map_smul c f

variable (𝕜) in
/-- L'opérateur `D` dans `Module.End 𝕜 C^∞`. -/
abbrev Dop : Module.End 𝕜 (Cinf 𝕜) := (Dder 𝕜).toLinearMap

local notation "𝔇" => Dop 𝕜

@[simp] lemma Dop_apply (f : Cinf 𝕜) : Dop 𝕜 f = D f := rfl

/-- L'opérateur de multiplication `M_q`. -/
abbrev M (q : Cinf 𝕜) : Module.End 𝕜 (Cinf 𝕜) := Algebra.lmul 𝕜 (Cinf 𝕜) q

@[simp] lemma M_apply (q f : Cinf 𝕜) : M q f = q * f := rfl

lemma M_one : M (1 : Cinf 𝕜) = 1 := map_one _
lemma M_eq_zero (p : Cinf 𝕜) : M p = 0 ↔ p = 0 := map_eq_zero_iff _ Algebra.lmul_injective

/-- La fonction coordonnée `x`. -/
def X : Cinf 𝕜 := ⟨fun x => (x : 𝕜), by
  change ContDiff ℝ ∞ fun x : ℝ => (x : 𝕜)
  simpa using (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff⟩

lemma D_X : D (X : Cinf 𝕜) = 1 := Subtype.ext <| funext fun x => by
  change deriv (fun y : ℝ => (y : 𝕜)) x = 1
  simpa using ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).hasDerivAt (x := x)).deriv

/-- **Prop. 2.3** (relation fondamentale) : `[D, M_q] = M_{q'}`. -/
theorem lie_D_M (q : Cinf 𝕜) : ⁅𝔇, M q⁆ = M (D q) := by
  ext1 f
  simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, M_apply, Dop_apply, D_mul]
  ring

/-- **Prop. 2.3** : `[D, M_x] = Id`. -/
theorem lie_D_X : ⁅𝔇, M (X : Cinf 𝕜)⁆ = 1 := by
  rw [lie_D_M, D_X, M_one]

/-- **Prop. 2.3** : `D` commute avec `M_q` si et seulement si `q` est constante (`ℝ` est
connexe). -/
theorem lie_D_M_eq_zero_iff (q : Cinf 𝕜) :
    ⁅𝔇, M q⁆ = 0 ↔ ∃ c : 𝕜, (q : ℝ → 𝕜) = fun _ => c := by
  rw [lie_D_M, M_eq_zero]
  constructor
  · intro h
    have h' : ∀ x, deriv (q : ℝ → 𝕜) x = 0 := fun x => by
      simpa using congrFun (congrArg Subtype.val h) x
    exact ⟨q.1 0, funext fun x => is_const_of_deriv_eq_zero (Cinf.diff q) h' x 0⟩
  · rintro ⟨c, hc⟩
    exact Subtype.ext (funext fun x => by simp [hc])

/-- **§2, identité de Jacobi**, pour le commutateur dans un anneau associatif quelconque
(`lie_jacobi` de mathlib pour la structure d'anneau de Lie `LieRing.ofAssociativeRing`). -/
theorem jacobi {R : Type*} [Ring R] (A B C : R) :
    ⁅A, ⁅B, C⁆⁆ + ⁅B, ⁅C, A⁆⁆ + ⁅C, ⁅A, B⁆⁆ = 0 := by
  let := LieRing.ofAssociativeRing (A := R)
  exact lie_jacobi A B C

/-- **Lemme 2.5** (conjugaison), forme opératorielle : si `E F = 1` et `E' = q E` (c.-à-d.
`E = e^Q`, `F = e^{-Q}`, `Q' = q`), alors `M_E ∘ D ∘ M_F = D - M_q`. -/
theorem conj (E F q : Cinf 𝕜) (hEF : E * F = 1) (hE : D E = q * E) :
    M E * 𝔇 * M F = 𝔇 - M q := by
  have hF : E * D F = -q := by
    have := congrArg D hEF
    rw [D_mul, D_one, hE] at this
    linear_combination this - q * hEF
  ext1 f
  simp only [Module.End.mul_apply, M_apply, LinearMap.sub_apply, Dop_apply, D_mul]
  linear_combination (D f) * hEF + f * hF

/-- `x ↦ e^{Q(x)}` pour `Q` réelle lisse. -/
def expC (Q : Cinf ℝ) : Cinf ℝ := ⟨fun x => Real.exp (Q.1 x), by
  change ContDiff ℝ ∞ _; exact contDiff_exp.comp (Cinf.contDiff Q)⟩

/-- **Lemme 2.5** avec `E = e^Q` : `D - Q' = e^Q ∘ D ∘ e^{-Q}`. -/
theorem conj_exp (Q : Cinf ℝ) : M (expC Q) * Dop ℝ * M (expC (-Q)) = Dop ℝ - M (D Q) :=
  conj _ _ _ (Subtype.ext <| funext fun x => by simp [expC, ← Real.exp_add])
    (Subtype.ext <| funext fun x => by
      simpa [expC, mul_comm] using ((Cinf.diff Q x).hasDerivAt.exp).deriv)

/-! ## §3. Coefficients constants -/

/-- **§3** : `(D - r₁)(D - r₂) = D² - (r₁ + r₂) D + r₁ r₂` pour des constantes `r₁, r₂ ∈ 𝕜`. La
réécriture `D ∘ r₂ = r₂ ∘ D` est `Algebra.commutes`, c.-à-d. `[D, r₂] = 0`. -/
theorem const_factor (r₁ r₂ : 𝕜) :
    (𝔇 - algebraMap 𝕜 _ r₁) * (𝔇 - algebraMap 𝕜 _ r₂) =
      𝔇 * 𝔇 - algebraMap 𝕜 _ (r₁ + r₂) * 𝔇 + algebraMap 𝕜 (Module.End 𝕜 (Cinf 𝕜)) (r₁ * r₂) := by
  ext1 f
  simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply,
    Module.algebraMap_end_apply, Dop_apply, D_sub, D_smul]
  module

/-- La racine cubique de l'unité `j = e^{2iπ/3} = -1/2 + i √3/2`. -/
def j : ℂ := -1 / 2 + (√3 / 2) * Complex.I

lemma j_sq_add : j ^ 2 + j + 1 = 0 := by
  have h3 : ((√3 : ℝ) : ℂ) ^ 2 = 3 := by norm_cast; simp
  rw [j]; linear_combination (Complex.I ^ 2 / 4) * h3 + (3 / 4 : ℂ) * Complex.I_sq

/-- **§7.3**, factorisation sur `ℂ` : `D² + D + 1 = (D - j)(D - j²)`. -/
theorem factor_j :
    (Dop ℂ - algebraMap ℂ _ j) * (Dop ℂ - algebraMap ℂ _ (j ^ 2)) = Dop ℂ * Dop ℂ + Dop ℂ + 1 := by
  have e : j * j ^ 2 = 1 := by linear_combination (j - 1) * j_sq_add
  ext1 f
  simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply,
    Module.algebraMap_end_apply, Dop_apply, D_sub, D_smul, Module.End.one_apply]
  linear_combination (norm := module) j_sq_add • (-D f) + e • f

/-! ## §4. Coefficients variables : le commutateur comme obstruction -/

/-- **§4**, développement : `(D - p)(D - q) = D² - (p + q) D + (p q - q')`. -/
theorem factor (p q : Cinf 𝕜) :
    (𝔇 - M p) * (𝔇 - M q) = 𝔇 * 𝔇 - M (p + q) * 𝔇 + M (p * q - D q) := by
  ext1 f
  simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply, M_apply, Dop_apply,
    D_sub, D_mul]
  ring

/-- **Prop. 4.1** (Riccati) : `D² + a D + b = (D - p)(D - q)` si et seulement si `p = -a - q` et
`q' + q² + a q + b = 0`. Le sens direct teste les opérateurs sur `1` et sur `x`. -/
theorem riccati_iff (p q a b : Cinf 𝕜) :
    (𝔇 - M p) * (𝔇 - M q) = 𝔇 * 𝔇 + M a * 𝔇 + M b ↔
      p = -a - q ∧ D q + q * q + a * q + b = 0 := by
  rw [factor]
  constructor
  · intro h
    have h1 := LinearMap.congr_fun h 1
    have h2 := LinearMap.congr_fun h X
    simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, M_apply,
      Dop_apply, D_one, D_X, mul_zero, mul_one, sub_zero, zero_add, add_zero] at h1 h2
    exact ⟨by linear_combination -h2 + X * h1, by linear_combination q * (-h2 + X * h1) - h1⟩
  · rintro ⟨rfl, h⟩
    ext1 f
    simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply, M_apply, Dop_apply]
    linear_combination (-f) * h

/-- **Remarque 4.4** : `[D - p, D - q] = p' - q'`. -/
theorem lie_factor (p q : Cinf 𝕜) : ⁅𝔇 - M p, 𝔇 - M q⁆ = M (D p - D q) := by
  ext1 f
  simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, M_apply, Dop_apply, D_sub,
    D_mul]
  ring

/-- L'opérateur `L = D² + aD + b` évalué ponctuellement. -/
def L (a b y : ℝ → ℝ) (x : ℝ) : ℝ := deriv (deriv y) x + a x * deriv y x + b x * y x

lemma deriv2 {y y₁ y₂ : ℝ → ℝ} (h₁ : ∀ x, HasDerivAt y (y₁ x) x)
    (h₂ : ∀ x, HasDerivAt y₁ (y₂ x) x) (x : ℝ) : deriv y x = y₁ x ∧ deriv (deriv y) x = y₂ x :=
  ⟨(h₁ x).deriv, by rw [funext fun x => (h₁ x).deriv, (h₂ x).deriv]⟩

lemma L_eq {a b y y₁ y₂ : ℝ → ℝ} (h₁ : ∀ x, HasDerivAt y (y₁ x) x)
    (h₂ : ∀ x, HasDerivAt y₁ (y₂ x) x) (x : ℝ) : L a b y x = y₂ x + a x * y₁ x + b x * y x := by
  rw [L, (deriv2 h₁ h₂ x).1, (deriv2 h₁ h₂ x).2]

/-- **§4**, développement ponctuel de `(D - p)(D - q) y`, valable pour des coefficients non
lisses. -/
theorem factor_apply (p q y : ℝ → ℝ) {x : ℝ} (hq : DifferentiableAt ℝ q x)
    (hy : DifferentiableAt ℝ y x) (hy' : DifferentiableAt ℝ (deriv y) x) :
    deriv (fun t => deriv y t - q t * y t) x - p x * (deriv y x - q x * y x) =
      deriv (deriv y) x - (p x + q x) * deriv y x + (p x * q x - deriv q x) * y x := by
  rw [deriv_fun_sub hy' (hq.fun_mul hy), deriv_fun_mul hq hy]; ring

/-- **Prop. 4.2** : si `y₁` est solution de `(H)` et `y₁(x) ≠ 0`, alors `q = y₁'/y₁` vérifie
l'équation de Riccati en `x`. -/
theorem riccati_of_sol (a b y₁ : ℝ → ℝ) {x : ℝ} (hy : DifferentiableAt ℝ y₁ x)
    (hy' : DifferentiableAt ℝ (deriv y₁) x) (h0 : y₁ x ≠ 0) (hH : L a b y₁ x = 0) :
    deriv (fun t => deriv y₁ t / y₁ t) x + (deriv y₁ x / y₁ x) ^ 2 +
      a x * (deriv y₁ x / y₁ x) + b x = 0 := by
  rw [L] at hH
  rw [deriv_fun_div hy' hy h0]
  field_simp
  linear_combination y₁ x * hH

/-- **Exemple 4.3**, factorisation sur `]0, +∞[` : `x² (D - 1/x)(D - 1/x) y = x²y'' - 2xy' + 2y`. -/
theorem ex43_factor (y : ℝ → ℝ) {x : ℝ} (hx : x ≠ 0) (hy : DifferentiableAt ℝ y x)
    (hy' : DifferentiableAt ℝ (deriv y) x) :
    x ^ 2 * (deriv (fun t => deriv y t - t⁻¹ * y t) x - x⁻¹ * (deriv y x - x⁻¹ * y x)) =
      x ^ 2 * deriv (deriv y) x - 2 * x * deriv y x + 2 * y x := by
  rw [factor_apply (fun t => t⁻¹) _ y (differentiableAt_inv hx) hy hy', deriv_inv]
  field_simp; ring

/-- **Exemple 4.3** : `D - 1/x = x ∘ D ∘ 1/x` sur `]0, +∞[`. -/
theorem ex43_conj (y : ℝ → ℝ) {x : ℝ} (hx : x ≠ 0) (hy : DifferentiableAt ℝ y x) :
    x * deriv (fun t => y t / t) x = deriv y x - x⁻¹ * y x := by
  rw [deriv_fun_div hy differentiableAt_fun_id hx]; simp; field_simp

/-- **Exemple 4.3** : `y = x³/2 + A x² + B x` est solution de `x² y'' - 2x y' + 2y = x³`. -/
theorem ex43_sol (A B x : ℝ) :
    x ^ 2 * deriv (deriv fun t => t ^ 3 / 2 + A * t ^ 2 + B * t) x -
        2 * x * deriv (fun t => t ^ 3 / 2 + A * t ^ 2 + B * t) x +
      2 * (x ^ 3 / 2 + A * x ^ 2 + B * x) = x ^ 3 := by
  obtain ⟨h1, h2⟩ := deriv2 (y₁ := fun t => 3 * t ^ 2 / 2 + 2 * A * t + B)
    (y₂ := fun t => 3 * t + 2 * A) (fun t => by
      convert (((hasDerivAt_pow 3 t).div_const 2).fun_add
        ((hasDerivAt_pow 2 t).const_mul A)).fun_add ((hasDerivAt_id' t).const_mul B) using 1
      norm_num; ring)
    (fun t => by
      convert ((((hasDerivAt_pow 2 t).const_mul 3).div_const 2).fun_add
        ((hasDerivAt_id' t).const_mul (2 * A))).fun_add (hasDerivAt_const t B) using 1
      norm_num; ring) x
  rw [h1, h2]; ring

/-! ## Exercices 1 et 3 -/

/-- **Exercice 1** : `[D, M_{x^n}] = n M_{x^{n-1}}`. -/
theorem lie_D_X_pow (n : ℕ) : ⁅𝔇, M ((X : Cinf 𝕜) ^ n)⁆ = n • M (X ^ (n - 1)) := by
  rw [lie_D_M, D_pow, D_X, mul_one]; exact map_nsmul _ _ _

/-- **Exercice 1** : `[D², M_q] = 2 q' D + q''`. -/
theorem lie_D_sq_M (q : Cinf 𝕜) : ⁅𝔇 * 𝔇, M q⁆ = M (2 * D q) * 𝔇 + M (D (D q)) := by
  ext1 f
  simp only [Ring.lie_def, LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply, M_apply,
    Dop_apply, D_add, D_mul]
  ring

/-- **Exercice 3** : `eˣ` et `x + 1` sont solutions de `x y'' - (x+1) y' + y = 0` ; l'équation de
Riccati est vérifiée pour `q = 1`, `a = -(x+1)/x`, `b = 1/x`, avec `p = -a - q = 1/x`. -/
theorem ex3 (x : ℝ) (hx : x ≠ 0) :
    x * deriv (deriv Real.exp) x - (x + 1) * deriv Real.exp x + Real.exp x = 0 ∧
    x * deriv (deriv fun t => t + 1) x - (x + 1) * deriv (fun t => t + 1) x + (x + 1) = 0 ∧
    (0 : ℝ) + 1 ^ 2 + (-(x + 1) / x) * 1 + 1 / x = 0 ∧ 1 / x = -(-(x + 1) / x) - 1 := by
  refine ⟨by simp; ring, by simp, by field_simp; ring, by field_simp; ring⟩

/-! ## Lemme 2.5, formule de résolution -/

/-- **Lemme 2.5**, existence : `y = e^Q (∫_{x₀}^x e^{-Q} g + C)` est solution de `y' - q y = g`. -/
theorem conj_solution {q g Q : ℝ → ℝ} (hQ : ∀ x, HasDerivAt Q (q x) x) (hg : Continuous g)
    (x₀ C x : ℝ) :
    HasDerivAt (fun x => Real.exp (Q x) * ((∫ t in x₀..x, Real.exp (-Q t) * g t) + C))
      (q x * (Real.exp (Q x) * ((∫ t in x₀..x, Real.exp (-Q t) * g t) + C)) + g x) x := by
  have hc : Continuous fun t => Real.exp (-Q t) * g t :=
    ((continuous_iff_continuousAt.2 fun x => (hQ x).continuousAt).neg.rexp).mul hg
  convert (hQ x).exp.fun_mul ((hc.integral_hasStrictDerivAt x₀ x).hasDerivAt.add_const C)
    using 1
  rw [Real.exp_neg]; field_simp

/-- **Lemme 2.5**, unicité : toute solution de `y' - q y = g` est de la forme
`e^Q (∫_{x₀}^x e^{-Q} g + C)`, avec `C = e^{-Q(x₀)} y(x₀)`. -/
theorem conj_unique {q g Q y : ℝ → ℝ} (hQ : ∀ x, HasDerivAt Q (q x) x) (hg : Continuous g)
    (hy : ∀ x, HasDerivAt y (q x * y x + g x) x) (x₀ x : ℝ) :
    y x = Real.exp (Q x) * ((∫ t in x₀..x, Real.exp (-Q t) * g t) + Real.exp (-Q x₀) * y x₀) := by
  have hc : Continuous fun t => Real.exp (-Q t) * g t :=
    ((continuous_iff_continuousAt.2 fun x => (hQ x).continuousAt).neg.rexp).mul hg
  have hz : ∀ x, HasDerivAt (fun x => Real.exp (-Q x) * y x -
      ∫ t in x₀..x, Real.exp (-Q t) * g t) 0 x := fun x => by
    convert ((hQ x).fun_neg.exp.fun_mul (hy x)).fun_sub
      (hc.integral_hasStrictDerivAt x₀ x).hasDerivAt using 1
    ring
  have := is_const_of_deriv_eq_zero (fun x => (hz x).differentiableAt) (fun x => (hz x).deriv)
    x x₀
  simp only [intervalIntegral.integral_same, sub_zero] at this
  rw [← this, Real.exp_neg, add_sub_cancel, mul_inv_cancel_left₀ (Real.exp_pos _).ne']

/-- **§7.1**, facteur intégrant de Lie pour `y' + p y = f` : avec `P' = p`,
`(e^P y)' = e^P (y' + p y)`, donc `μ = e^{∫ p}`. -/
theorem integratingFactor {P p y : ℝ → ℝ} {y' x : ℝ} (hP : HasDerivAt P (p x) x)
    (hy : HasDerivAt y y' x) :
    HasDerivAt (fun t => Real.exp (P t) * y t) (Real.exp (P x) * (y' + p x * y x)) x := by
  convert hP.exp.fun_mul hy using 1; ring

/-- **§7.1**, remarque « Lien avec le lemme 2.5 » (corrigée) : si `B' = (b/a) B` (donc
`B = e^{-Q}` avec `Q' = q = -b/a`), alors `(B y)' = (B/a)(a y' + b y)` : le multiplicateur est
`u = B/a` et `a y' + b y = a B⁻¹ D (B y)`. Le `e^{-Q} = B/a` de la note doit se lire
`e^{-Q} = B`. -/
theorem exactDerivative {a b B y : ℝ → ℝ} {y' x : ℝ} (ha : a x ≠ 0)
    (hB : HasDerivAt B (b x / a x * B x) x) (hy : HasDerivAt y y' x) :
    HasDerivAt (fun t => B t * y t) (B x / a x * (a x * y' + b x * y x)) x := by
  convert hB.fun_mul hy using 1; field_simp; ring

/-! ## Exemples (§3, §7, exercice 2) -/

lemma hasDerivAt_exp_mul (c x : ℝ) :
    HasDerivAt (fun t => Real.exp (c * t)) (c * Real.exp (c * x)) x := by
  convert ((hasDerivAt_id' x).const_mul c).exp using 1; ring

/-- **Exemple 3.2** : `y = x/2 + 3/4 - A eˣ + B e^{2x}` est solution de `y'' - 3y' + 2y = x`. -/
theorem ex32 (A B x : ℝ) :
    L (fun _ => -3) (fun _ => 2)
      (fun t => t / 2 + 3 / 4 - A * Real.exp (1 * t) + B * Real.exp (2 * t)) x = x := by
  rw [L_eq (y₁ := fun t => 1 / 2 - A * (1 * Real.exp (1 * t)) + B * (2 * Real.exp (2 * t)))
    (y₂ := fun t => -A * (1 * (1 * Real.exp (1 * t))) + B * (2 * (2 * Real.exp (2 * t))))]
  · ring
  · exact fun t => ((((hasDerivAt_id' t).div_const 2).add_const _).fun_sub
      ((hasDerivAt_exp_mul 1 t).const_mul A)).fun_add ((hasDerivAt_exp_mul 2 t).const_mul B)
  · exact fun t => by
      convert ((hasDerivAt_const t (1 / 2 : ℝ)).fun_sub
        (((hasDerivAt_exp_mul 1 t).const_mul 1).const_mul A)).fun_add
        (((hasDerivAt_exp_mul 2 t).const_mul 2).const_mul B) using 1
      ring

/-- **§7.3** : `y = a e^{-3x} + b e^{-x} + (x/2) e^{-x} - cos x / 5 + sin x / 10` est solution de
`y'' + 4y' + 3y = e^{-x} + sin x` (les coefficients de la note sont corrects). -/
theorem ex73_full (a b x : ℝ) :
    L (fun _ => 4) (fun _ => 3) (fun t => a * Real.exp (-3 * t) + b * Real.exp (-1 * t) +
      t / 2 * Real.exp (-1 * t) - Real.cos t / 5 + Real.sin t / 10) x =
      Real.exp (-1 * x) + Real.sin x := by
  rw [L_eq (y₁ := fun t => a * (-3 * Real.exp (-3 * t)) + b * (-1 * Real.exp (-1 * t)) +
      (1 / 2 * Real.exp (-1 * t) + t / 2 * (-1 * Real.exp (-1 * t))) - -Real.sin t / 5 +
      Real.cos t / 10)
    (y₂ := fun t => a * (-3 * (-3 * Real.exp (-3 * t))) + b * (-1 * (-1 * Real.exp (-1 * t))) +
      (1 / 2 * (-1 * Real.exp (-1 * t)) + (1 / 2 * (-1 * Real.exp (-1 * t)) +
        t / 2 * (-1 * (-1 * Real.exp (-1 * t))))) - -Real.cos t / 5 + -Real.sin t / 10)]
  · ring
  · intro t
    have e₃ := hasDerivAt_exp_mul (-3) t
    have e₁ := hasDerivAt_exp_mul (-1) t
    convert ((((e₃.const_mul a).fun_add (e₁.const_mul b)).fun_add
      (((hasDerivAt_id' t).div_const 2).fun_mul e₁)).fun_sub
      ((Real.hasDerivAt_cos t).div_const 5)).fun_add ((Real.hasDerivAt_sin t).div_const 10)
      using 1
  · intro t
    have e₃ := hasDerivAt_exp_mul (-3) t
    have e₁ := hasDerivAt_exp_mul (-1) t
    convert (((((e₃.const_mul (-3)).const_mul a).fun_add ((e₁.const_mul (-1)).const_mul b)).fun_add
      ((e₁.const_mul (1 / 2)).fun_add
        (((hasDerivAt_id' t).div_const 2).fun_mul (e₁.const_mul (-1))))).fun_sub
      ((Real.hasDerivAt_sin t).fun_neg.div_const 5)).fun_add
      ((Real.hasDerivAt_cos t).div_const 10) using 1

/-- **§7.3** : `y = (x/2) e^{-x}` est une solution particulière de `y'' + 4y' + 3y = e^{-x}`
(cas `a = b = 0` de la formule complète, sans la partie en `sin`). -/
theorem ex73_part (x : ℝ) :
    L (fun _ => 4) (fun _ => 3) (fun t => t / 2 * Real.exp (-1 * t)) x = Real.exp (-1 * x) := by
  rw [L_eq (y₁ := fun t => 1 / 2 * Real.exp (-1 * t) + t / 2 * (-1 * Real.exp (-1 * t)))
    (y₂ := fun t => 1 / 2 * (-1 * Real.exp (-1 * t)) + (1 / 2 * (-1 * Real.exp (-1 * t)) +
        t / 2 * (-1 * (-1 * Real.exp (-1 * t)))))]
  · ring
  · exact fun t => ((hasDerivAt_id' t).div_const 2).fun_mul (hasDerivAt_exp_mul (-1) t)
  · intro t
    convert ((hasDerivAt_exp_mul (-1) t).const_mul (1 / 2)).fun_add
        (((hasDerivAt_id' t).div_const 2).fun_mul
          ((hasDerivAt_exp_mul (-1) t).const_mul (-1))) using 1

/-- **§7.3** : `sin` est solution de `y'' + y' + y = cos x`. -/
theorem ex73_sin (x : ℝ) : L (fun _ => 1) (fun _ => 1) Real.sin x = Real.cos x := by
  simp [L]

/-- **§7.3** : `(i - j)(i - j²) = i`. -/
theorem ex73_j : (Complex.I - j) * (Complex.I - j ^ 2) = Complex.I := by
  linear_combination (j - 1 - Complex.I) * j_sq_add + Complex.I_sq

/-- **Exercice 2** : `y_p = (x²/2) eˣ` est solution de `y'' - 2y' + y = eˣ`. -/
theorem ex2 (x : ℝ) :
    L (fun _ => -2) (fun _ => 1) (fun t => t ^ 2 / 2 * Real.exp t) x = Real.exp x := by
  rw [L_eq (y₁ := fun t => t * Real.exp t + t ^ 2 / 2 * Real.exp t)
    (y₂ := fun t => Real.exp t + t * Real.exp t + (t * Real.exp t + t ^ 2 / 2 * Real.exp t))]
  · ring
  · intro t
    convert ((hasDerivAt_pow 2 t).div_const 2).fun_mul (Real.hasDerivAt_exp t) using 1
    norm_num
  · intro t
    convert ((hasDerivAt_id' t).fun_mul (Real.hasDerivAt_exp t)).fun_add
      (((hasDerivAt_pow 2 t).div_const 2).fun_mul (Real.hasDerivAt_exp t)) using 1
    norm_num

/-- **§7.1, premier exemple** : `y = 1 + K / sin x` est solution de `y' sin x + y cos x = cos x`. -/
theorem ex71_sin (K x : ℝ) (hx : Real.sin x ≠ 0) :
    deriv (fun t => 1 + K / Real.sin t) x * Real.sin x + (1 + K / Real.sin x) * Real.cos x =
      Real.cos x := by
  rw [((hasDerivAt_const x 1).fun_add
    ((hasDerivAt_const x K).fun_div (Real.hasDerivAt_sin x) hx)).deriv]
  field_simp; ring

/-- **§7.1, premier exemple**, réciproque sur `]0, π[` : toute solution est `1 + K / sin x`. -/
theorem ex71_sin_unique {y : ℝ → ℝ} (hy : DifferentiableOn ℝ y (Set.Ioo 0 π))
    (hE : ∀ x ∈ Set.Ioo 0 π, deriv y x * Real.sin x + y x * Real.cos x = Real.cos x) :
    ∃ K, ∀ x ∈ Set.Ioo 0 π, y x = 1 + K / Real.sin x := by
  have hd : ∀ x ∈ Set.Ioo 0 π, DifferentiableAt ℝ y x := fun x hx =>
    hy.differentiableAt (Ioo_mem_nhds hx.1 hx.2)
  obtain ⟨K, hK⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo
    (f := fun t => y t * Real.sin t - Real.sin t)
    (fun x hx => ((hd x hx).fun_mul differentiableAt_sin).fun_sub differentiableAt_sin
      |>.differentiableWithinAt)
    (fun x hx => by
      simp only [Pi.zero_apply]
      rw [deriv_fun_sub ((hd x hx).fun_mul differentiableAt_sin) differentiableAt_sin,
        deriv_fun_mul (hd x hx) differentiableAt_sin, Real.deriv_sin, hE x hx, sub_self])
  refine ⟨K, fun x hx => ?_⟩
  have := (Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2).ne'
  rw [← hK x hx]; field_simp; ring

/-- **§7.1, second exemple** : `y = 1 + C cos x` est solution de `y' cos x + y sin x = sin x`. -/
theorem ex71_cos (C x : ℝ) :
    deriv (fun t => 1 + C * Real.cos t) x * Real.cos x + (1 + C * Real.cos x) * Real.sin x =
      Real.sin x := by
  simp; ring

/-- Un bloc `e^{px} D e^{-px}` du §7.2 est `D - p`. -/
lemma block (p : ℝ) {v : ℝ → ℝ} (hv : Differentiable ℝ v) (x : ℝ) :
    Real.exp (p * x) * deriv (fun t => Real.exp (-(p * t)) * v t) x = deriv v x - p * v x := by
  have h := ((hasDerivAt_exp_mul (-p) x).fun_mul (hv x).hasDerivAt).deriv
  simp only [neg_mul] at h
  rw [h, Real.exp_neg]; field_simp; ring

/-- **§7.2**, « petit exercice » :
`e^{px} (e^{-px} [e^{qx} (e^{-qx} u)']')' = u'' - (p + q) u' + p q u`. -/
theorem petit_exercice (p q : ℝ) {u : ℝ → ℝ} (hu : Differentiable ℝ u)
    (hu' : Differentiable ℝ (deriv u)) (x : ℝ) :
    Real.exp (p * x) * deriv (fun t => Real.exp (-(p * t)) *
        (Real.exp (q * t) * deriv (fun s => Real.exp (-(q * s)) * u s) t)) x =
      deriv (deriv u) x - (p + q) * deriv u x + p * q * u x := by
  have hb := block p (v := fun t => deriv u t - q * u t) (hu'.sub (hu.const_mul q)) x
  beta_reduce at hb
  simp only [block q hu]
  rw [hb, deriv_fun_sub (hu' x) ((hu x).const_mul q),
    deriv_const_mul _ (hu x)]
  ring

/-! ## §5. Variation des constantes -/

open Matrix in
/-- **Prop. 5.x** (coordonnées `(C₁, C₂)`) : si `Φᵢ' = A Φᵢ`, alors `Y = C₁ Φ₁ + C₂ Φ₂` est
solution de `Y' = A Y + F` en `x` si et seulement si `C₁' Φ₁ + C₂' Φ₂ = F` (taille `n` et `A(x)`
quelconques). -/
theorem vdc_system {n : ℕ} (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (F Φ₁ Φ₂ : ℝ → Fin n → ℝ)
    {C₁ C₂ : ℝ → ℝ} {c₁ c₂ x : ℝ} (hΦ₁ : HasDerivAt Φ₁ (A x *ᵥ Φ₁ x) x)
    (hΦ₂ : HasDerivAt Φ₂ (A x *ᵥ Φ₂ x) x) (hC₁ : HasDerivAt C₁ c₁ x) (hC₂ : HasDerivAt C₂ c₂ x) :
    HasDerivAt (fun t => C₁ t • Φ₁ t + C₂ t • Φ₂ t)
        (A x *ᵥ (C₁ x • Φ₁ x + C₂ x • Φ₂ x) + F x) x ↔ c₁ • Φ₁ x + c₂ • Φ₂ x = F x := by
  have h := (hC₁.smul hΦ₁).fun_add (hC₂.smul hΦ₂)
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  constructor
  · intro h'
    have := h.unique h'
    rw [← sub_eq_zero] at this ⊢
    rw [← this]; abel
  · intro h'
    convert h using 1
    rw [← h']; abel

/-- **(vdc)**, Cramer : avec `W = φ₁ φ₂' - φ₂ φ₁' ≠ 0`, le système `C₁'φ₁ + C₂'φ₂ = 0`,
`C₁'φ₁' + C₂'φ₂' = f` équivaut à `C₁' = -φ₂ f / W`, `C₂' = φ₁ f / W`. -/
theorem cramer {φ₁ φ₂ dφ₁ dφ₂ f c₁ c₂ : ℝ} (hW : φ₁ * dφ₂ - φ₂ * dφ₁ ≠ 0) :
    (c₁ * φ₁ + c₂ * φ₂ = 0 ∧ c₁ * dφ₁ + c₂ * dφ₂ = f) ↔
      (c₁ = -(φ₂ * f) / (φ₁ * dφ₂ - φ₂ * dφ₁) ∧ c₂ = φ₁ * f / (φ₁ * dφ₂ - φ₂ * dφ₁)) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [eq_div_iff hW]; linear_combination dφ₂ * h1 - φ₂ * h2,
      by rw [eq_div_iff hW]; linear_combination φ₁ * h2 - dφ₁ * h1⟩
  · rintro ⟨rfl, rfl⟩
    constructor <;> field_simp <;> ring

/-- **(vdc)** : si `φ₁, φ₂` sont solutions de `(H)` de wronskien non nul et
`C₁' = -φ₂ f / W`, `C₂' = φ₁ f / W`, alors `y = C₁ φ₁ + C₂ φ₂` est solution de `(E)`, avec
`y' = C₁ φ₁' + C₂ φ₂'`. -/
theorem vdc_solution {a b f φ₁ φ₂ dφ₁ dφ₂ C₁ C₂ : ℝ → ℝ} {x : ℝ}
    (hφ₁ : HasDerivAt φ₁ (dφ₁ x) x) (hdφ₁ : HasDerivAt dφ₁ (-(a x * dφ₁ x) - b x * φ₁ x) x)
    (hφ₂ : HasDerivAt φ₂ (dφ₂ x) x) (hdφ₂ : HasDerivAt dφ₂ (-(a x * dφ₂ x) - b x * φ₂ x) x)
    (hW : φ₁ x * dφ₂ x - φ₂ x * dφ₁ x ≠ 0)
    (hC₁ : HasDerivAt C₁ (-(φ₂ x * f x) / (φ₁ x * dφ₂ x - φ₂ x * dφ₁ x)) x)
    (hC₂ : HasDerivAt C₂ (φ₁ x * f x / (φ₁ x * dφ₂ x - φ₂ x * dφ₁ x)) x) :
    HasDerivAt (fun t => C₁ t * φ₁ t + C₂ t * φ₂ t) (C₁ x * dφ₁ x + C₂ x * dφ₂ x) x ∧
    HasDerivAt (fun t => C₁ t * dφ₁ t + C₂ t * dφ₂ t)
      (f x - a x * (C₁ x * dφ₁ x + C₂ x * dφ₂ x) - b x * (C₁ x * φ₁ x + C₂ x * φ₂ x)) x := by
  obtain ⟨h1, h2⟩ := (cramer (c₁ := -(φ₂ x * f x) / (φ₁ x * dφ₂ x - φ₂ x * dφ₁ x))
    (c₂ := φ₁ x * f x / (φ₁ x * dφ₂ x - φ₂ x * dφ₁ x)) (f := f x) hW).2 ⟨rfl, rfl⟩
  exact ⟨by convert (hC₁.fun_mul hφ₁).fun_add (hC₂.fun_mul hφ₂) using 1; linear_combination -h1,
    by convert (hC₁.fun_mul hdφ₁).fun_add (hC₂.fun_mul hdφ₂) using 1; linear_combination -h2⟩

/-- **(vdc)**, forme intégrale : `y = -φ₁ ∫ φ₂ f / W + φ₂ ∫ φ₁ f / W` est solution de `(E)`. -/
theorem vdc_formula {a b f φ₁ φ₂ dφ₁ dφ₂ : ℝ → ℝ} (hf : Continuous f)
    (hφ₁ : ∀ x, HasDerivAt φ₁ (dφ₁ x) x)
    (hdφ₁ : ∀ x, HasDerivAt dφ₁ (-(a x * dφ₁ x) - b x * φ₁ x) x)
    (hφ₂ : ∀ x, HasDerivAt φ₂ (dφ₂ x) x)
    (hdφ₂ : ∀ x, HasDerivAt dφ₂ (-(a x * dφ₂ x) - b x * φ₂ x) x)
    (hW : ∀ x, φ₁ x * dφ₂ x - φ₂ x * dφ₁ x ≠ 0) (x₀ x : ℝ) :
    let C₁ := fun x => -∫ t in x₀..x, φ₂ t * f t / (φ₁ t * dφ₂ t - φ₂ t * dφ₁ t)
    let C₂ := fun x => ∫ t in x₀..x, φ₁ t * f t / (φ₁ t * dφ₂ t - φ₂ t * dφ₁ t)
    HasDerivAt (fun t => C₁ t * φ₁ t + C₂ t * φ₂ t) (C₁ x * dφ₁ x + C₂ x * dφ₂ x) x ∧
    HasDerivAt (fun t => C₁ t * dφ₁ t + C₂ t * dφ₂ t)
      (f x - a x * (C₁ x * dφ₁ x + C₂ x * dφ₂ x) - b x * (C₁ x * φ₁ x + C₂ x * φ₂ x)) x := by
  have hc : ∀ {g : ℝ → ℝ}, (∀ x, HasDerivAt g (dφ₁ x) x ∨ HasDerivAt g (dφ₂ x) x) →
      Continuous g := fun h => continuous_iff_continuousAt.2 fun x =>
    (h x).elim (·.continuousAt) (·.continuousAt)
  have c₁ := hc fun x => .inl (hφ₁ x); have c₂ := hc fun x => .inr (hφ₂ x)
  have d₁ : Continuous dφ₁ := continuous_iff_continuousAt.2 fun x => (hdφ₁ x).continuousAt
  have d₂ : Continuous dφ₂ := continuous_iff_continuousAt.2 fun x => (hdφ₂ x).continuousAt
  have cW : Continuous fun t => φ₁ t * dφ₂ t - φ₂ t * dφ₁ t := (c₁.mul d₂).sub (c₂.mul d₁)
  have k₁ : Continuous fun t => φ₁ t * f t / (φ₁ t * dφ₂ t - φ₂ t * dφ₁ t) :=
    (c₁.mul hf).div cW hW
  have k₂ : Continuous fun t => φ₂ t * f t / (φ₁ t * dφ₂ t - φ₂ t * dφ₁ t) :=
    (c₂.mul hf).div cW hW
  intro C₁ C₂
  refine vdc_solution (hφ₁ x) (hdφ₁ x) (hφ₂ x) (hdφ₂ x) (hW x) ?_ ?_
  · convert (k₂.integral_hasStrictDerivAt x₀ x).hasDerivAt.fun_neg using 1
    ring
  · exact (k₁.integral_hasStrictDerivAt x₀ x).hasDerivAt

/-- **§1/§5, Abel** : le wronskien de deux solutions de `(H)` vérifie `W' = -a W`. -/
theorem abel_wronskian {a b φ₁ φ₂ dφ₁ dφ₂ : ℝ → ℝ} {x : ℝ}
    (hφ₁ : HasDerivAt φ₁ (dφ₁ x) x) (hdφ₁ : HasDerivAt dφ₁ (-(a x * dφ₁ x) - b x * φ₁ x) x)
    (hφ₂ : HasDerivAt φ₂ (dφ₂ x) x) (hdφ₂ : HasDerivAt dφ₂ (-(a x * dφ₂ x) - b x * φ₂ x) x) :
    HasDerivAt (fun t => φ₁ t * dφ₂ t - φ₂ t * dφ₁ t)
      (-a x * (φ₁ x * dφ₂ x - φ₂ x * dφ₁ x)) x := by
  convert (hφ₁.fun_mul hdφ₂).fun_sub (hφ₂.fun_mul hdφ₁) using 1; ring

/-- **§1** : si `a` admet une primitive, le wronskien de deux solutions de `(H)` ne s'annule nulle
part dès qu'il est non nul en un point. -/
theorem wronskian_ne_zero {a b φ₁ φ₂ dφ₁ dφ₂ α : ℝ → ℝ} (hα : ∀ x, HasDerivAt α (a x) x)
    (hφ₁ : ∀ x, HasDerivAt φ₁ (dφ₁ x) x)
    (hdφ₁ : ∀ x, HasDerivAt dφ₁ (-(a x * dφ₁ x) - b x * φ₁ x) x)
    (hφ₂ : ∀ x, HasDerivAt φ₂ (dφ₂ x) x)
    (hdφ₂ : ∀ x, HasDerivAt dφ₂ (-(a x * dφ₂ x) - b x * φ₂ x) x)
    {x₀ : ℝ} (h₀ : φ₁ x₀ * dφ₂ x₀ - φ₂ x₀ * dφ₁ x₀ ≠ 0) (x : ℝ) :
    φ₁ x * dφ₂ x - φ₂ x * dφ₁ x ≠ 0 := by
  have hz : ∀ x, HasDerivAt (fun t => (φ₁ t * dφ₂ t - φ₂ t * dφ₁ t) * Real.exp (α t)) 0 x :=
    fun x => by
      convert (abel_wronskian (hφ₁ x) (hdφ₁ x) (hφ₂ x) (hdφ₂ x)).fun_mul (hα x).exp using 1
      ring
  have := is_const_of_deriv_eq_zero (fun x => (hz x).differentiableAt) (fun x => (hz x).deriv)
    x x₀
  intro h
  simp only [h, zero_mul] at this
  exact h₀ (by simpa [Real.exp_ne_zero] using this.symm)

end Operators

/-! ## §5.4 et exercice 4 : champs de vecteurs sur le plan des phases -/

section VectorFields

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Le champ de vecteurs `ξ` agissant sur les fonctions comme une dérivation :
`(X_ξ g)(p) = Dg(p)(ξ p)`. -/
def vf (ξ : E → E) (g : E → ℝ) : E → ℝ := fun p => fderiv ℝ g p (ξ p)

/-- Le commutateur `[X, X'] g = X (X' g) - X' (X g)`. -/
def bracket (X X' : (E → ℝ) → E → ℝ) (g : E → ℝ) : E → ℝ := X (X' g) - X' (X g)

/-- Sur le plan des phases `ℝ × ℝ`, `X_ξ = ξ₁ ∂_y + ξ₂ ∂_{y'}`. -/
lemma vf_prod (ξ : ℝ × ℝ → ℝ × ℝ) (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    vf ξ g p = (ξ p).1 * fderiv ℝ g p (1, 0) + (ξ p).2 * fderiv ℝ g p (0, 1) := by
  have : ξ p = (ξ p).1 • ((1 : ℝ), (0 : ℝ)) + (ξ p).2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
  rw [vf, this, map_add, map_smul, map_smul]; simp

lemma fderiv_fderiv_apply {g : E → ℝ} (hg : ContDiff ℝ 2 g) (p v w : E) :
    fderiv ℝ (fun q => fderiv ℝ g q v) p w = fderiv ℝ (fderiv ℝ g) p w v := by
  have hd : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  rw [fderiv_clm_apply (hd p) (differentiableAt_const v)]; simp

/-- **§5.4 / exercice 4** : `[X_φ, S] = X_φ`, où `X_φ` est le champ constant `v = (φ, φ')`
et `S = y ∂_y + y' ∂_{y'}` est le champ `ξ = id`. -/
theorem bracket_translation_dilation {g : E → ℝ} (hg : ContDiff ℝ 2 g) (v : E) :
    bracket (vf fun _ => v) (vf id) g = vf (fun _ => v) g := by
  funext p
  have hd : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hs := (hg.contDiffAt (x := p)).isSymmSndFDerivAt (by simp)
  simp only [bracket, Pi.sub_apply]
  unfold vf
  rw [fderiv_clm_apply (hd p) differentiableAt_id, fderiv_fderiv_apply hg]
  simp [hs v p]

/-- **§5.4** : les translations par deux solutions commutent, `[X_{φ₁}, X_{φ₂}] = 0`. -/
theorem bracket_translations {g : E → ℝ} (hg : ContDiff ℝ 2 g) (v w : E) :
    bracket (vf fun _ => v) (vf fun _ => w) g = 0 := by
  funext p
  simp only [bracket, Pi.sub_apply, Pi.zero_apply]
  unfold vf
  rw [fderiv_fderiv_apply hg, fderiv_fderiv_apply hg]
  exact sub_eq_zero.2 ((hg.contDiffAt (x := p)).isSymmSndFDerivAt (by simp) v w)

end VectorFields

/-! ## §6. Exponentielle de matrice -/

section Exponential

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- **Prop. 6.1**, pour la famille commutante `B(x) = β(x) • A₀` (donc `A(x) = β'(x) • A₀`
commute avec `B(x)`) : `(e^{B(x)})' = A(x) e^{B(x)}`. -/
theorem hasDerivAt_exp_scalar {β : ℝ → ℝ} {β' x : ℝ} (A₀ : 𝔸) (hβ : HasDerivAt β β' x) :
    HasDerivAt (fun t => NormedSpace.exp (β t • A₀))
      ((β' • A₀) * NormedSpace.exp (β x • A₀)) x := by
  simpa [Function.comp_def, smul_mul_assoc] using
    (hasDerivAt_exp_smul_const' A₀ (β x)).scomp x hβ

/-- **§6, Duhamel** (coefficients constants) :
`Y(x) = e^{(x-x₀)A} (Y₀ + ∫_{x₀}^x e^{-(s-x₀)A} F(s) ds)` est solution de `Y' = A Y + F`. -/
theorem duhamel (A Y₀ : 𝔸) {F : ℝ → 𝔸} (hF : Continuous F) (x₀ x : ℝ) :
    HasDerivAt (fun x => NormedSpace.exp ((x - x₀) • A) *
        (Y₀ + ∫ s in x₀..x, NormedSpace.exp ((x₀ - s) • A) * F s))
      (A * (NormedSpace.exp ((x - x₀) • A) *
        (Y₀ + ∫ s in x₀..x, NormedSpace.exp ((x₀ - s) • A) * F s)) + F x) x := by
  have hc : Continuous fun s : ℝ => NormedSpace.exp ((x₀ - s) • A) * F s :=
    ((differentiable_exp_smul_const ℝ A).continuous.comp
      (continuous_const.sub continuous_id)).mul hF
  have h1 : HasDerivAt (fun t => NormedSpace.exp ((t - x₀) • A))
      (A * NormedSpace.exp ((x - x₀) • A)) x := by
    simpa [Function.comp_def] using
      (hasDerivAt_exp_smul_const' A (x - x₀)).scomp x ((hasDerivAt_id' x).sub_const x₀)
  have hinv : NormedSpace.exp ((x - x₀) • A) * NormedSpace.exp ((x₀ - x) • A) = 1 := by
    rw [← NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ)
      (((Commute.refl A).smul_left _).smul_right _)
      ((NormedSpace.expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)
      ((NormedSpace.expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _),
      ← add_smul, show x - x₀ + (x₀ - x) = 0 by ring, zero_smul, NormedSpace.exp_zero]
  convert h1.fun_mul ((hc.integral_hasStrictDerivAt x₀ x).hasDerivAt.const_add Y₀) using 1
  rw [mul_assoc, ← mul_assoc (NormedSpace.exp ((x - x₀) • A)) (NormedSpace.exp ((x₀ - x) • A)),
    hinv, one_mul]

/-- **Exercice 5** : pour `A(x) = [[0,1],[0,x]]`, `[A(x), A(s)] = [[0, s-x],[0,0]]`. -/
theorem ex5 (x s : ℝ) : ⁅!![0, 1; 0, x], !![(0 : ℝ), 1; 0, s]⁆ = !![0, s - x; 0, 0] := by
  rw [Ring.lie_def, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp; ring

/-- **Exercice 5** : `[A(x), A(s)] ≠ 0` pour `x ≠ s`, donc la prop. 6.1 ne s'applique pas
directement. -/
theorem ex5_ne (x s : ℝ) (h : x ≠ s) : ⁅!![0, 1; 0, x], !![(0 : ℝ), 1; 0, s]⁆ ≠ 0 := by
  rw [ex5]; intro h'
  have := congrFun (congrFun h' 0) 1
  simp [sub_eq_zero] at this
  exact h this.symm

end Exponential


end CrochetLieEDO

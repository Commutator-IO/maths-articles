import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.Tactic.NormNum
import Mathlib.GroupTheory.CoprodI
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-!
# Engendrer et présenter `SL₂(ℤ)`

Formalisation de la fiche « Engendrer et présenter SL₂(ℤ) » (M. Hua, octobre 2026),
`sl2z-generateurs.tex`. Les numéros des énoncés sont ceux de la fiche.

## Modèles

* **Théorème 1.1** : c'est `SpecialLinearGroup.SL2Z_generators` de Mathlib, avec les
  matrices `ModularGroup.S` et `ModularGroup.T` de la fiche.
* **Le ping-pong** (théorème 2.2) : `PSL₂(ℤ)` agit fidèlement sur les irrationnels ; on prend
  directement les permutations `σ̄ : x ↦ -1/x` et `ρ̄ : x ↦ 1/(1 - x)` de `{x : ℝ // Irrational x}`
  et l'on applique `Monoid.CoprodI.lift_injective_of_ping_pong` de Mathlib aux sous-groupes
  qu'elles engendrent, d'ordres `2` et `3`, avec les irrationnels négatifs et positifs.
* **Le formulaire** (section 4) : les matrices de Grothendieck sont des éléments de
  `Matrix (Fin 2) (Fin 2) ℤ` écrits en clair, ainsi que leurs inverses, et chaque relation
  est un calcul de produits `2 × 2` (`Matrix.mul_fin_two`). Les indices `∞, 0, 1` sont
  écrits `I`, `0`, `1` dans les noms (`σI` pour `σ_∞`).

## Écarts avec la fiche

* Aucun énoncé de la fiche ne s'est révélé faux.

## Omis

La fidélité de l'action de `PSL₂(ℤ)` sur les irrationnels et la surjectivité, qui
identifient le groupe engendré par `σ̄` et `ρ̄` à `PSL₂(ℤ)` (théorème 2.2) ; le corollaire 2.3
(présentation de `SL₂(ℤ)`), la proposition 3.1 (Sanov), les remarques et les exercices.
-/

namespace SL2ZGenerateurs

open Matrix

/-! ## 1. Engendrer -/

/-- **Théorème 1.1** : `SL₂(ℤ)` est engendré par `S` et `T`. -/
theorem generateurs :
    Subgroup.closure {ModularGroup.S, ModularGroup.T} = (⊤ : Subgroup (SpecialLinearGroup (Fin 2) ℤ)) :=
  SpecialLinearGroup.SL2Z_generators

/-- Les matrices de la fiche : `S = !![0, -1; 1, 0]` et `T = !![1, 1; 0, 1]`. -/
theorem S_T :
    (ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ) = !![0, -1; 1, 0] ∧
      (ModularGroup.T : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 1; 0, 1] :=
  ⟨ModularGroup.coe_S, ModularGroup.coe_T⟩

/-! ## 4. Le formulaire de 1982 -/

/-- `ω = -I`. -/
def ω : Matrix (Fin 2) (Fin 2) ℤ := !![-1, 0; 0, -1]
def ρ : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; -1, 1]
def ρinv : Matrix (Fin 2) (Fin 2) ℤ := !![1, -1; 1, 0]
def σI : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; -1, 0]
def σ0 : Matrix (Fin 2) (Fin 2) ℤ := !![-1, 1; -2, 1]
def σ1 : Matrix (Fin 2) (Fin 2) ℤ := !![-1, 2; -1, 1]
def σIinv : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; 1, 0]
def σ0inv : Matrix (Fin 2) (Fin 2) ℤ := !![1, -1; 2, -1]
def σ1inv : Matrix (Fin 2) (Fin 2) ℤ := !![1, -2; 1, -1]
def ε0 : Matrix (Fin 2) (Fin 2) ℤ := !![1, -1; 0, 1]
def ε1 : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 1, 1]
def εI : Matrix (Fin 2) (Fin 2) ℤ := !![2, -1; 1, 0]
def Γ0 : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]
def ΓI : Matrix (Fin 2) (Fin 2) ℤ := !![-1, 0; 0, 1]

/-- Les inverses écrits en clair sont bien les inverses. -/
theorem inverses :
    ρ * ρinv = 1 ∧ σI * σIinv = 1 ∧ σ0 * σ0inv = 1 ∧ σ1 * σ1inv = 1 := by
  simp only [ρ, ρinv, σI, σIinv, σ0, σ0inv, σ1, σ1inv, mul_fin_two, one_fin_two]
  norm_num

/-- **Section 1** : `σ = S⁻¹` et `ρ = (TS)⁻¹`, d'ordres `4` et `6`, avec `σ² = ρ³ = ω`. -/
theorem ordres :
    σI * σI = ω ∧ ρ * ρ * ρ = ω ∧ ω * ω = 1 ∧
      σIinv = (ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ) ∧
      (ModularGroup.T : Matrix (Fin 2) (Fin 2) ℤ) * ModularGroup.S * ρ = 1 := by
  rw [ModularGroup.coe_S, ModularGroup.coe_T]
  simp only [ρ, σI, σIinv, ω, mul_fin_two, one_fin_two]
  norm_num

/-- **Proposition 4.1** : `σ_i² = ω` et la conjugaison par `ρ` permute circulairement les
`σ_i` (`∞ → 0 → 1 → ∞`). -/
theorem sigma_conj :
    σ0 * σ0 = ω ∧ σ1 * σ1 = ω ∧
      ρ * σI * ρinv = σ0 ∧ ρ * σ0 * ρinv = σ1 ∧ ρ * σ1 * ρinv = σI := by
  simp only [ρ, ρinv, σI, σ0, σ1, ω, mul_fin_two]
  norm_num

/-- **Proposition 4.1** : la conjugaison par `ρ` permute circulairement les `ε_i`. -/
theorem eps_conj : ρ * εI * ρinv = ε0 ∧ ρ * ε0 * ρinv = ε1 ∧ ρ * ε1 * ρinv = εI := by
  simp only [ρ, ρinv, εI, ε0, ε1, mul_fin_two]
  norm_num

/-- **Proposition 4.1**, la formule corrigée : `ε_i = σ_{i-1}⁻¹ ρ`. -/
theorem eps_eq : ε0 = σIinv * ρ ∧ ε1 = σ0inv * ρ ∧ εI = σ1inv * ρ := by
  simp only [ρ, εI, ε0, ε1, σIinv, σ0inv, σ1inv, mul_fin_two]
  norm_num

/-- **Remarque 4.2** : la formule de la page, `ε_i = σ_i⁻¹ ρ`, est fausse pour chaque `i`. -/
theorem eps_page_faux : ε0 ≠ σ0inv * ρ ∧ ε1 ≠ σ1inv * ρ ∧ εI ≠ σIinv * ρ := by
  simp only [ρ, εI, ε0, ε1, σIinv, σ0inv, σ1inv, mul_fin_two]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    · have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => (M 0 0, M 0 1, M 1 0, M 1 1)) h
      norm_num at this

/-- **Proposition 4.1** : les carrés `ϱ_i = ε_i²` vérifient `ϱ_∞ ϱ_1 ϱ_0 = ω`. -/
theorem lacets : (εI * εI) * (ε1 * ε1) * (ε0 * ε0) = ω := by
  simp only [εI, ε1, ε0, ω, mul_fin_two]
  norm_num

/-- **Remarque 4.2** : avec les matrices de 1982, `Γ_∞ = σ⁻¹ Γ_0`, et non `σ Γ_0` comme
l'écrit la page (formule du formulaire de 1981), qui ne vaut qu'au signe `ω` près. -/
theorem gamma_infini : ΓI = σIinv * Γ0 ∧ ΓI ≠ σI * Γ0 ∧ ω * ΓI = σI * Γ0 := by
  simp only [ΓI, σIinv, σI, Γ0, ω, mul_fin_two]
  refine ⟨by norm_num, fun h => ?_, by norm_num⟩
  have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) h
  norm_num at this

/-! ## 2. Le ping-pong -/

section PingPong

/-- Les irrationnels, sur lesquels les homographies à coefficients entiers agissent. -/
abbrev Irr := {x : ℝ // Irrational x}

theorem irr_one_sub (x : Irr) : Irrational (1 - x.1) := by simpa using x.2.natCast_sub 1

/-- `σ̄ (x) = -1/x`, image de `σ` dans les permutations des irrationnels. -/
noncomputable def sigmaBar : Equiv.Perm Irr where
  toFun x := ⟨-x.1⁻¹, x.2.inv.neg⟩
  invFun x := ⟨-x.1⁻¹, x.2.inv.neg⟩
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)

/-- `ρ̄ (x) = 1/(1 - x)`, image de `ρ`, de réciproque `x ↦ 1 - 1/x`. -/
noncomputable def rhoBar : Equiv.Perm Irr where
  toFun x := ⟨(1 - x.1)⁻¹, (irr_one_sub x).inv⟩
  invFun x := ⟨1 - x.1⁻¹, by simpa using x.2.inv.natCast_sub 1⟩
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)

theorem sigmaBar_apply (x : Irr) : (sigmaBar x).1 = -x.1⁻¹ := rfl

theorem rhoBar_apply (x : Irr) : (rhoBar x).1 = (1 - x.1)⁻¹ := rfl

/-- Un point irrationnel quelconque, pour tester qu'une permutation n'est pas l'identité. -/
noncomputable def sqrt2 : Irr := ⟨√2, irrational_sqrt_two⟩

theorem sigmaBar_sq : sigmaBar ^ 2 = 1 := by
  ext x
  simp [sq, sigmaBar_apply]

theorem rhoBar_cube : rhoBar ^ 3 = 1 := by
  ext x
  show (rhoBar (rhoBar (rhoBar x))).1 = x.1
  have h0 := x.2.ne_zero
  have h1 : 1 - x.1 ≠ 0 := sub_ne_zero.2 x.2.ne_one.symm
  simp only [rhoBar_apply]
  have e1 : 1 - (1 - x.1)⁻¹ = -x.1 / (1 - x.1) := by field_simp; ring
  rw [e1, inv_div, show 1 - (1 - x.1) / -x.1 = x.1⁻¹ by field_simp; ring, inv_inv]

/-- `σ̄` n'a pas de point fixe : `-1/x = x` donnerait `x² = -1`. -/
theorem sigmaBar_ne_one : sigmaBar ≠ 1 := by
  intro h
  have := congrArg (fun g : Equiv.Perm Irr => (g sqrt2).1) h
  simp only [sigmaBar_apply, Equiv.Perm.coe_one, id] at this
  have h0 : sqrt2.1 ≠ 0 := sqrt2.2.ne_zero
  field_simp at this
  nlinarith [sq_nonneg sqrt2.1]

/-- `ρ̄` n'a pas de point fixe : `1/(1 - x) = x` donnerait `x² - x + 1 = 0`. -/
theorem rhoBar_ne_one : rhoBar ≠ 1 := by
  intro h
  have := congrArg (fun g : Equiv.Perm Irr => (g sqrt2).1) h
  simp only [rhoBar_apply, Equiv.Perm.coe_one, id] at this
  have h1 : 1 - sqrt2.1 ≠ 0 := sub_ne_zero.2 sqrt2.2.ne_one.symm
  field_simp at this
  nlinarith [sq_nonneg (sqrt2.1 - 1 / 2)]

/-- **Section 2** : `σ̄` est d'ordre `2`. -/
theorem orderOf_sigmaBar : orderOf sigmaBar = 2 :=
  orderOf_eq_prime sigmaBar_sq sigmaBar_ne_one

/-- **Section 2** : `ρ̄` est d'ordre `3`. -/
theorem orderOf_rhoBar : orderOf rhoBar = 3 :=
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  orderOf_eq_prime rhoBar_cube rhoBar_ne_one

/-- Les deux générateurs, indexés par `Fin 2`. -/
noncomputable def gen (i : Fin 2) : Equiv.Perm Irr := if i = 0 then sigmaBar else rhoBar

/-- Les ensembles du ping-pong : les irrationnels négatifs, puis positifs. -/
def pp (i : Fin 2) : Set Irr := if i = 0 then {x | x.1 < 0} else {x | 0 < x.1}

theorem eq_of_mem_zpowers_two {g h : Equiv.Perm Irr} (hg : orderOf g = 2)
    (hh : h ∈ Subgroup.zpowers g) (h1 : h ≠ 1) : h = g := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
  rw [← zpow_mod_orderOf, hg] at h1 ⊢
  push_cast at h1 ⊢
  rcases (by omega : k % 2 = 0 ∨ k % 2 = 1) with hk | hk
  · rw [hk, zpow_zero] at h1; exact absurd rfl h1
  · rw [hk, zpow_one]

theorem eq_of_mem_zpowers_three {g h : Equiv.Perm Irr} (hg : orderOf g = 3)
    (hh : h ∈ Subgroup.zpowers g) (h1 : h ≠ 1) : h = g ∨ h = g * g := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
  rw [← zpow_mod_orderOf, hg] at h1 ⊢
  push_cast at h1 ⊢
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with hk | hk | hk
  · rw [hk, zpow_zero] at h1; exact absurd rfl h1
  · left; rw [hk, zpow_one]
  · right; rw [hk, zpow_two]

/-- **Théorème 2.2**, l'injectivité, par le lemme du ping-pong de Mathlib : le morphisme du
produit libre des sous-groupes engendrés par `σ̄` (d'ordre `2`) et `ρ̄` (d'ordre `3`) vers les
permutations des irrationnels est injectif. Le groupe engendré par les deux homographies
`x ↦ -1/x` et `x ↦ 1/(1 - x)` est donc le produit libre `ℤ/2 ∗ ℤ/3`. -/
theorem pingpong :
    Function.Injective (Monoid.CoprodI.lift fun i => (Subgroup.zpowers (gen i)).subtype) := by
  refine Monoid.CoprodI.lift_injective_of_ping_pong _ ?_ pp ?_ ?_ ?_
  · -- `ρ̄` engendre un groupe à trois éléments.
    refine Or.inr ⟨1, ?_⟩
    have hc : Nat.card (Subgroup.zpowers (gen 1)) = 3 := by
      rw [Nat.card_zpowers]; simpa [gen] using orderOf_rhoBar
    have : Finite (Subgroup.zpowers (gen 1)) := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
    rw [← Nat.cast_card, hc]
    norm_num
  · intro i
    fin_cases i
    · exact ⟨⟨-√2, irrational_sqrt_two.neg⟩, by simp [pp]⟩
    · exact ⟨sqrt2, by simp [pp, sqrt2]⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact Set.disjoint_left.2 fun x hx hx' => by simp [pp] at hx hx'; linarith
    · exact Set.disjoint_left.2 fun x hx hx' => by simp [pp] at hx hx'; linarith
    · exact absurd rfl hij
  · intro i j hij h h1
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · -- `σ̄` envoie les positifs chez les négatifs.
      have hs : (h : Equiv.Perm Irr) = sigmaBar :=
        eq_of_mem_zpowers_two orderOf_sigmaBar (by simpa [gen] using h.2)
          (fun e => h1 (Subtype.ext e))
      rintro _ ⟨x, hx, rfl⟩
      have hx' : 0 < x.1 := by simpa [pp] using hx
      show ((h : Equiv.Perm Irr) • x).1 < 0
      rw [Equiv.Perm.smul_def, hs, sigmaBar_apply]
      exact neg_neg_of_pos (inv_pos.2 hx' : (0 : ℝ) < x.1⁻¹)
    · -- `ρ̄` et `ρ̄²` envoient les négatifs chez les positifs.
      have hr := eq_of_mem_zpowers_three orderOf_rhoBar (by simpa [gen] using h.2)
        (fun e => h1 (Subtype.ext e))
      rintro _ ⟨x, hx, rfl⟩
      have hx' : x.1 < 0 := by simpa [pp] using hx
      show 0 < ((h : Equiv.Perm Irr) • x).1
      have key : ∀ y : Irr, y.1 < 1 → 0 < (rhoBar y).1 ∧ (y.1 < 0 → (rhoBar y).1 < 1) := by
        intro y hy
        rw [rhoBar_apply]
        refine ⟨inv_pos.2 (by linarith), fun hy0 => ?_⟩
        rw [inv_lt_one₀ (by linarith)]
        linarith
      rw [Equiv.Perm.smul_def]
      rcases hr with e | e <;> rw [e]
      · exact (key x (by linarith)).1
      · exact (key _ ((key x (by linarith)).2 hx')).1
    · exact absurd rfl hij

end PingPong

end SL2ZGenerateurs

import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.Tactic.NormNum

/-!
# Engendrer et présenter `SL₂(ℤ)`

Formalisation de la fiche « Engendrer et présenter SL₂(ℤ) » (M. Hua, octobre 2026),
`sl2z-generateurs.tex`. Les numéros des énoncés sont ceux de la fiche.

## Modèles

* **Théorème 1.1** : c'est `SpecialLinearGroup.SL2Z_generators` de Mathlib, avec les
  matrices `ModularGroup.S` et `ModularGroup.T` de la fiche.
* **Le formulaire** (section 4) : les matrices de Grothendieck sont des éléments de
  `Matrix (Fin 2) (Fin 2) ℤ` écrits en clair, ainsi que leurs inverses, et chaque relation
  est un calcul de produits `2 × 2` (`Matrix.mul_fin_two`). Les indices `∞, 0, 1` sont
  écrits `I`, `0`, `1` dans les noms (`σI` pour `σ_∞`).

## Écarts avec la fiche

* Aucun énoncé de la fiche ne s'est révélé faux.

## Omis

Le lemme du ping-pong et le théorème 2.2 (`PSL₂(ℤ) ≃ ℤ/2 ∗ ℤ/3`), le corollaire 2.3
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

end SL2ZGenerateurs

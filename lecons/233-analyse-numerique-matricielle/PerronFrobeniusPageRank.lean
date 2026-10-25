import Mathlib

/-!
# Du théorème de Perron-Frobenius à PageRank

Formalisation de la fiche « Du théorème de Perron-Frobenius à PageRank » (M. Hua, octobre
2026), `perron-frobenius-pagerank.tex`. Les numéros des énoncés sont ceux de la fiche.

## Modèles

* Les pages sont indexées par un type fini `ι`. Les vecteurs sont des fonctions `ι → ℝ`, et le
  produit `P^T x` de la fiche est le produit à gauche `x ᵥ* P` de Mathlib : on écrit les
  distributions en ligne, ce qui évite toutes les transpositions.
* `l1 w = ∑ |wᵢ|` est la norme `‖w‖₁` de la fiche. Elle est définie à la main : la norme de
  Mathlib sur `ι → ℝ` est la norme sup, qui ne sert ici qu'à obtenir la complétude.
* **§4.2.** Le web est une relation `lien : ι → ι → Prop` décidable ; `liens lien` est la
  matrice `P`, `pendante lien` le vecteur `d` des pages sans issue et `matP1 lien v` la matrice
  `P₁ = P + d vᵀ`. La matrice Google `google c P v = c P + (1 - c) 𝟙 vᵀ` est définie pour toute
  matrice `P`, sur un anneau commutatif quelconque, pour servir aussi au théorème 5.1 sur `ℂ`.

## Écarts avec la fiche

* Aucun énoncé de la fiche ne s'est révélé faux.
* Prop. 4.4 : l'existence du vecteur PageRank est démontrée sans le théorème de Perron, par le
  théorème du point fixe : l'itération `x ↦ x ᵥ* G` est `c`-contractante pour `‖·‖₁` sur les
  distributions (théorème 5.3), et `ι → ℝ` est complet. La formule `π = (1-c) ∑ cᵏ (P₁ᵀ)ᵏ v`
  n'est démontrée que sous la forme du système linéaire `π - c π P₁ = (1 - c) v`.
* Th. 5.1 : on démontre que toute valeur propre `μ ≠ 1` de `P₁`, de vecteur propre à gauche
  `w`, donne la valeur propre `c μ` de `G` avec le même vecteur propre (sur tout corps), et que
  toute valeur propre réelle `λ ≠ 1` de `G` vérifie `|λ| ≤ c`. L'égalité des spectres avec
  multiplicités (la similitude par `Q = (𝟙 | X)`) n'est pas démontrée.
* Ex. 4.5 : le vecteur PageRank est calculé exactement,
  `π = (3080, 4389, 1380, 3080) / 11929`, ce qui redonne les valeurs `0,258 ; 0,368 ; 0,116 ;
  0,258` de la fiche.
* Le tableau des nombres d'itérations (§5.1) est vérifié : pour chaque `c`, l'entier indiqué est
  le plus petit `k` tel que `2 cᵏ ≤ 10⁻⁴`.

## Omis

Les sections 2 et 3 (théorèmes de Perron et de Perron-Frobenius, lemme `(I + A)^{n-1} > 0`) :
Mathlib ne contient pas encore la théorie des matrices positives ; le théorème 4.2 pour une
matrice stochastique quelconque ; l'exemple 5.4 (vitesse observée), l'exemple 6.1 (ferme de
liens) et la section 7 (méthodes itératives) ; les exercices 1 et 3.
-/

open Finset Matrix Filter Topology

noncomputable section

namespace PageRank

variable {ι : Type*} [Fintype ι]

/-! ## Définitions -/

/-- Une matrice **stochastique** : coefficients positifs, lignes de somme `1`. -/
def EstStochastique (P : Matrix ι ι ℝ) : Prop :=
  (∀ i j, 0 ≤ P i j) ∧ ∀ i, ∑ j, P i j = 1

/-- Une **distribution** : vecteur positif de somme `1`. -/
def EstDistribution (x : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1

/-- La norme `‖w‖₁ = ∑ |wᵢ|`. -/
def l1 (w : ι → ℝ) : ℝ := ∑ i, |w i|

/-- La **matrice Google** `G = c P + (1 - c) 𝟙 vᵀ`. -/
def google {R : Type*} [CommRing R] (c : R) (P : Matrix ι ι R) (v : ι → R) : Matrix ι ι R :=
  c • P + (1 - c) • vecMulVec (fun _ => 1) v

/-- `π` est **un vecteur PageRank** de `G` : une distribution stationnaire, `G^T π = π`. -/
def EstPageRank (G : Matrix ι ι ℝ) (π : ι → ℝ) : Prop :=
  EstDistribution π ∧ π ᵥ* G = π

/-! ## La norme `‖·‖₁` -/

theorem l1_nonneg (w : ι → ℝ) : 0 ≤ l1 w :=
  sum_nonneg fun i _ => abs_nonneg (w i)

theorem l1_smul (a : ℝ) (w : ι → ℝ) : l1 (a • w) = |a| * l1 w := by
  simp [l1, abs_mul, mul_sum]

theorem l1_sub_comm (x y : ι → ℝ) : l1 (x - y) = l1 (y - x) := by
  simp only [l1, Pi.sub_apply, abs_sub_comm]

theorem l1_sub_le (x y z : ι → ℝ) : l1 (x - z) ≤ l1 (x - y) + l1 (y - z) := by
  simp only [l1, Pi.sub_apply, ← sum_add_distrib]
  exact sum_le_sum fun i _ => abs_sub_le (x i) (y i) (z i)

theorem eq_of_l1_sub_eq_zero {x y : ι → ℝ} (h : l1 (x - y) = 0) : x = y := by
  funext i
  have := (sum_eq_zero_iff_of_nonneg fun j _ => abs_nonneg ((x - y) j)).1 h i (mem_univ i)
  simpa [sub_eq_zero] using this

/-- Une distance qui se contracte d'un facteur `c < 1` est nulle. -/
theorem eq_of_l1_le {x y : ι → ℝ} {c : ℝ} (hc1 : c < 1) (h : l1 (x - y) ≤ c * l1 (x - y)) :
    x = y :=
  eq_of_l1_sub_eq_zero (le_antisymm (by nlinarith [l1_nonneg (x - y)]) (l1_nonneg _))

/-- La norme sup est majorée par la norme `‖·‖₁`. -/
theorem norm_le_l1 (w : ι → ℝ) : ‖w‖ ≤ l1 w :=
  (pi_norm_le_iff_of_nonneg (l1_nonneg w)).2 fun i => by
    rw [Real.norm_eq_abs]
    exact single_le_sum (fun j _ => abs_nonneg (w j)) (mem_univ i)

/-- Deux distributions sont à distance au plus `2`. -/
theorem l1_sub_le_two {x y : ι → ℝ} (hx : EstDistribution x) (hy : EstDistribution y) :
    l1 (x - y) ≤ 2 := by
  have h : ∀ z : ι → ℝ, EstDistribution z → l1 z = 1 := fun z hz => by
    rw [l1, ← hz.2]; exact sum_congr rfl fun i _ => abs_of_nonneg (hz.1 i)
  have hx' : ∑ i, |x i| = 1 := h x hx
  have hy' : ∑ i, |y i| = 1 := h y hy
  calc l1 (x - y) ≤ ∑ i, (|x i| + |y i|) := sum_le_sum fun i _ => by
        simpa using abs_sub_le (x i) 0 (y i)
    _ = 2 := by rw [sum_add_distrib, hx', hy']; norm_num

/-! ## Matrices stochastiques -/

/-- Une matrice dont les lignes sont de somme `1` conserve la somme des coordonnées. -/
theorem sum_vecMul {R : Type*} [CommRing R] {P : Matrix ι ι R} (hP : ∀ i, ∑ j, P i j = 1)
    (w : ι → R) : ∑ j, (w ᵥ* P) j = ∑ i, w i := by
  simp only [vecMul, dotProduct]
  rw [sum_comm]
  simp [← mul_sum, hP]

theorem distribution_vecMul {P : Matrix ι ι ℝ} (hP : EstStochastique P) {x : ι → ℝ}
    (hx : EstDistribution x) : EstDistribution (x ᵥ* P) :=
  ⟨fun j => sum_nonneg fun i _ => mul_nonneg (hx.1 i) (hP.1 i j), by
    rw [sum_vecMul hP.2, hx.2]⟩

/-- Une matrice stochastique ne fait pas grandir la norme `‖·‖₁` : `‖P^T w‖₁ ≤ ‖w‖₁`. -/
theorem l1_vecMul_le {P : Matrix ι ι ℝ} (hP : EstStochastique P) (w : ι → ℝ) :
    l1 (w ᵥ* P) ≤ l1 w := by
  calc l1 (w ᵥ* P) = ∑ j, |∑ i, w i * P i j| := rfl
    _ ≤ ∑ j, ∑ i, |w i| * P i j := sum_le_sum fun j _ =>
        (abs_sum_le_sum_abs _ _).trans_eq
          (sum_congr rfl fun i _ => by rw [abs_mul, abs_of_nonneg (hP.1 i j)])
    _ = ∑ i, |w i| * ∑ j, P i j := by rw [sum_comm]; simp [mul_sum]
    _ = l1 w := by simp [hP.2, l1]

/-! ## §4.2. La matrice Google -/

section Web

variable (lien : ι → ι → Prop) [DecidableRel lien]

/-- Le nombre `dᵢ` de liens sortants de la page `i`. -/
def degre (i : ι) : ℕ := #(univ.filter (lien i))

/-- La matrice des liens : `P i j = 1/dᵢ` si `i → j`, `0` sinon. -/
def liens : Matrix ι ι ℝ := fun i j => if lien i j then ((degre lien i : ℝ))⁻¹ else 0

/-- Le vecteur indicateur `d` des pages sans issue. -/
def pendante (i : ι) : ℝ := if degre lien i = 0 then 1 else 0

/-- La matrice `P₁ = P + d vᵀ` : depuis une page sans issue, on repart selon `v`. -/
def matP1 (v : ι → ℝ) : Matrix ι ι ℝ := liens lien + vecMulVec (pendante lien) v

/-- La ligne `i` de `P` est de somme `1`, ou nulle si `i` est sans issue. -/
theorem somme_liens (i : ι) :
    ∑ j, liens lien i j = if degre lien i = 0 then 0 else 1 := by
  simp only [liens]
  rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
  split_ifs with h
  · simp [show #(univ.filter (lien i)) = 0 from h]
  · exact mul_inv_cancel₀ (Nat.cast_ne_zero.2 h)

/-- **§4.2** : `P₁` est stochastique. -/
theorem stochastique_matP1 {v : ι → ℝ} (hv : EstDistribution v) :
    EstStochastique (matP1 lien v) := by
  constructor
  · intro i j
    have := hv.1 j
    simp only [matP1, Matrix.add_apply, vecMulVec_apply, liens, pendante]
    split_ifs <;> positivity
  · intro i
    simp only [matP1, Matrix.add_apply, vecMulVec_apply, sum_add_distrib, ← mul_sum, hv.2,
      somme_liens, pendante]
    split_ifs <;> norm_num

end Web

section Google

variable {R : Type*} [CommRing R]

/-- Le produit par la matrice Google sans former `G` :
`G^T x = c P^T x + (1 - c) (∑ xᵢ) v`. -/
theorem vecMul_google (c : R) (P : Matrix ι ι R) (v x : ι → R) :
    x ᵥ* google c P v = c • (x ᵥ* P) + ((1 - c) * ∑ i, x i) • v := by
  funext j
  simp only [vecMul, dotProduct, google, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul,
    Pi.add_apply, Pi.smul_apply, mul_sum, sum_mul, ← sum_add_distrib]
  exact sum_congr rfl fun i _ => by ring

/-- **Th. 5.1** (un sens) : un vecteur propre à gauche de `P₁` pour `μ ≠ 1` est vecteur
propre à gauche de `G` pour `c μ`. -/
theorem valeur_propre_google {K : Type*} [Field K] {P : Matrix ι ι K}
    (hP : ∀ i, ∑ j, P i j = 1) (c μ : K) (v w : ι → K) (hw : w ᵥ* P = μ • w) (hμ : μ ≠ 1) :
    w ᵥ* google c P v = (c * μ) • w := by
  have hs : ∑ i, w i = 0 := by
    have h := sum_vecMul hP w
    rw [hw] at h
    simp only [Pi.smul_apply, smul_eq_mul, ← mul_sum] at h
    have : (μ - 1) * ∑ i, w i = 0 := by rw [sub_mul, h, one_mul, sub_self]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hμ)
  rw [vecMul_google, hw, hs, mul_zero, zero_smul, add_zero, smul_smul]

end Google

variable {c : ℝ} {P : Matrix ι ι ℝ} {v : ι → ℝ}

/-- **Prop. 4.4** : `G` est stochastique… -/
theorem stochastique_google (hP : EstStochastique P) (hv : EstDistribution v) (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) : EstStochastique (google c P v) := by
  constructor
  · intro i j
    have := hP.1 i j; have := hv.1 j
    simp only [google, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, one_mul]
    have : 0 ≤ 1 - c := by linarith
    positivity
  · intro i
    simp only [google, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, one_mul,
      sum_add_distrib, ← mul_sum, hP.2, hv.2]
    ring

/-- … et strictement positive si `v > 0` et `c < 1`. -/
theorem google_pos (hP : EstStochastique P) (hv : ∀ j, 0 < v j) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (i j : ι) : 0 < google c P v i j := by
  have := hP.1 i j; have := hv j
  simp only [google, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, one_mul]
  have : 0 < 1 - c := by linarith
  positivity

/-- Sur les distributions, `G^T x = c P^T x + (1 - c) v`. -/
theorem vecMul_google_of_distribution {x : ι → ℝ} (hx : EstDistribution x) :
    x ᵥ* google c P v = c • (x ᵥ* P) + (1 - c) • v := by
  rw [vecMul_google, hx.2, mul_one]

/-- **Th. 5.3** (cœur de la preuve) : sur deux vecteurs de même somme, l'itération est
`c`-contractante pour `‖·‖₁`. -/
theorem l1_vecMul_google_sub (hP : EstStochastique P) (hc0 : 0 ≤ c) {x y : ι → ℝ}
    (hxy : ∑ i, x i = ∑ i, y i) :
    l1 (x ᵥ* google c P v - y ᵥ* google c P v) ≤ c * l1 (x - y) := by
  have h : x ᵥ* google c P v - y ᵥ* google c P v = c • ((x - y) ᵥ* P) := by
    rw [vecMul_google, vecMul_google, hxy, sub_vecMul, smul_sub]; abel
  rw [h, l1_smul, abs_of_nonneg hc0]
  exact mul_le_mul_of_nonneg_left (l1_vecMul_le hP _) hc0

/-- L'itération de la méthode de la puissance, `x ↦ G^T x`. -/
abbrev iteration (c : ℝ) (P : Matrix ι ι ℝ) (v : ι → ℝ) : (ι → ℝ) → ι → ℝ :=
  fun x => x ᵥ* google c P v

theorem distribution_iterate (hP : EstStochastique P) (hv : EstDistribution v) (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) {x : ι → ℝ} (hx : EstDistribution x) (k : ℕ) :
    EstDistribution ((iteration c P v)^[k] x) := by
  induction k with
  | zero => exact hx
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact distribution_vecMul (stochastique_google hP hv hc0 hc1) ih

/-- **Prop. 4.4** : si `0 ≤ c < 1`, la matrice Google a un unique vecteur PageRank. -/
theorem existe_unique_pagerank (hP : EstStochastique P) (hv : EstDistribution v) (hc0 : 0 ≤ c)
    (hc1 : c < 1) : ∃! π, EstPageRank (google c P v) π := by
  set f := iteration c P v
  set u : ℕ → ι → ℝ := fun k => f^[k] v
  have hu : ∀ k, EstDistribution (u k) := distribution_iterate hP hv hc0 hc1.le hv
  -- Les écarts successifs décroissent comme `cᵏ`.
  have hgeom : ∀ k, l1 (u (k + 1) - u k) ≤ l1 (u 1 - u 0) * c ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h := l1_vecMul_google_sub (v := v) hP hc0 ((hu (k + 1)).2.trans (hu k).2.symm)
      have e : ∀ m, u (m + 1) = u m ᵥ* google c P v := fun m =>
        Function.iterate_succ_apply' f m v
      rw [← e, ← e] at h
      calc l1 (u (k + 2) - u (k + 1)) ≤ c * l1 (u (k + 1) - u k) := h
        _ ≤ c * (l1 (u 1 - u 0) * c ^ k) := mul_le_mul_of_nonneg_left ih hc0
        _ = l1 (u 1 - u 0) * c ^ (k + 1) := by ring
  have hcauchy : CauchySeq u := by
    refine cauchySeq_of_le_geometric c (l1 (u 1 - u 0)) hc1 fun k => ?_
    rw [dist_eq_norm]
    exact (norm_le_l1 _).trans ((l1_sub_comm _ _).trans_le (hgeom k))
  obtain ⟨π, hπ⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hcoord : ∀ i, Tendsto (fun k => u k i) atTop (𝓝 (π i)) := fun i =>
    ((continuous_apply i).tendsto π).comp hπ
  have hdist : EstDistribution π := by
    refine ⟨fun i => ge_of_tendsto (hcoord i) (Eventually.of_forall fun k => (hu k).1 i), ?_⟩
    have h := tendsto_finsetSum univ fun i _ => hcoord i
    have h1 : (fun k => ∑ i, u k i) = fun _ => 1 := funext fun k => (hu k).2
    rw [h1] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  have hfix : π ᵥ* google c P v = π := by
    have hcont : Continuous f := continuous_id.matrix_vecMul continuous_const
    have h1 : Tendsto (fun k => f (u k)) atTop (𝓝 (f π)) := (hcont.tendsto π).comp hπ
    have h2 : Tendsto (fun k => f (u k)) atTop (𝓝 π) := by
      have : (fun k => f (u k)) = fun k => u (k + 1) := funext fun k =>
        (Function.iterate_succ_apply' f k v).symm
      rw [this]
      exact hπ.comp (tendsto_add_atTop_nat 1)
    exact tendsto_nhds_unique h1 h2
  refine ⟨π, ⟨hdist, hfix⟩, fun π' ⟨hd', hf'⟩ => ?_⟩
  refine eq_of_l1_le hc1 ?_
  have h := l1_vecMul_google_sub (v := v) hP hc0 (hd'.2.trans hdist.2.symm)
  rwa [hf', hfix] at h

/-- **Prop. 4.4** : le vecteur PageRank résout le système linéaire `(I - c P₁ᵀ) π = (1 - c) v`. -/
theorem pagerank_systeme {π : ι → ℝ} (h : EstPageRank (google c P v) π) :
    π - c • (π ᵥ* P) = (1 - c) • v := by
  have := h.2
  rw [vecMul_google_of_distribution h.1] at this
  rw [sub_eq_iff_eq_add']
  exact this.symm

/-- **Exercice 4** : `πⱼ ≥ (1 - c) vⱼ`. -/
theorem pagerank_ge (hP : EstStochastique P) (hc0 : 0 ≤ c) {π : ι → ℝ}
    (h : EstPageRank (google c P v) π) (j : ι) : (1 - c) * v j ≤ π j := by
  have e := congr_fun h.2 j
  rw [vecMul_google_of_distribution h.1] at e
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e
  have : 0 ≤ (π ᵥ* P) j := ((distribution_vecMul hP h.1).1 j)
  nlinarith

/-- **Th. 5.3** : `‖π⁽ᵏ⁾ - π‖₁ ≤ cᵏ ‖π⁽⁰⁾ - π‖₁`. -/
theorem l1_iterate_sub_le (hP : EstStochastique P) (hv : EstDistribution v) (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) {π x : ι → ℝ} (hπ : EstPageRank (google c P v) π) (hx : EstDistribution x)
    (k : ℕ) : l1 ((iteration c P v)^[k] x - π) ≤ c ^ k * l1 (x - π) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hk := distribution_iterate hP hv hc0 hc1 hx k
    have h := l1_vecMul_google_sub (v := v) hP hc0 (hk.2.trans hπ.1.2.symm)
    rw [hπ.2] at h
    calc _ ≤ c * l1 ((iteration c P v)^[k] x - π) := h
      _ ≤ c * (c ^ k * l1 (x - π)) := mul_le_mul_of_nonneg_left ih hc0
      _ = c ^ (k + 1) * l1 (x - π) := by ring

/-- **Th. 5.3** : le critère d'arrêt a posteriori
`‖π⁽ᵏ⁾ - π‖₁ ≤ c/(1-c) ‖π⁽ᵏ⁾ - π⁽ᵏ⁻¹⁾‖₁`. -/
theorem l1_sub_le_a_posteriori (hP : EstStochastique P) (hc0 : 0 ≤ c) (hc1 : c < 1)
    {π y : ι → ℝ} (hπ : EstPageRank (google c P v) π) (hy : EstDistribution y) :
    l1 (y ᵥ* google c P v - π) ≤ c / (1 - c) * l1 (y ᵥ* google c P v - y) := by
  set x := y ᵥ* google c P v
  have h := l1_vecMul_google_sub (v := v) hP hc0 (hy.2.trans hπ.1.2.symm)
  rw [hπ.2] at h
  have ht := l1_sub_le y x π
  rw [l1_sub_comm y x] at ht
  rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
  nlinarith

/-- **Th. 5.1** : toute valeur propre réelle `λ ≠ 1` de `G` vérifie `|λ| ≤ c`. -/
theorem abs_valeur_propre_le (hP : EstStochastique P) (hv : EstDistribution v) (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) {w : ι → ℝ} (hw0 : w ≠ 0) {l : ℝ} (hw : w ᵥ* google c P v = l • w)
    (hl : l ≠ 1) : |l| ≤ c := by
  have hs : ∑ i, w i = 0 := by
    have h := sum_vecMul (stochastique_google hP hv hc0 hc1).2 w
    rw [hw] at h
    simp only [Pi.smul_apply, smul_eq_mul, ← mul_sum] at h
    have : (l - 1) * ∑ i, w i = 0 := by rw [sub_mul, h, one_mul, sub_self]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hl)
  have e : l • w = c • (w ᵥ* P) := by
    rw [← hw, vecMul_google, hs, mul_zero, zero_smul, add_zero]
  have h := congr_arg l1 e
  rw [l1_smul, l1_smul, abs_of_nonneg hc0] at h
  have hpos : 0 < l1 w := lt_of_le_of_ne (l1_nonneg w) fun h0 =>
    hw0 (eq_of_l1_sub_eq_zero (by rw [sub_zero]; exact h0.symm))
  have := mul_le_mul_of_nonneg_left (l1_vecMul_le hP w) hc0
  exact le_of_mul_le_mul_right (h ▸ this) hpos

/-! ## §5.1. Le nombre d'itérations -/

/-- Le tableau du §5.1 : pour chaque `c`, le plus petit `k` tel que `2 cᵏ ≤ 10⁻⁴`. -/
theorem tableau_iterations :
    (2 * (85 / 100 : ℝ) ^ 61 ≤ 1 / 10 ^ 4 ∧ 1 / 10 ^ 4 < 2 * (85 / 100 : ℝ) ^ 60) ∧
    (2 * (86 / 100 : ℝ) ^ 66 ≤ 1 / 10 ^ 4 ∧ 1 / 10 ^ 4 < 2 * (86 / 100 : ℝ) ^ 65) ∧
    (2 * (87 / 100 : ℝ) ^ 72 ≤ 1 / 10 ^ 4 ∧ 1 / 10 ^ 4 < 2 * (87 / 100 : ℝ) ^ 71) ∧
    (2 * (88 / 100 : ℝ) ^ 78 ≤ 1 / 10 ^ 4 ∧ 1 / 10 ^ 4 < 2 * (88 / 100 : ℝ) ^ 77) ∧
    (2 * (89 / 100 : ℝ) ^ 85 ≤ 1 / 10 ^ 4 ∧ 1 / 10 ^ 4 < 2 * (89 / 100 : ℝ) ^ 84) ∧
    (2 * (90 / 100 : ℝ) ^ 94 ≤ 1 / 10 ^ 4 ∧ 1 / 10 ^ 4 < 2 * (90 / 100 : ℝ) ^ 93) := by
  norm_num

/-- Avec `c = 0,85`, `61` itérations garantissent `‖π⁽⁶¹⁾ - π‖₁ ≤ 10⁻⁴`, quel que soit le web. -/
theorem soixante_et_une (hP : EstStochastique P) (hv : EstDistribution v) {π x : ι → ℝ}
    (hπ : EstPageRank (google (85 / 100) P v) π) (hx : EstDistribution x) :
    l1 ((iteration (85 / 100) P v)^[61] x - π) ≤ 1 / 10 ^ 4 :=
  calc _ ≤ (85 / 100 : ℝ) ^ 61 * l1 (x - π) :=
        l1_iterate_sub_le hP hv (by norm_num) (by norm_num) hπ hx 61
    _ ≤ (85 / 100 : ℝ) ^ 61 * 2 :=
        mul_le_mul_of_nonneg_left (l1_sub_le_two hx hπ.1) (by positivity)
    _ ≤ 1 / 10 ^ 4 := by norm_num

/-! ## Ex. 4.5. Le web à quatre pages -/

/-- Les liens de la figure 1 : `1 → 2, 4` ; `3 → 1, 2, 4` ; `4 → 1, 2` (pages numérotées
à partir de `0`). -/
def adj4 : Matrix (Fin 4) (Fin 4) ℕ := !![0, 1, 0, 1; 0, 0, 0, 0; 1, 1, 0, 1; 1, 1, 0, 0]

def lien4 (i j : Fin 4) : Prop := adj4 i j = 1

instance : DecidableRel lien4 := fun i j => inferInstanceAs (Decidable (adj4 i j = 1))

/-- La distribution uniforme sur les quatre pages. -/
def v4 : Fin 4 → ℝ := fun _ => 1 / 4

theorem degre_lien4 :
    degre lien4 0 = 2 ∧ degre lien4 1 = 0 ∧ degre lien4 2 = 3 ∧ degre lien4 3 = 2 := by
  decide

/-- La matrice `P₁` de l'exemple 4.5. -/
theorem matP1_quatre : matP1 lien4 v4 =
    !![0, 1/2, 0, 1/2; 1/4, 1/4, 1/4, 1/4; 1/3, 1/3, 0, 1/3; 1/2, 1/2, 0, 0] := by
  obtain ⟨h0, h1, h2, h3⟩ := degre_lien4
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matP1, liens, pendante, lien4, adj4, v4, vecMulVec_apply, h0, h1, h2, h3]

/-- **Ex. 4.5** : pour `c = 0,85`, le vecteur PageRank vaut exactement
`(3080, 4389, 1380, 3080) / 11929 ≈ (0,258 ; 0,368 ; 0,116 ; 0,258)`. -/
theorem pagerank_quatre :
    EstPageRank (google (85 / 100) (matP1 lien4 v4) v4)
      ![3080 / 11929, 4389 / 11929, 1380 / 11929, 3080 / 11929] := by
  refine ⟨⟨fun i => by fin_cases i <;> norm_num, by simp [Fin.sum_univ_four]; norm_num⟩, ?_⟩
  rw [matP1_quatre]
  funext j
  fin_cases j <;>
    simp [vecMul, dotProduct, google, vecMulVec_apply, v4, Fin.sum_univ_four] <;> norm_num

/-! ## Exercice 2. Une chaîne périodique -/

/-- **Exercice 2** : pour `P = [[0,1],[1,0]]` et `v` uniforme, la méthode de la puissance
issue de `(1, 0)` donne `π⁽ᵏ⁾ = (½, ½) + (-c)ᵏ (½, -½)`. -/
theorem exercice_periodique (c : ℝ) (k : ℕ) :
    (iteration c !![0, 1; 1, 0] ![1 / 2, 1 / 2])^[k] ![1, 0] =
      ![1 / 2 + (-c) ^ k / 2, 1 / 2 - (-c) ^ k / 2] := by
  induction k with
  | zero => funext i; fin_cases i <;> norm_num
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    funext j
    fin_cases j <;>
      simp [vecMul, dotProduct, google, Fin.sum_univ_two] <;> ring

end PageRank

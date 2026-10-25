import Mathlib

/-!
# Hille-Yosida : la limite de la résolvante, et le rôle de la densité

Formalisation d'une partie des sections 2 et 3 de la fiche « Le théorème de Hille-Yosida »
(`hille-yosida.tex`, même dossier), qui suit le chapitre VII de Brezis.

Le fichier tranche une question posée dans un courriel d'étudiant : peut-on démontrer
`J_λ v → v` pour tout `v ∈ H` par un calcul direct, sans passer par la densité de `D(A)`
(Brezis, proposition VII.1 a) ? Réponse :

* le calcul direct est juste sur `D(A)` : `‖J_λ v - v‖ ≤ λ ‖A v‖` (`norm_J_sub_le`) ;
* l'inégalité VII.2 b, `‖A_λ v‖ ≤ ‖A v‖`, découle bien de VII.2 a2 et de `‖J_λ‖ ≤ 1`
  (`yosida_eq`, `norm_yosida_le`) ;
* mais la convergence pour tout `v ∈ H` **entraîne** la densité de `D(A)`
  (`dense_of_tendsto`), puisque `J_λ v` est toujours dans `D(A)` : aucune preuve ne peut
  éviter la densité ;
* la densité est vraie (`dense_domain`, Brezis VII.1 a), et elle donne la convergence pour
  tout `v` (`tendsto_J`, Brezis VII.2 c).

## Modèle

`H` est un espace préhilbertien réel (complet quand c'est nécessaire), `D` un sous-espace et
`A : D →ₗ[ℝ] H` un opérateur linéaire défini sur `D` seulement. Un opérateur maximal monotone
est donné, dans la structure `MaxMono`, par sa monotonie et par une résolvante
`J : ℝ → H → D` qui résout `u + λ A u = f` pour tout `λ > 0`. L'existence de cette résolvante
pour tout `λ > 0` est la proposition VII.1 c de Brezis, démontrée dans la fiche à partir du
cas `λ = 1` par le point fixe de Banach ; on la prend ici comme donnée. Tout le reste
(unicité, linéarité, contraction, densité, limites) est démontré.
-/

open Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace HilleYosida

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Un opérateur maximal monotone `A : D(A) → H`, avec sa résolvante `J s = (I + s A)⁻¹`
pour `s > 0`. -/
structure MaxMono (D : Submodule ℝ H) (A : D →ₗ[ℝ] H) where
  /-- La résolvante, à valeurs dans le domaine. -/
  J : ℝ → H → D
  /-- `J s f` résout l'équation stationnaire `u + s A u = f`. -/
  hJ : ∀ s > 0, ∀ f : H, (J s f : H) + s • A (J s f) = f
  /-- Monotonie : `(A v, v) ≥ 0`. -/
  mono : ∀ v : D, 0 ≤ ⟪A v, (v : H)⟫_ℝ

variable {D : Submodule ℝ H} {A : D →ₗ[ℝ] H} (M : MaxMono D A)

namespace MaxMono

/-- Le produit scalaire de l'équation stationnaire avec sa solution. -/
lemma inner_eq {s : ℝ} (hs : 0 < s) (f : H) :
    ⟪f, (M.J s f : H)⟫_ℝ = ‖(M.J s f : H)‖ ^ 2 + s * ⟪A (M.J s f), (M.J s f : H)⟫_ℝ := by
  have h := M.hJ s hs f
  calc ⟪f, (M.J s f : H)⟫_ℝ
      = ⟪(M.J s f : H) + s • A (M.J s f), (M.J s f : H)⟫_ℝ := by rw [h]
    _ = ‖(M.J s f : H)‖ ^ 2 + s * ⟪A (M.J s f), (M.J s f : H)⟫_ℝ := by
        rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]

/-- **Brezis VII.1 c** : la résolvante est une contraction, `‖J_λ f‖ ≤ ‖f‖`. -/
lemma norm_J_le {s : ℝ} (hs : 0 < s) (f : H) : ‖(M.J s f : H)‖ ≤ ‖f‖ := by
  have h1 := M.inner_eq hs f
  have h2 : 0 ≤ s * ⟪A (M.J s f), (M.J s f : H)⟫_ℝ := mul_nonneg hs.le (M.mono _)
  have h3 : ⟪f, (M.J s f : H)⟫_ℝ ≤ ‖f‖ * ‖(M.J s f : H)‖ := real_inner_le_norm _ _
  have h4 : ‖(M.J s f : H)‖ ^ 2 ≤ ‖f‖ * ‖(M.J s f : H)‖ := by linarith
  rcases (norm_nonneg (M.J s f : H)).eq_or_lt with h | h
  · rw [← h]; exact norm_nonneg f
  · nlinarith

/-- Unicité de la solution de l'équation stationnaire (monotonie). -/
lemma eq_J {s : ℝ} (hs : 0 < s) (u : D) {f : H} (hu : (u : H) + s • A u = f) :
    (u : H) = M.J s f := by
  set w : D := u - M.J s f with hwdef
  have hw : (w : H) + s • A w = 0 := by
    simp only [hwdef, Submodule.coe_sub, map_sub, smul_sub]
    calc (u : H) - (M.J s f : H) + (s • A u - s • A (M.J s f))
        = ((u : H) + s • A u) - ((M.J s f : H) + s • A (M.J s f)) := by abel
      _ = 0 := by rw [hu, M.hJ s hs f, sub_self]
  have h := congrArg (fun x => ⟪x, (w : H)⟫_ℝ) hw
  simp only [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
    inner_zero_left] at h
  have h2 := mul_nonneg hs.le (M.mono w)
  have h3 : ‖(w : H)‖ ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
  have h4 : (w : H) = 0 := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3)
  rw [hwdef, Submodule.coe_sub, sub_eq_zero] at h4
  exact h4

lemma J_add {s : ℝ} (hs : 0 < s) (f g : H) :
    (M.J s (f + g) : H) = M.J s f + M.J s g := by
  symm
  apply M.eq_J hs (M.J s f + M.J s g)
  simp only [Submodule.coe_add, map_add, smul_add]
  calc (M.J s f : H) + M.J s g + (s • A (M.J s f) + s • A (M.J s g))
      = ((M.J s f : H) + s • A (M.J s f)) + ((M.J s g : H) + s • A (M.J s g)) := by abel
    _ = f + g := by rw [M.hJ s hs f, M.hJ s hs g]

lemma J_sub {s : ℝ} (hs : 0 < s) (f g : H) :
    (M.J s (f - g) : H) = M.J s f - M.J s g := by
  symm
  apply M.eq_J hs (M.J s f - M.J s g)
  simp only [Submodule.coe_sub, map_sub, smul_sub]
  calc (M.J s f : H) - M.J s g + (s • A (M.J s f) - s • A (M.J s g))
      = ((M.J s f : H) + s • A (M.J s f)) - ((M.J s g : H) + s • A (M.J s g)) := by abel
    _ = f - g := by rw [M.hJ s hs f, M.hJ s hs g]

lemma J_smul {s : ℝ} (hs : 0 < s) (c : ℝ) (f : H) :
    (M.J s (c • f) : H) = c • (M.J s f : H) := by
  symm
  apply M.eq_J hs (c • M.J s f)
  simp only [Submodule.coe_smul, map_smul]
  calc c • (M.J s f : H) + s • c • A (M.J s f)
      = c • ((M.J s f : H) + s • A (M.J s f)) := by rw [smul_add, smul_comm s c]
    _ = c • f := by rw [M.hJ s hs f]

/-- Sur le domaine : `J_λ v + λ J_λ (A v) = v`, c'est-à-dire `J_λ (I + λ A) v = v`. -/
lemma J_add_smul_J {s : ℝ} (hs : 0 < s) (v : D) :
    (M.J s v : H) + s • (M.J s (A v) : H) = v := by
  have h := (M.eq_J hs v (f := (v : H) + s • A v) rfl).symm
  rwa [M.J_add hs, M.J_smul hs] at h

/-- **Le calcul du courriel, juste sur `D(A)`** : pour `v ∈ D(A)`,
`‖J_λ v - v‖ = λ ‖J_λ (A v)‖ ≤ λ ‖A v‖`. -/
theorem norm_J_sub_le {s : ℝ} (hs : 0 < s) (v : D) :
    ‖(M.J s v : H) - v‖ ≤ s * ‖A v‖ := by
  have h := M.J_add_smul_J hs v
  have e : (M.J s v : H) - v = -(s • (M.J s (A v) : H)) := by
    refine eq_neg_of_add_eq_zero_left ?_
    calc (M.J s v : H) - v + s • (M.J s (A v) : H)
        = ((M.J s v : H) + s • (M.J s (A v) : H)) - v := by abel
      _ = 0 := by rw [h, sub_self]
  rw [e, norm_neg, norm_smul, Real.norm_of_nonneg hs.le]
  exact mul_le_mul_of_nonneg_left (M.norm_J_le hs _) hs.le

/-- **Brezis VII.2 a2** : sur le domaine, la régularisée de Yosida
`A_λ v = (v - J_λ v) / λ` vaut `J_λ (A v)`. -/
theorem yosida_eq {s : ℝ} (hs : 0 < s) (v : D) :
    s⁻¹ • ((v : H) - M.J s v) = M.J s (A v) := by
  have h := M.J_add_smul_J hs v
  have e : (v : H) - M.J s v = s • (M.J s (A v) : H) := by
    calc (v : H) - M.J s v = ((M.J s v : H) + s • (M.J s (A v) : H)) - M.J s v := by rw [h]
      _ = s • (M.J s (A v) : H) := by abel
  rw [e, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]

/-- **Brezis VII.2 b**, comme le dit le courriel : `‖A_λ v‖ ≤ ‖A v‖` découle de VII.2 a2 et de
`‖J_λ‖ ≤ 1`. -/
theorem norm_yosida_le {s : ℝ} (hs : 0 < s) (v : D) :
    ‖s⁻¹ • ((v : H) - M.J s v)‖ ≤ ‖A v‖ := by
  rw [M.yosida_eq hs v]
  exact M.norm_J_le hs _

/-- **Ce qui manque au courriel** : si `J_λ v → v` pour tout `v ∈ H`, alors `D(A)` est dense,
puisque chaque `J_λ v` est dans `D(A)`. La densité ne peut donc pas être évitée. -/
theorem dense_of_tendsto
    (h : ∀ v : H, Tendsto (fun s => (M.J s v : H)) (𝓝[>] 0) (𝓝 v)) :
    Dense (D : Set H) := by
  intro v
  exact mem_closure_of_tendsto (h v) (Eventually.of_forall fun s => (M.J s v).property)

include M in
/-- **Brezis VII.1 a** : le domaine d'un opérateur maximal monotone est dense. -/
theorem dense_domain [CompleteSpace H] : Dense (D : Set H) := by
  have hbot : Dᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro f hf
    have h1 := M.inner_eq one_pos f
    have h0 : ⟪f, (M.J 1 f : H)⟫_ℝ = 0 :=
      Submodule.inner_left_of_mem_orthogonal (M.J 1 f).property hf
    have h2 := M.mono (M.J 1 f)
    have h3 : ‖(M.J 1 f : H)‖ ^ 2 = 0 := le_antisymm (by nlinarith) (sq_nonneg _)
    have h4 : M.J 1 f = 0 :=
      (Submodule.coe_eq_zero).mp (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3))
    have h5 := M.hJ 1 one_pos f
    rw [h4] at h5
    simpa using h5.symm
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr
    (Submodule.topologicalClosure_eq_top_iff.mpr hbot)

/-- **Brezis VII.2 c** : `J_λ v → v` quand `λ → 0⁺`, pour tout `v ∈ H`. La preuve combine le
calcul sur `D(A)` (`norm_J_sub_le`), la contraction (`norm_J_le`) et la densité
(`dense_domain`). -/
theorem tendsto_J [CompleteSpace H] (v : H) :
    Tendsto (fun s => (M.J s v : H)) (𝓝[>] 0) (𝓝 v) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨w, hwD, hw⟩ : ∃ w ∈ (D : Set H), dist v w < ε / 3 :=
    Metric.mem_closure_iff.mp (dense_domain M v) (ε / 3) (by positivity)
  set K : ℝ := ‖A ⟨w, hwD⟩‖ + 1 with hK
  have hK0 : 0 < K := by positivity
  refine ⟨ε / (3 * K), by positivity, fun s hs hsd => ?_⟩
  have hs0 : (0 : ℝ) < s := hs
  have hsK : s * (3 * K) < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hs0] at hsd
    exact (lt_div_iff₀ (by positivity)).mp hsd
  have hstud : ‖(M.J s w : H) - w‖ ≤ s * ‖A ⟨w, hwD⟩‖ := M.norm_J_sub_le hs0 ⟨w, hwD⟩
  have key : (M.J s v : H) - v = (M.J s (v - w) : H) + ((M.J s w : H) - w) + (w - v) := by
    rw [M.J_sub hs0]; abel
  have h1 : ‖v - w‖ < ε / 3 := by rwa [← dist_eq_norm]
  have h2 : ‖w - v‖ < ε / 3 := by rwa [← dist_eq_norm, dist_comm]
  have h3 : s * ‖A ⟨w, hwD⟩‖ < ε / 3 := by
    have : s * ‖A ⟨w, hwD⟩‖ ≤ s * K := mul_le_mul_of_nonneg_left (by linarith) hs0.le
    linarith
  rw [dist_eq_norm, key]
  calc ‖(M.J s (v - w) : H) + ((M.J s w : H) - w) + (w - v)‖
      ≤ ‖(M.J s (v - w) : H)‖ + ‖(M.J s w : H) - w‖ + ‖w - v‖ := norm_add₃_le
    _ ≤ ‖v - w‖ + s * ‖A ⟨w, hwD⟩‖ + ‖w - v‖ := by
        gcongr
        · exact M.norm_J_le hs0 _
    _ < ε / 3 + ε / 3 + ε / 3 := by linarith
    _ = ε := by ring

end MaxMono

end HilleYosida

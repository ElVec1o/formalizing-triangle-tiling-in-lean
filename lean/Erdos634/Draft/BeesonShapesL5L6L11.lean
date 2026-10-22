import Erdos634.Draft.BeesonColoringThm1
import Erdos634.TileAt

/-!
# Beeson (arXiv 1206.2229v4) Lemma 5, Lemma 6, Lemma 11 for a real `CongruentDissection`

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Lemmas 5, 6, 11), Laczkovich (DCG 48 (2012)),
Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.

Project hypothesis, named: (H1) `alpha not in Q * pi` replaces Beeson's Lemma 1 (Laczkovich Thm 5.1, 5.3; not in Lean).
Printed statements and the differences:
* Lemma 5: "3a + 2b = pi implies gamma > pi/2" (gamma = pi - a - b = 2a + b).
* Lemma 6: "no tile has its gamma angle at a vertex of ABC, and there are exactly five tiles with vertices at the
  vertices of ABC" when ABC is not similar to T.  Here: counts of (tile, vertex) INCIDENCES, since the printed
  "five tiles" counts angles (a tile with two vertices at two corners of ABC would be counted twice; the print does
  not address this).  "ABC similar to T" is read as AAA: the angles of ABC are a permutation of (a, b, gamma).
* Lemma 11: the angles of ABC are one of the five triples (up to vertex order), and three alpha and two beta
  angles of tiles occupy the vertices, at least one tile angle at each vertex.
Tile angles at a target vertex are the tiles' `localAngle`s (`Dissection.sum_localAngle_eq`).
-/

open scoped Classical

namespace Erdos634.BeesonColoring

open Erdos634.Geometry

def Triple3 (x y z a b c : ℝ) : Prop :=
  (x = a ∧ y = b ∧ z = c) ∨ (x = a ∧ y = c ∧ z = b) ∨ (x = b ∧ y = a ∧ z = c) ∨
  (x = b ∧ y = c ∧ z = a) ∨ (x = c ∧ y = a ∧ z = b) ∨ (x = c ∧ y = b ∧ z = a)

def FiveShapes (x y z α β : ℝ) : Prop :=
  Triple3 x y z α (α + 2 * β) α ∨ Triple3 x y z β (3 * α) β ∨
  Triple3 x y z (α + β) α (α + β) ∨ Triple3 x y z (2 * α) β (α + β) ∨
  Triple3 x y z (2 * α) α (2 * β)

theorem three_shapes_arith {α β θ0 θ1 θ2 : ℝ} (a0 a1 a2 b0 b1 b2 : ℕ)
    (h0 : θ0 = a0 * α + b0 * β) (h1 : θ1 = a1 * α + b1 * β) (h2 : θ2 = a2 * α + b2 * β)
    (hP : a0 + a1 + a2 = 3) (hQ : b0 + b1 + b2 = 2)
    (n0 : 1 ≤ a0 + b0) (n1 : 1 ≤ a1 + b1) (n2 : 1 ≤ a2 + b2) :
    Triple3 θ0 θ1 θ2 α β (2 * α + β) ∨ FiveShapes θ0 θ1 θ2 α β := by
  have ha2 : a2 = 3 - a0 - a1 := by omega
  have hb2 : b2 = 2 - b0 - b1 := by omega
  have a0le : a0 ≤ 3 := by omega
  have a1le : a1 ≤ 3 := by omega
  have b0le : b0 ≤ 2 := by omega
  have b1le : b1 ≤ 2 := by omega
  subst ha2 hb2 h0 h1 h2
  interval_cases a0 <;> interval_cases a1 <;> interval_cases b0 <;> interval_cases b1 <;>
    first | (exfalso; omega) | simp [Triple3, FiveShapes]

theorem one_each_arith {α β γ θ0 θ1 θ2 : ℝ} (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℕ)
    (h0 : θ0 = a0 * α + b0 * β + c0 * γ) (h1 : θ1 = a1 * α + b1 * β + c1 * γ)
    (h2 : θ2 = a2 * α + b2 * β + c2 * γ)
    (hP : a0 + a1 + a2 = 1) (hQ : b0 + b1 + b2 = 1) (hR : c0 + c1 + c2 = 1)
    (n0 : 1 ≤ a0 + b0 + c0) (n1 : 1 ≤ a1 + b1 + c1) (n2 : 1 ≤ a2 + b2 + c2) :
    Triple3 θ0 θ1 θ2 α β γ := by
  have : a0 ≤ 1 := by omega
  have : a1 ≤ 1 := by omega
  have : b0 ≤ 1 := by omega
  have : b1 ≤ 1 := by omega
  have : c0 ≤ 1 := by omega
  have : c1 ≤ 1 := by omega
  have ha2 : a2 = 1 - a0 - a1 := by omega
  have hb2 : b2 = 1 - b0 - b1 := by omega
  have hc2 : c2 = 1 - c0 - c1 := by omega
  subst ha2 hb2 hc2 h0 h1 h2
  interval_cases a0 <;> interval_cases a1 <;> interval_cases b0 <;> interval_cases b1 <;>
    interval_cases c0 <;> interval_cases c1 <;>
    first | (exfalso; omega) | simp [Triple3]

/-- **Beeson Lemma 5.**  `3 alpha + 2 beta = pi`, `alpha > 0`, `gamma = pi - alpha - beta` give
`gamma = 2 alpha + beta` and `gamma > pi/2`.  (Printed proof: `2 gamma = pi + alpha`.) -/
theorem lemma5 {α β γ : ℝ} (hα : 0 < α) (hrel : 3 * α + 2 * β = Real.pi)
    (hγ : γ = Real.pi - α - β) : γ = 2 * α + β ∧ Real.pi / 2 < γ := by
  constructor <;> linarith

/-- The tile's corner counts at target vertex `k`. -/
noncomputable def vcount {N : ℕ} (D : CongruentDissection N) (k : Fin 3) (x : ℝ) : ℕ :=
  ({i | (D.tile i).localAngle (D.target.pts k) = x} : Finset (Fin N)).card

/-- Every tile's local angle at a target vertex is `alpha`, `beta`, `gamma = 2 alpha + beta`, `pi` or `0`,
for the model with angles `(alpha, beta, 2 alpha + beta)` in some vertex order. -/
theorem localAngle_mem_3a {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (h : D.model.ThreeAlphaData α β a b c) (k : Fin 3) (i : Fin N) :
    (D.tile i).localAngle (D.target.pts k) ∈ ({α, β, 2 * α + β, Real.pi, 0} : Finset ℝ) := by
  obtain ⟨σ, h0, -, h1, -, h2, -⟩ := h
  have key : ∀ (σ : Equiv.Perm (Fin 3)) (i : Fin 3),
      (σ (i + 1) = σ i + 1 ∧ σ (i + 2) = σ i + 2) ∨ (σ (i + 1) = σ i + 2 ∧ σ (i + 2) = σ i + 1) := by
    decide
  have rel : ∀ i : Fin 3, cornerAngle ((D.model.relabel σ).pts (i + 1)) ((D.model.relabel σ).pts i)
      ((D.model.relabel σ).pts (i + 2)) = D.model.angleAt (σ i) := by
    intro i
    show cornerAngle (D.model.pts (σ (i + 1))) (D.model.pts (σ i)) (D.model.pts (σ (i + 2))) = _
    rcases key σ i with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2]; rfl
    · rw [e1, e2]; unfold Tri.angleAt
      exact EuclideanGeometry.angle_comm _ _ _
  exact Erdos634.Geometry.Dissection.congruentDissection_localAngle_mem (D.relabelModel σ) α β (2 * α + β)
    ((rel 0).trans h0) ((rel 1).trans h1) ((rel 2).trans h2) k i

/-- **Corner figure at every target vertex** (general target shape; `H1`).  At vertex `k`, with
`a_k, b_k, c_k` the numbers of tile angles `alpha, beta, gamma` there: no straight angle, and
`a_k alpha + b_k beta + c_k gamma` is the target's angle at `k`. -/
theorem corner_fig {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) (k : Fin 3) :
    vcount D k Real.pi = 0 ∧
    (vcount D k α : ℝ) * α + (vcount D k β : ℝ) * β + (vcount D k (2 * α + β) : ℝ) * (2 * α + β)
      = D.target.angleAt k := by
  obtain ⟨ha, hb, -, hαpos, hβpos⟩ := model_abc_pos h
  have hαβ : α ≠ β := fun e => hirr ⟨1 / 5, by push_cast; linarith⟩
  have hαπ : α ≠ Real.pi := by intro e; linarith
  have hβπ : β ≠ Real.pi := by intro e; linarith
  have hπ0 : Real.pi ≠ 0 := Real.pi_ne_zero
  have hm := Erdos634.TilePlacement.corner_multiplicities D.toDissection α β (2 * α + β) hαβ
    (by intro e; linarith) hαπ hαpos.ne' (by intro e; linarith) hβπ hβpos.ne'
    (by intro e; linarith) (by intro e; linarith) hπ0 k (fun i => localAngle_mem_3a D h k i)
  have hpos := D.target.angleAt_pos' k
  have hsum := D.target.angleAt_sum
  have hlt : D.target.angleAt k < Real.pi := by
    have := D.target.angleAt_pos' 0
    have := D.target.angleAt_pos' 1
    have := D.target.angleAt_pos' 2
    fin_cases k <;> simp <;> linarith
  have hpi : vcount D k Real.pi = 0 := by
    by_contra hne
    have h1 : (1 : ℝ) ≤ (vcount D k Real.pi : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
    have hp : (vcount D k Real.pi : ℝ) * Real.pi ≥ Real.pi := by nlinarith [Real.pi_pos]
    have := mul_nonneg (Nat.cast_nonneg (vcount D k α) : (0:ℝ) ≤ _) hαpos.le
    have := mul_nonneg (Nat.cast_nonneg (vcount D k β) : (0:ℝ) ≤ _) hβpos.le
    have := mul_nonneg (Nat.cast_nonneg (vcount D k (2 * α + β)) : (0:ℝ) ≤ _) (by linarith : (0:ℝ) ≤ 2 * α + β)
    unfold vcount at *
    change _ = D.target.angleAt k at hm
    linarith
  refine ⟨hpi, ?_⟩
  unfold vcount at hpi ⊢
  have := hm
  rw [hpi] at this
  change _ = D.target.angleAt k at this
  simpa using this

/-- Totals of the counts over the three target vertices: `P + 2J = 3`, `Q + J = 2` (`H1`). -/
theorem corner_totals {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) :
    (∑ k, vcount D k α) + 2 * (∑ k, vcount D k (2 * α + β)) = 3 ∧
    (∑ k, vcount D k β) + (∑ k, vcount D k (2 * α + β)) = 2 := by
  have e0 := corner_fig D hirr hrel h 0
  have e1 := corner_fig D hirr hrel h 1
  have e2 := corner_fig D hirr hrel h 2
  have hsum := D.target.angleAt_sum
  have hx : ((∑ k, vcount D k α : ℕ) : ℝ) * α + ((∑ k, vcount D k β : ℕ) : ℝ) * β
      + ((∑ k, vcount D k (2 * α + β) : ℕ) : ℝ) * (2 * α + β)
      = ((3 : ℤ) : ℝ) * α + ((2 : ℤ) : ℝ) * β := by
    simp only [Fin.sum_univ_three]
    push_cast
    linarith [e0.2, e1.2, e2.2]
  obtain ⟨u, v⟩ := vertex_multiplicities hrel hirr _ _ _ 3 2 hx
  constructor <;> omega

/-- **Beeson Lemma 6** (`H1`, printed gap: incidences).  Either the angles of ABC are a permutation of
`(alpha, beta, gamma)` (ABC similar to T), or no tile has its gamma angle at a vertex of ABC, and the
vertices carry exactly three tile angles `alpha` and two `beta` (five tile-vertex incidences). -/
theorem lemma6 {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) :
    Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β) ∨
    ((∀ k, vcount D k (2 * α + β) = 0) ∧ (∑ k, vcount D k α) = 3 ∧ (∑ k, vcount D k β) = 2 ∧
      (∑ k, (vcount D k α + vcount D k β)) = 5) := by
  obtain ⟨hP, hQ⟩ := corner_totals D hirr hrel h
  by_cases hJ : (∑ k, vcount D k (2 * α + β)) = 0
  · right
    have hz : ∀ k, vcount D k (2 * α + β) = 0 := fun k => by
      have := Finset.sum_eq_zero_iff.mp hJ k (Finset.mem_univ k)
      exact this
    refine ⟨hz, by omega, by omega, ?_⟩
    rw [Finset.sum_add_distrib]; omega
  · left
    have hJ1 : (∑ k, vcount D k (2 * α + β)) = 1 := by omega
    have e0 := corner_fig D hirr hrel h 0
    have e1 := corner_fig D hirr hrel h 1
    have e2 := corner_fig D hirr hrel h 2
    obtain ⟨ha, hb, -, hαpos, hβpos⟩ := model_abc_pos h
    have npos : ∀ k : Fin 3, 1 ≤ vcount D k α + vcount D k β + vcount D k (2 * α + β) := by
      intro k
      by_contra hn
      have h0 : vcount D k α = 0 := by omega
      have h1 : vcount D k β = 0 := by omega
      have h2 : vcount D k (2 * α + β) = 0 := by omega
      have := (corner_fig D hirr hrel h k).2
      rw [h0, h1, h2] at this
      have := D.target.angleAt_pos' k
      simp_all
    simp only [Fin.sum_univ_three] at hP hQ hJ1
    exact one_each_arith _ _ _ _ _ _ _ _ _ e0.2.symm e1.2.symm e2.2.symm (by omega) (by omega) hJ1
      (npos 0) (npos 1) (npos 2)

/-- **Beeson Lemma 11** (`H1`).  If the angles of ABC are not a permutation of `(alpha, beta, gamma)`
(ABC not similar to T), they are one of the five triples, up to vertex order
`(a, a+2b, a)`, `(b, 3a, b)`, `(a+b, a, a+b)`, `(2a, b, a+b)`, `(2a, a, 2b)`, and the vertices carry exactly
three tile angles `alpha` and two `beta`, at least one at each vertex, and no `gamma`. -/
theorem lemma11 {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β)) :
    FiveShapes (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β ∧
    (∑ k, vcount D k α) = 3 ∧ (∑ k, vcount D k β) = 2 ∧ (∀ k, vcount D k (2 * α + β) = 0) ∧
    (∀ k, 1 ≤ vcount D k α + vcount D k β) := by
  rcases lemma6 D hirr hrel h with hs | ⟨hz, hP, hQ, -⟩
  · exact absurd hs hns
  · have e0 := corner_fig D hirr hrel h 0
    have e1 := corner_fig D hirr hrel h 1
    have e2 := corner_fig D hirr hrel h 2
    have npos : ∀ k : Fin 3, 1 ≤ vcount D k α + vcount D k β := by
      intro k
      by_contra hn
      have h0 : vcount D k α = 0 := by omega
      have h1 : vcount D k β = 0 := by omega
      have := (corner_fig D hirr hrel h k).2
      rw [h0, h1, hz k] at this
      have := D.target.angleAt_pos' k
      simp_all
    simp only [Fin.sum_univ_three] at hP hQ
    have f0 := e0.2; have f1 := e1.2; have f2 := e2.2
    rw [hz 0] at f0; rw [hz 1] at f1; rw [hz 2] at f2
    have := three_shapes_arith _ _ _ _ _ _ (by simpa using f0.symm) (by simpa using f1.symm)
      (by simpa using f2.symm) hP hQ (npos 0) (npos 1) (npos 2)
    refine ⟨?_, by simpa [Fin.sum_univ_three] using hP, by simpa [Fin.sum_univ_three] using hQ, hz, npos⟩
    rcases this with h6 | h5
    · exact absurd h6 hns
    · exact h5

end Erdos634.BeesonColoring

#print axioms Erdos634.BeesonColoring.lemma5
#print axioms Erdos634.BeesonColoring.lemma6
#print axioms Erdos634.BeesonColoring.lemma11

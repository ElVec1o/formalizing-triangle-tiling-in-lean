import Erdos634.CornerAnglePermCensus
import Erdos634.Draft.BeesonShapesL5L6L11

/-!
# Beeson (arXiv 1206.2229v4) Lemma 10 (vertex types; centre count `NC = 1 + N1 + 2 N2 + N3`)

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Lemma 10), Laczkovich (DCG 48 (2012)), Beeson-Zhang.
Formalization debt, not progress on the /goal outcomes.

Printed Lemma 10 (`3 alpha + 2 beta = pi`, ABC not similar to T): (ii) every vertex other than A, B, C has one of the
types `(3,2,0)`, `(1,1,1)`, `(2,2,2)`, `(6,4,0)`, `(4,3,1)`, `(0,1,3)` (numbers of tile angles `alpha, beta, gamma`);
(i) `NC = 1 + N1 + 2 N2 + N3`, `NC` = number of `(0,1,3)` vertices ("centers"), `N1, N2, N3` those of type `(3,2,0)`,
`(6,4,0)`, `(4,3,1)`.  Here "vertex" is a point of `cornerPts` (a vertex of some tile); the type of a point is
`vecAt`.  This is the general-shape version of the base-beta census `congruentDissection_vertex_census`
(`CornerAnglePermCensus`), which assumed the target shape (beta, beta, 3 alpha); the proof is the printed excess count:
`sum_v (n_alpha - n_gamma) = N - N = 0` (`congruentDissection_corner_balance`), with the three ABC vertices contributing
`3` (`lemma11`) and each other vertex `3,0,0,6,3,-3` by type.
Project hypothesis (H1) `alpha not in Q * pi` replaces Beeson's Lemma 1 (Laczkovich 5.1, 5.3; not in Lean).
-/

open scoped Classical

namespace Erdos634.BeesonColoring

open Erdos634.Geometry

theorem count_arg {X : Type*} (C T : Finset X) (hT : T ⊆ C) (vec : X → ℕ × ℕ × ℕ) (N : ℕ)
    (hα : ∑ v ∈ C, (vec v).1 = N) (hγ : ∑ v ∈ C, (vec v).2.2 = N)
    (hcor : ∑ v ∈ T, (((vec v).1 : ℤ) - ((vec v).2.2 : ℤ)) = 3)
    (hTn : ∀ v ∈ T, vec v ≠ (3, 2, 0) ∧ vec v ≠ (6, 4, 0) ∧ vec v ≠ (4, 3, 1) ∧ vec v ≠ (0, 1, 3))
    (hty : ∀ v ∈ C, v ∉ T → vec v = (3, 2, 0) ∨ vec v = (1, 1, 1) ∨ vec v = (2, 2, 2) ∨
      vec v = (6, 4, 0) ∨ vec v = (4, 3, 1) ∨ vec v = (0, 1, 3)) :
    (C.filter (fun v => vec v = (0, 1, 3))).card
      = 1 + (C.filter (fun v => vec v = (3, 2, 0))).card
        + 2 * (C.filter (fun v => vec v = (6, 4, 0))).card
        + (C.filter (fun v => vec v = (4, 3, 1))).card := by
  set w : X → ℤ := fun v => ((vec v).1 : ℤ) - ((vec v).2.2 : ℤ)
    - 3 * (if vec v = (3, 2, 0) then 1 else 0) - 6 * (if vec v = (6, 4, 0) then 1 else 0)
    - 3 * (if vec v = (4, 3, 1) then 1 else 0) + 3 * (if vec v = (0, 1, 3) then 1 else 0) with hw
  have h1 : ∑ v ∈ C, w v = ∑ v ∈ T, w v := by
    symm
    apply Finset.sum_subset hT
    intro v hv hvT
    rcases hty v hv hvT with h | h | h | h | h | h <;> simp [hw, h]
  have h2 : ∑ v ∈ T, w v = 3 := by
    rw [← hcor]
    apply Finset.sum_congr rfl
    intro v hv
    obtain ⟨a, b, c, d⟩ := hTn v hv
    simp [hw, a, b, c, d]
  have h3 : ∑ v ∈ C, w v = ((N : ℤ) - N) - 3 * ((C.filter (fun v => vec v = (3, 2, 0))).card : ℤ)
      - 6 * ((C.filter (fun v => vec v = (6, 4, 0))).card : ℤ)
      - 3 * ((C.filter (fun v => vec v = (4, 3, 1))).card : ℤ)
      + 3 * ((C.filter (fun v => vec v = (0, 1, 3))).card : ℤ) := by
    have e1 : ∑ v ∈ C, ((vec v).1 : ℤ) = N := by exact_mod_cast hα
    have e2 : ∑ v ∈ C, ((vec v).2.2 : ℤ) = N := by exact_mod_cast hγ
    simp only [hw, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_boole, e1, e2]
  have : ((C.filter (fun v => vec v = (0, 1, 3))).card : ℤ)
      = 1 + (C.filter (fun v => vec v = (3, 2, 0))).card
        + 2 * (C.filter (fun v => vec v = (6, 4, 0))).card
        + (C.filter (fun v => vec v = (4, 3, 1))).card := by linarith
  exact_mod_cast this

/-- The type `(n_alpha, n_beta, n_gamma)` of a point: numbers of tiles presenting `alpha`, `beta`, `gamma = 2 alpha + beta`. -/
noncomputable def vecAt {N : ℕ} (D : CongruentDissection N) (α β : ℝ) (v : Plane) : ℕ × ℕ × ℕ :=
  (({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
   ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
   ({i | (D.tile i).localAngle v = 2 * α + β} : Finset (Fin N)).card)

/-- Relabelling the model so that its corner angles at `0, 1, 2` are `alpha, beta, gamma`. -/
theorem relabelled {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (h : D.model.ThreeAlphaData α β a b c) :
    ∃ σ : Equiv.Perm (Fin 3),
      cornerAngle ((D.relabelModel σ).model.pts 1) ((D.relabelModel σ).model.pts 0)
        ((D.relabelModel σ).model.pts 2) = α ∧
      cornerAngle ((D.relabelModel σ).model.pts 2) ((D.relabelModel σ).model.pts 1)
        ((D.relabelModel σ).model.pts 0) = β ∧
      cornerAngle ((D.relabelModel σ).model.pts 0) ((D.relabelModel σ).model.pts 2)
        ((D.relabelModel σ).model.pts 1) = 2 * α + β := by
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
  exact ⟨σ, (rel 0).trans h0, (rel 1).trans h1, (rel 2).trans h2⟩

set_option maxHeartbeats 1000000 in
/-- **Beeson Lemma 10** (UNAUDITED; (H1); ABC not similar to T, as `lemma11`).
(ii) every tile vertex other than A, B, C has one of the six types; (i) the centre count identity. -/
theorem lemma10 {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β)) :
    (∀ v ∈ cornerPts D.toDissection, v ∉ Set.range D.target.pts →
      vecAt D α β v = (3, 2, 0) ∨ vecAt D α β v = (1, 1, 1) ∨ vecAt D α β v = (2, 2, 2) ∨
      vecAt D α β v = (6, 4, 0) ∨ vecAt D α β v = (4, 3, 1) ∨ vecAt D α β v = (0, 1, 3)) ∧
    ((cornerPts D.toDissection).filter (fun v => vecAt D α β v = (0, 1, 3))).card
      = 1 + ((cornerPts D.toDissection).filter (fun v => vecAt D α β v = (3, 2, 0))).card
        + 2 * ((cornerPts D.toDissection).filter (fun v => vecAt D α β v = (6, 4, 0))).card
        + ((cornerPts D.toDissection).filter (fun v => vecAt D α β v = (4, 3, 1))).card := by
  obtain ⟨ha, hb, -, hαpos, hβpos⟩ := model_abc_pos h
  obtain ⟨hl11a, hP, hQ, hz, hnp⟩ := lemma11 D hirr hrel h hns
  obtain ⟨σ, hmα, hmβ, hmγ⟩ := relabelled D h
  set D' := D.relabelModel σ with hD'
  have hπ := Real.pi_pos
  have hαβ : α ≠ β := fun e => hirr ⟨1 / 5, by push_cast; linarith⟩
  have hαγ : α ≠ 2 * α + β := by intro e; linarith
  have hαπ : α ≠ Real.pi := by intro e; linarith
  have hα2π : α ≠ 2 * Real.pi := by intro e; linarith
  have hα0 : α ≠ 0 := hαpos.ne'
  have hβγ : β ≠ 2 * α + β := by intro e; linarith
  have hβπ : β ≠ Real.pi := by intro e; linarith
  have hβ2π : β ≠ 2 * Real.pi := by intro e; linarith
  have hβ0 : β ≠ 0 := hβpos.ne'
  have hγπ : 2 * α + β ≠ Real.pi := by intro e; linarith
  have hγ2π : 2 * α + β ≠ 2 * Real.pi := by intro e; linarith
  have hγ0 : 2 * α + β ≠ 0 := by intro e; linarith
  have hπ2π : Real.pi ≠ 2 * Real.pi := by intro e; linarith
  have hπ0 : Real.pi ≠ 0 := hπ.ne'
  have h2π0 : 2 * Real.pi ≠ 0 := by intro e; linarith
  -- (ii)
  have hty : ∀ v ∈ cornerPts D.toDissection, v ∉ Set.range D.target.pts →
      vecAt D α β v = (3, 2, 0) ∨ vecAt D α β v = (1, 1, 1) ∨ vecAt D α β v = (2, 2, 2) ∨
      vecAt D α β v = (6, 4, 0) ∨ vecAt D α β v = (4, 3, 1) ∨ vecAt D α β v = (0, 1, 3) := by
    intro v hv hnr
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨m, -, hm⟩ := Finset.mem_image.mp hj
    rcases cornerPts_trichotomy D.toDissection hv with hc | ⟨hfr, hnv⟩ | hint
    · exact absurd hc hnr
    · rcases congruentDissection_boundary_figure_at_corner D' α β (2 * α + β) hαβ hαγ hαπ hα0
        hβγ hβπ hβ0 hγπ hγ0 hπ0 rfl hrel hirr hmα hmβ hmγ hfr hnv j m hm with
        ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩
      · left; exact Prod.ext e1 (Prod.ext e2 e3)
      · right; left; exact Prod.ext e1 (Prod.ext e2 e3)
    · rcases congruentDissection_interior_figure_at_corner D' α β (2 * α + β) hαβ hαγ hαπ hα2π
        hα0 hβγ hβπ hβ2π hβ0 hγπ hγ2π hγ0 hπ2π hπ0 h2π0 hmα hmβ hmγ rfl hrel hirr hint j m hm with
        ⟨-, ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩⟩ | ⟨-, ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩⟩
      · left; exact Prod.ext e1 (Prod.ext e2 e3)
      · right; left; exact Prod.ext e1 (Prod.ext e2 e3)
      · right; right; right; left; exact Prod.ext e1 (Prod.ext e2 e3)
      · right; right; right; right; left; exact Prod.ext e1 (Prod.ext e2 e3)
      · right; right; left; exact Prod.ext e1 (Prod.ext e2 e3)
      · right; right; right; right; right; exact Prod.ext e1 (Prod.ext e2 e3)
  refine ⟨hty, ?_⟩
  -- (i)
  have hdist := model_corner_dist D' hmα hmβ hmγ hαβ hαγ hβγ
  have hbalα := congruentDissection_corner_balance D' hdist 0
    (by rw [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl, hmα]; exact hα0)
    (by rw [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl, hmα]; exact hαπ)
    (by rw [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl, hmα]; exact hα2π)
  rw [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl, hmα] at hbalα
  have hbalγ := congruentDissection_corner_balance D' hdist 2
    (by rw [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl, hmγ]; exact hγ0)
    (by rw [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl, hmγ]; exact hγπ)
    (by rw [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl, hmγ]; exact hγ2π)
  rw [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl, hmγ] at hbalγ
  -- the corners of ABC are tile vertices
  have hmem : ∀ k : Fin 3, D.target.pts k ∈ cornerPts D.toDissection := by
    intro k
    rcases Nat.eq_zero_or_pos (vcount D k α) with h0 | h0
    · have h1 : 0 < vcount D k β := by have := hnp k; omega
      obtain ⟨i, hi⟩ := Finset.card_pos.mp h1
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      obtain ⟨m, hm⟩ := vertex_of_localAngle_corner (D.tile i) hi hβ0 hβπ hβ2π
      rw [← hm]; exact mem_cornerPts D.toDissection i m
    · obtain ⟨i, hi⟩ := Finset.card_pos.mp h0
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      obtain ⟨m, hm⟩ := vertex_of_localAngle_corner (D.tile i) hi hα0 hαπ hα2π
      rw [← hm]; exact mem_cornerPts D.toDissection i m
  have hinj := D.target.indep.injective
  have hc : ∀ k, vecAt D α β (D.target.pts k)
      = (vcount D k α, vcount D k β, vcount D k (2 * α + β)) := fun k => rfl
  have hP' := hP
  have hQ' := hQ
  simp only [Fin.sum_univ_three] at hP' hQ'
  have hz0 := hz 0
  have hz1 := hz 1
  have hz2 := hz 2
  have hn0 := hnp 0
  have hn1 := hnp 1
  have hn2 := hnp 2
  refine count_arg (cornerPts D.toDissection) (Finset.univ.image D.target.pts) ?_ (vecAt D α β) N
    hbalα hbalγ ?_ ?_
    (fun v hv hn => hty v hv (fun ⟨k, hk⟩ => hn (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩)))
  · intro v hv
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hv
    exact hmem k
  · rw [Finset.sum_image (fun x _ y _ hxy => hinj hxy)]
    simp only [Fin.sum_univ_three, hc]
    simp only [hz0, hz1, hz2]
    push_cast
    have : ((vcount D 0 α : ℕ) : ℤ) + vcount D 1 α + vcount D 2 α = 3 := by exact_mod_cast hP'
    linarith
  · intro v hv
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hv
    have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
    rw [hc]
    rcases hk with rfl | rfl | rfl <;> simp only [ne_eq, Prod.mk.injEq] <;> omega

end Erdos634.BeesonColoring

#print axioms Erdos634.BeesonColoring.lemma10

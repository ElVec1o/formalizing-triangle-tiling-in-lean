-- Draft/H1gDir.lean — ATOM H1.g(dir) (SCOPE_L1_plan.md): the DIRECTION half of L1, from NG.
--
--   Hypotheses: a CongruentDissection `D`, a subfield `K ⊆ ℝ` containing every model distance and
--   `|det model|`, and ONE tile edge vector with both coordinates in `K` (e.g. an edge on a
--   target side lying on the x-axis).
--   Conclusion: EVERY edge vector of EVERY tile has both coordinates in `K`.
--
-- Route (replaces the paper's "one coset of Zα+Zπ/2" by a cleaner field argument that needs no
-- angles and no irrationality):  (A) inside a tile, `e_{k+1} = (dot/|e|²) e_k + (det/|e|²) rot e_k`
-- with `dot,|e|²,det ∈ K`;  (B) across a shared line, `e_i = r • e_j` with `r = ± length ratio ∈ K`;
-- (C) NG connectivity (`H1fNG.nbrGraph_connected`, `adj_edges_parallel`) propagates.
-- Formalization debt; NOT /goal progress.  Standard axioms, no sorry.
import Erdos634.Draft.H1fNGEdge
import Erdos634.Draft.H1hCTCong
import Erdos634.TilePlacement

open MeasureTheory Set

namespace Erdos634.H1gDir

open Erdos634.Geometry Erdos634.H1fNG

/-- Edge vector of the `k`-th edge. -/
def edgeVec (T : Tri) (k : Fin 3) : Plane := T.pts (k + 1) - T.pts k

/-- Both coordinates in `K`. -/
def InK (K : Subfield ℝ) (v : Plane) : Prop := v 0 ∈ K ∧ v 1 ∈ K

theorem sqd (p q : Plane) : dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 :=
  Erdos634.H1hCT.dist_sq_plane p q

/-- **(A), pointwise form.**  Three points with all three distances and the cross product
`cross(q-p, r-q)` in `K`, `p ≠ q`: the edge `q-p` having coordinates in `K` forces `r-q` to. -/
theorem step_in_K (K : Subfield ℝ) {p q r : Plane} (hpq : p ≠ q)
    (d1 : dist p q ∈ K) (d2 : dist q r ∈ K) (d3 : dist r p ∈ K)
    (hδ : cross (q - p) (r - q) ∈ K) (hu : InK K (q - p)) : InK K (r - q) := by
  obtain ⟨hu0, hu1⟩ := hu
  simp only [PiLp.sub_apply] at hu0 hu1
  have e1 : (q 0 - p 0) ^ 2 + (q 1 - p 1) ^ 2 ∈ K := by
    have := K.pow_mem d1 2
    rw [sqd] at this
    have h : (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 = (q 0 - p 0) ^ 2 + (q 1 - p 1) ^ 2 := by ring
    rwa [h] at this
  have e2 : (r 0 - q 0) ^ 2 + (r 1 - q 1) ^ 2 ∈ K := by
    have := K.pow_mem d2 2
    rw [sqd] at this
    have h : (q 0 - r 0) ^ 2 + (q 1 - r 1) ^ 2 = (r 0 - q 0) ^ 2 + (r 1 - q 1) ^ 2 := by ring
    rwa [h] at this
  have e3 : (r 0 - p 0) ^ 2 + (r 1 - p 1) ^ 2 ∈ K := by
    have := K.pow_mem d3 2
    rw [sqd] at this
    have h : (r 0 - p 0) ^ 2 + (r 1 - p 1) ^ 2 = (r 0 - p 0) ^ 2 + (r 1 - p 1) ^ 2 := rfl
    rwa [h] at this
  -- dot product
  have hdot : (q 0 - p 0) * (r 0 - q 0) + (q 1 - p 1) * (r 1 - q 1) ∈ K := by
    have h : (q 0 - p 0) * (r 0 - q 0) + (q 1 - p 1) * (r 1 - q 1) =
        ((r 0 - p 0) ^ 2 + (r 1 - p 1) ^ 2 - ((q 0 - p 0) ^ 2 + (q 1 - p 1) ^ 2)
          - ((r 0 - q 0) ^ 2 + (r 1 - q 1) ^ 2)) / 2 := by ring
    rw [h]
    exact K.div_mem (K.sub_mem (K.sub_mem e3 e1) e2) (by simpa [one_add_one_eq_two] using K.add_mem K.one_mem K.one_mem)
  have hs : (q 0 - p 0) ^ 2 + (q 1 - p 1) ^ 2 ≠ 0 := by
    intro h0
    apply hpq
    have h1 : q 0 - p 0 = 0 := by nlinarith [sq_nonneg (q 0 - p 0), sq_nonneg (q 1 - p 1)]
    have h2 : q 1 - p 1 = 0 := by nlinarith [sq_nonneg (q 0 - p 0), sq_nonneg (q 1 - p 1)]
    ext i; fin_cases i
    · simp only [sub_eq_zero] at h1; exact h1.symm
    · simp only [sub_eq_zero] at h2; exact h2.symm
  simp only [cross, PiLp.sub_apply] at hδ
  refine ⟨?_, ?_⟩
  · have h : r 0 - q 0 = (((q 0 - p 0) * (r 0 - q 0) + (q 1 - p 1) * (r 1 - q 1)) * (q 0 - p 0)
        - ((q 0 - p 0) * (r 1 - q 1) - (q 1 - p 1) * (r 0 - q 0)) * (q 1 - p 1)) /
        ((q 0 - p 0) ^ 2 + (q 1 - p 1) ^ 2) := by
      field_simp; ring
    simp only [PiLp.sub_apply]
    rw [h]
    exact K.div_mem (K.sub_mem (K.mul_mem hdot hu0) (K.mul_mem hδ hu1)) e1
  · have h : r 1 - q 1 = (((q 0 - p 0) * (r 0 - q 0) + (q 1 - p 1) * (r 1 - q 1)) * (q 1 - p 1)
        + ((q 0 - p 0) * (r 1 - q 1) - (q 1 - p 1) * (r 0 - q 0)) * (q 0 - p 0)) /
        ((q 0 - p 0) ^ 2 + (q 1 - p 1) ^ 2) := by
      field_simp; ring
    simp only [PiLp.sub_apply]
    rw [h]
    exact K.div_mem (K.add_mem (K.mul_mem hdot hu1) (K.mul_mem hδ hu0)) e1

theorem cross_edges (T : Tri) (k : Fin 3) :
    cross (T.pts (k + 1) - T.pts k) (T.pts (k + 1 + 1) - T.pts (k + 1)) = T.det := by
  fin_cases k <;> simp [cross, Tri.det] <;> ring

theorem step_tile (K : Subfield ℝ) (T : Tri) (hd : ∀ k l, dist (T.pts k) (T.pts l) ∈ K)
    (hdet : T.det ∈ K) {k : Fin 3} (hk : InK K (edgeVec T k)) : InK K (edgeVec T (k + 1)) := by
  have hne : T.pts k ≠ T.pts (k + 1) :=
    Erdos634.TilePlacement.pts_ne T (by fin_cases k <;> decide)
  have h := step_in_K K (p := T.pts k) (q := T.pts (k + 1)) (r := T.pts (k + 1 + 1)) hne
    (hd _ _) (hd _ _) (hd _ _) (by rw [cross_edges]; exact hdet) hk
  exact h

/-- **(A)** one edge vector of a tile in `K²` ⟹ all three. -/
theorem tile_all_in_K (K : Subfield ℝ) (T : Tri) (hd : ∀ k l, dist (T.pts k) (T.pts l) ∈ K)
    (hdet : T.det ∈ K) {k : Fin 3} (hk : InK K (edgeVec T k)) : ∀ k', InK K (edgeVec T k') := by
  have h1 := step_tile K T hd hdet hk
  have h2 := step_tile K T hd hdet h1
  intro k'
  fin_cases k <;> fin_cases k' <;> simpa [edgeVec] using (by assumption : InK K _) <;> first
    | exact hk | exact h1 | exact h2

/-- **(B)** two edges with proportional vectors `e = r • e'`, both of length in `K`:
`e ∈ K²` iff `e' ∈ K²`. -/
theorem prop_in_K (K : Subfield ℝ) {e e' : Plane} {r : ℝ} (hr : r ≠ 0) (he : e = r • e')
    (hl : ‖e‖ ∈ K) (hl' : ‖e'‖ ∈ K) (hne' : e' ≠ 0) : InK K e ↔ InK K e' := by
  have hn : ‖e‖ = |r| * ‖e'‖ := by rw [he, norm_smul, Real.norm_eq_abs]
  have hpos : 0 < ‖e'‖ := norm_pos_iff.mpr hne'
  have habs : |r| ∈ K := by
    have : |r| = ‖e‖ / ‖e'‖ := by rw [hn]; field_simp
    rw [this]; exact K.div_mem hl hl'
  have hrK : r ∈ K := by
    rcases abs_cases r with ⟨h, _⟩ | ⟨h, _⟩
    · rw [← h]; exact habs
    · have : r = -|r| := by linarith
      rw [this]; exact K.neg_mem habs
  have h0 : e 0 = r * e' 0 := by rw [he]; simp
  have h1 : e 1 = r * e' 1 := by rw [he]; simp
  constructor
  · rintro ⟨a, b⟩
    refine ⟨?_, ?_⟩
    · have : e' 0 = e 0 / r := by rw [h0]; field_simp
      rw [this]; exact K.div_mem a hrK
    · have : e' 1 = e 1 / r := by rw [h1]; field_simp
      rw [this]; exact K.div_mem b hrK
  · rintro ⟨a, b⟩
    exact ⟨by rw [h0]; exact K.mul_mem hrK a, by rw [h1]; exact K.mul_mem hrK b⟩

theorem abs_mem_iff (K : Subfield ℝ) (x : ℝ) (h : |x| ∈ K) : x ∈ K := by
  rcases abs_cases x with ⟨h1, _⟩ | ⟨h1, _⟩
  · rwa [← h1]
  · have : x = -|x| := by linarith
    rw [this]; exact K.neg_mem h

theorem edgeVec_ne (T : Tri) (k : Fin 3) : edgeVec T k ≠ 0 := by
  intro h
  exact Erdos634.TilePlacement.pts_ne T (i := k + 1) (k := k) (by fin_cases k <;> decide)
    (sub_eq_zero.mp h)

theorem norm_edgeVec (T : Tri) (k : Fin 3) : ‖edgeVec T k‖ = dist (T.pts (k + 1)) (T.pts k) := by
  rw [edgeVec, dist_eq_norm]

/-- **L1 (direction half).**  In a congruent dissection whose model has all distances and
`|det|` in the subfield `K`, one edge vector in `K²` puts every edge vector of every tile in `K²`. -/
theorem edges_in_K {N : ℕ} (D : CongruentDissection N) (K : Subfield ℝ)
    (hd : ∀ j l, dist (D.model.pts j) (D.model.pts l) ∈ K) (hdet : |D.model.det| ∈ K)
    {i0 : Fin N} {k0 : Fin 3} (hbase : InK K (edgeVec (D.tile i0) k0)) :
    ∀ i k, InK K (edgeVec (D.tile i) k) := by
  have hdT : ∀ i k l, dist ((D.tile i).pts k) ((D.tile i).pts l) ∈ K := by
    intro i k l
    obtain ⟨σ, hσ⟩ := (D.tiles_congruent i).dist_eq
    rw [hσ]; exact hd _ _
  have hdetT : ∀ i, (D.tile i).det ∈ K := by
    intro i
    apply abs_mem_iff
    rw [Erdos634.KConj.abs_det_congr (D.tiles_congruent i)]; exact hdet
  have hreach : ∀ i, (nbrGraph D.toDissection).Reachable i0 i → ∃ k, InK K (edgeVec (D.tile i) k) := by
    intro i hi
    rw [SimpleGraph.reachable_iff_reflTransGen] at hi
    induction hi with
    | refl => exact ⟨k0, hbase⟩
    | @tail b c _ hadj ih =>
      obtain ⟨k, hk⟩ := ih
      have hall := tile_all_in_K K _ (hdT b) (hdetT b) hk
      obtain ⟨k1, l1, r, hr, he⟩ := adj_edges_parallel D.toDissection hadj
      refine ⟨l1, ?_⟩
      have he' : edgeVec (D.tile b) k1 = r • edgeVec (D.tile c) l1 := he
      have hl1 : ‖edgeVec (D.tile b) k1‖ ∈ K := by rw [norm_edgeVec]; exact hdT _ _ _
      have hl2 : ‖edgeVec (D.tile c) l1‖ ∈ K := by rw [norm_edgeVec]; exact hdT _ _ _
      have := (prop_in_K K hr he' hl1 hl2 (edgeVec_ne _ _)).1 (hall k1)
      exact this
  intro i k
  have hconn := nbrGraph_connected D.toDissection
  obtain ⟨k1, hk1⟩ := hreach i (hconn.preconnected i0 i)
  exact tile_all_in_K K _ (hdT i) (hdetT i) hk1 k

/-- **Base edge.**  If a target side (`pts 0 → pts 1`) lies on the x-axis, some tile edge on it has
its vector in `K²` (its length is a model distance, in `K`). -/
theorem base_edge_in_K {N : ℕ} (D : CongruentDissection N) (K : Subfield ℝ)
    (hd : ∀ j l, dist (D.model.pts j) (D.model.pts l) ∈ K)
    (h0 : D.target.pts 0 1 = 0) (h1 : D.target.pts 1 1 = 0) :
    ∃ i k, InK K (edgeVec (D.tile i) k) := by
  classical
  obtain ⟨part, hcov, -, hsum⟩ := Dissection.side_partition D.toDissection 0
  have h01 : (0 : Fin 3) + 1 = 1 := rfl
  rw [h01] at hcov hsum
  have hne : part.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    subst hemp
    have hn : (segment ℝ (D.target.pts 0) (D.target.pts 1)).Nonempty :=
      ⟨_, left_mem_segment ℝ _ _⟩
    simp at hcov
    rw [← hcov] at hn
    simp at hn
  obtain ⟨e, he⟩ := hne
  have hsub : (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts 0) (D.target.pts 1) := by
    intro x hx
    rw [← hcov]
    exact Set.mem_iUnion₂.mpr ⟨e, he, hx⟩
  have hy : ∀ x ∈ segment ℝ (D.target.pts 0) (D.target.pts 1), x 1 = 0 := by
    rintro x ⟨a, b, -, -, hab, rfl⟩
    simp [h0, h1]
  have hl : (D.tile e.1).pts e.2 ∈ (D.tile e.1).edge e.2 := left_mem_segment ℝ _ _
  have hr : (D.tile e.1).pts (e.2 + 1) ∈ (D.tile e.1).edge e.2 := right_mem_segment ℝ _ _
  have y1 := hy _ (hsub hl)
  have y2 := hy _ (hsub hr)
  refine ⟨e.1, e.2, ?_, ?_⟩
  · show (D.tile e.1).pts (e.2 + 1) 0 - (D.tile e.1).pts e.2 0 ∈ K
    set x := (D.tile e.1).pts (e.2 + 1) 0 - (D.tile e.1).pts e.2 0 with hx
    have hdist : dist ((D.tile e.1).pts (e.2 + 1)) ((D.tile e.1).pts e.2) ∈ K := by
      obtain ⟨σ, hσ⟩ := (D.tiles_congruent e.1).dist_eq
      rw [hσ]; exact hd _ _
    have hsq := sqd ((D.tile e.1).pts (e.2 + 1)) ((D.tile e.1).pts e.2)
    rw [y1, y2] at hsq
    have : dist ((D.tile e.1).pts (e.2 + 1)) ((D.tile e.1).pts e.2) = |x| := by
      rw [← Real.sqrt_sq dist_nonneg, hsq]
      rw [hx]; simp [Real.sqrt_sq_eq_abs]
    rw [this] at hdist
    exact abs_mem_iff K x hdist
  · show (D.tile e.1).pts (e.2 + 1) 1 - (D.tile e.1).pts e.2 1 ∈ K
    rw [y1, y2, sub_zero]; exact K.zero_mem

/-- **L1 (direction half), final form.**  Target side on the x-axis. -/
theorem edges_in_K_of_horizontal_side {N : ℕ} (D : CongruentDissection N) (K : Subfield ℝ)
    (hd : ∀ j l, dist (D.model.pts j) (D.model.pts l) ∈ K) (hdet : |D.model.det| ∈ K)
    (h0 : D.target.pts 0 1 = 0) (h1 : D.target.pts 1 1 = 0) :
    ∀ i k, InK K (edgeVec (D.tile i) k) := by
  obtain ⟨i0, k0, hb⟩ := base_edge_in_K D K hd h0 h1
  exact edges_in_K D K hd hdet hb

end Erdos634.H1gDir

#print axioms Erdos634.H1gDir.edges_in_K_of_horizontal_side

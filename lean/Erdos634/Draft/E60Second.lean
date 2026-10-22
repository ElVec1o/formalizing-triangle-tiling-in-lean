/-
Draft/E60Second.lean -- the second tile along an edge, for an arbitrary `Dissection`.

Geometric layer of the degree count of `Draft/E60Graph.lean` (Laczkovich's graph `Γ_a`; the count is the one of
Beeson and Zhang, arXiv:2604.01314, Lemma 3.5, transposed from the tile with an angle `2π/3` to the tile with an
angle `π/3`).  Nothing here is specific to a tile shape.

* `coord_on_edge`: barycentric coordinates of the point `pts k + θ (pts l − pts k)`.
* `localAngle_pi_on_edge`: for `0 < θ < 1` the local angle there is `π`.
* `exists_gap`: around any point there is a radius free of other tile vertices.
* `second_along` (the main statement): let `p = P + θ w` be a point of the edge `[P, P + w]` of the tile `i₀`,
  `0 ≤ θ < 1`, and let the points of that edge just after `p` be interior to the target.  Then another tile `j` has
  an edge `[Q, Q + s w]`, `s > 0`, on the same line, which either starts at `p` (`Q = p`) or contains `p` in its
  relative interior.  Proof: at a nearby non-vertex point of the edge exactly two tiles meet
  (`Dissection.second_tile_at_edge_point`), their edges are antiparallel (`Dissection.leftDir_antiparallel`), and the
  gap keeps the endpoints of the second edge away from the open stretch between `p` and that point.
* `next_at_junction`: if `p` is strictly inside the edge of `i₀` and is a vertex of some tile, the second edge
  starts at `p` (a third tile cannot pass through `p`: `RouteOne.two_through_excludes_third`).
* `interior_of_sum_gt_pi`, `interior_ray`: interior points from the local angle sum.

Composite-N formalization debt (the `π/3` leaf of the classification); not prime-case work.
No sorry, no native_decide.
-/
import Erdos634.CornerAnglePerm
import Erdos634.RouteOneVertexKill

open Erdos634.Geometry

namespace Erdos634.Draft.E60Second

variable {N : ℕ}

theorem fin3_cases : ∀ m k l : Fin 3, m ≠ k → m ≠ l → k ≠ l →
    (k = m + 1 ∧ l = m + 2) ∨ (k = m + 2 ∧ l = m + 1) := by decide

theorem fin3_third : ∀ k l : Fin 3, k ≠ l → ∃ m : Fin 3, m ≠ k ∧ m ≠ l ∧ ∀ j : Fin 3, j = m ∨ j = k ∨ j = l := by
  decide

theorem fin3_idx : ∀ x : Fin 3, (x + 1) + 1 = x + 2 ∧ (x + 1) + 2 = x ∧ (x + 2) + 1 = x ∧ (x + 2) + 2 = x + 1 ∧
    x + 1 ≠ x ∧ x + 2 ≠ x ∧ x + 1 ≠ x + 2 := by decide

/-- the three barycentric coordinates sum to `1` (indices `k, k+1, k+2`) -/
theorem coord_sum3 (T : Tri) (k : Fin 3) (q : Plane) :
    T.basis.coord k q + T.basis.coord (k + 1) q + T.basis.coord (k + 2) q = 1 := by
  have h := T.basis.sum_coord_apply_eq_one q
  rw [Fin.sum_univ_three] at h
  have key : ∀ (f : Fin 3 → ℝ) (k : Fin 3), f k + f (k + 1) + f (k + 2) = f 0 + f 1 + f 2 := by
    intro f k
    fin_cases k
    · rfl
    · show f 1 + f 2 + f 0 = f 0 + f 1 + f 2
      ring
    · show f 2 + f 0 + f 1 = f 0 + f 1 + f 2
      ring
  exact (key (fun i => T.basis.coord i q) k).trans h

/-- **Barycentric coordinates along the line of an edge.** -/
theorem coord_on_edge (T : Tri) {k l : Fin 3} (hkl : k ≠ l) (θ : ℝ) (j : Fin 3) :
    T.basis.coord j (T.pts k + θ • (T.pts l - T.pts k))
      = (if j = l then θ else 0) + (if j = k then 1 - θ else 0) := by
  have hcne : ∀ (i j : Fin 3), i ≠ j → T.basis.coord i (T.pts j) = 0 :=
    fun i j h => T.basis.coord_apply_ne h
  have hceq : ∀ i : Fin 3, T.basis.coord i (T.pts i) = 1 := fun i => T.basis.coord_apply_eq i
  have hlm : T.pts k + θ • (T.pts l - T.pts k) = AffineMap.lineMap (T.pts k) (T.pts l) θ := by
    rw [AffineMap.lineMap_apply]
    simp only [vsub_eq_sub, vadd_eq_add]
    abel
  rw [hlm, AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
  by_cases hjl : j = l
  · subst hjl
    have hjk : j ≠ k := fun h => hkl h.symm
    rw [hceq j, hcne j k hjk, if_pos rfl, if_neg hjk]; ring
  · by_cases hjk : j = k
    · subst hjk
      rw [hceq j, hcne j l hjl, if_neg hjl, if_pos rfl]; ring
    · rw [hcne j l hjl, hcne j k hjk, if_neg hjl, if_neg hjk]; ring

/-- a point strictly inside the edge `[pts k, pts l]`: one coordinate vanishes, the other two are positive -/
theorem onEdge_of_edge (T : Tri) {k l : Fin 3} (hkl : k ≠ l) {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) :
    ∃ m : Fin 3, m ≠ k ∧ m ≠ l ∧ T.basis.coord m (T.pts k + θ • (T.pts l - T.pts k)) = 0 ∧
      ∀ j, j ≠ m → 0 < T.basis.coord j (T.pts k + θ • (T.pts l - T.pts k)) := by
  obtain ⟨m, hmk, hml, hall⟩ := fin3_third k l hkl
  refine ⟨m, hmk, hml, ?_, ?_⟩
  · rw [coord_on_edge T hkl, if_neg hml, if_neg hmk]; ring
  · intro j hj
    rw [coord_on_edge T hkl]
    rcases hall j with h | h | h
    · exact absurd h hj
    · rw [h, if_neg hkl, if_pos rfl]; linarith
    · rw [h, if_pos rfl, if_neg (Ne.symm hkl)]; linarith

/-- **The local angle at a point strictly inside an edge is `π`.** -/
theorem localAngle_pi_on_edge (T : Tri) {k l : Fin 3} (hkl : k ≠ l) {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) :
    T.localAngle (T.pts k + θ • (T.pts l - T.pts k)) = Real.pi := by
  obtain ⟨m, -, -, hm0, hmpos⟩ := onEdge_of_edge T hkl h0 h1
  exact Erdos634.RouteOne.localAngle_pi_of_coords T _ m hm0 hmpos

/-- the local angle at a vertex lies strictly between `0` and `π` -/
theorem localAngle_vertex_bounds (T : Tri) (k : Fin 3) :
    0 < T.localAngle (T.pts k) ∧ T.localAngle (T.pts k) < Real.pi := by
  rw [Tri.localAngle_vertex]
  exact ⟨Erdos634.MarchFlank.cornerAngle_pos T k, Erdos634.RouteOneVertexKill.cornerAngle_lt_pi T k⟩

/-- **A gap.**  Around `p` there is a radius within which the only tile vertex is (possibly) `p` itself. -/
theorem exists_gap (D : Dissection N) (p : Plane) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (i : Fin N) (k : Fin 3), (D.tile i).pts k ≠ p → δ ≤ dist p ((D.tile i).pts k) := by
  classical
  let S : Finset ℝ := ((Finset.univ : Finset (Fin N × Fin 3)).filter
    (fun e => (D.tile e.1).pts e.2 ≠ p)).image (fun e => dist p ((D.tile e.1).pts e.2))
  by_cases hS : S.Nonempty
  · refine ⟨S.min' hS, ?_, ?_⟩
    · obtain ⟨e, he, heq⟩ := Finset.mem_image.mp (S.min'_mem hS)
      rw [← heq]
      exact dist_pos.mpr (Ne.symm (Finset.mem_filter.mp he).2)
    · intro i k hne
      exact S.min'_le _ (Finset.mem_image.mpr
        ⟨(i, k), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩, rfl⟩)
  · refine ⟨1, one_pos, ?_⟩
    intro i k hne
    exact absurd ⟨_, Finset.mem_image.mpr
      ⟨(i, k), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩, rfl⟩⟩ hS

/-- a point where the local angles of the tiles sum to more than `π` is interior to the target -/
theorem interior_of_sum_gt_pi (D : Dissection N) {p : Plane}
    (hp : Real.pi < ∑ i, (D.tile i).localAngle p) : p ∈ interior D.target.carrier := by
  classical
  rw [D.sum_localAngle_eq p] at hp
  have hpi := Real.pi_pos
  rw [Tri.localAngle] at hp
  split at hp
  · rename_i h
    have := Erdos634.RouteOneVertexKill.cornerAngle_lt_pi D.target h.choose
    linarith
  · split at hp
    · rename_i h
      exact (D.target.mem_interior_iff_coord_pos p).mpr h
    · split at hp
      · linarith
      · linarith

/-- two tiles, one through `p` and one with a positive local angle at `p` which is not `π`: `p` is interior -/
theorem interior_of_through_and_vertex (D : Dissection N) {p : Plane} {i j : Fin N} (hij : i ≠ j)
    (hi : (D.tile i).localAngle p = Real.pi) (hj : 0 < (D.tile j).localAngle p) :
    p ∈ interior D.target.carrier := by
  classical
  apply interior_of_sum_gt_pi
  have h1 : ({i, j} : Finset (Fin N)) ⊆ Finset.univ := Finset.subset_univ _
  have h2 : ∑ m ∈ ({i, j} : Finset (Fin N)), (D.tile m).localAngle p ≤ ∑ m, (D.tile m).localAngle p :=
    Finset.sum_le_sum_of_subset_of_nonneg h1 (fun m _ _ => (D.tile m).localAngle_nonneg p)
  rw [Finset.sum_pair hij, hi] at h2
  linarith

/-- the points of a ray from an interior point are interior for a while -/
theorem interior_ray {S : Set Plane} {p : Plane} (hp : p ∈ interior S) (w : Plane) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t → t < ε → p + t • w ∈ interior S := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp isOpen_interior p hp
  refine ⟨r / (‖w‖ + 1), by positivity, ?_⟩
  intro t ht0 ht
  apply hsub
  rw [Metric.mem_ball, dist_eq_norm, show p + t • w - p = t • w by abel, norm_smul, Real.norm_eq_abs,
    abs_of_pos ht0]
  have h1 : t * (‖w‖ + 1) < r := by
    rwa [lt_div_iff₀ (by positivity)] at ht
  nlinarith [norm_nonneg w]

set_option maxHeartbeats 1600000 in
/-- **The second tile along an edge.**  `P, P + w` are two vertices of the tile `i₀`, `p = P + θ w` with
`0 ≤ θ < 1`, and the points `P + (θ + t) w`, `0 < t < ε`, are interior to the target.  Then another tile `j` has
vertices `Q, Q + s w` with `s > 0`, and either `Q = p` or `p` lies strictly between them. -/
theorem second_along (D : Dissection N) (i₀ : Fin N) {k₀ l₀ : Fin 3} (hkl : k₀ ≠ l₀) {P w : Plane}
    (hP : (D.tile i₀).pts k₀ = P) (hw : (D.tile i₀).pts l₀ - (D.tile i₀).pts k₀ = w) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {ε : ℝ} (hε : 0 < ε)
    (hint : ∀ t : ℝ, 0 < t → t < ε → P + (θ + t) • w ∈ interior D.target.carrier) :
    ∃ j, j ≠ i₀ ∧ ∃ k l : Fin 3, k ≠ l ∧ ∃ s : ℝ, 0 < s ∧
      (D.tile j).pts l - (D.tile j).pts k = s • w ∧
      ((D.tile j).pts k = P + θ • w ∨
       ∃ ν : ℝ, 0 < ν ∧ ν < 1 ∧ P + θ • w = (D.tile j).pts k + ν • (s • w)) := by
  classical
  obtain ⟨p, hp⟩ : ∃ p : Plane, p = P + θ • w := ⟨_, rfl⟩
  rw [← hp]
  have hw0 : w ≠ 0 := by
    rw [← hw]
    exact sub_ne_zero.mpr (fun h => hkl ((D.tile i₀).indep.injective h).symm)
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  obtain ⟨δ, hδ, hgap⟩ := exists_gap D p
  -- the test parameter
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ℝ, t₀ = min (min (ε / 2) ((1 - θ) / 2)) (δ / (2 * ‖w‖)) := ⟨_, rfl⟩
  have ht₀pos : 0 < t₀ := by
    rw [ht₀]
    exact lt_min (lt_min (by linarith) (by linarith)) (by positivity)
  have ht₀ε : t₀ < ε := by
    have : t₀ ≤ ε / 2 := by rw [ht₀]; exact le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  have ht₀θ : θ + t₀ < 1 := by
    have : t₀ ≤ (1 - θ) / 2 := by rw [ht₀]; exact le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  have ht₀δ : t₀ * ‖w‖ < δ := by
    have h1 : t₀ ≤ δ / (2 * ‖w‖) := by rw [ht₀]; exact min_le_right _ _
    have h2 : t₀ * ‖w‖ ≤ δ / (2 * ‖w‖) * ‖w‖ := mul_le_mul_of_nonneg_right h1 hwn.le
    have h3 : δ / (2 * ‖w‖) * ‖w‖ = δ / 2 := by field_simp
    linarith
  obtain ⟨m, hm⟩ : ∃ m : Plane, m = P + (θ + t₀) • w := ⟨_, rfl⟩
  have hmp : m = p + t₀ • w := by rw [hm, hp, add_smul]; abel
  have hdist : dist p m = t₀ * ‖w‖ := by
    rw [hmp, dist_eq_norm, show p - (p + t₀ • w) = -(t₀ • w) by abel, norm_neg, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht₀pos]
  -- `m` is not a tile vertex
  have hmv : ∀ i k, m ≠ (D.tile i).pts k := by
    intro i k hmk
    by_cases hpk : (D.tile i).pts k = p
    · have h0 : dist p m = 0 := by rw [hmk, hpk]; exact dist_self _
      rw [hdist] at h0
      have := mul_pos ht₀pos hwn
      linarith
    · have := hgap i k hpk
      rw [← hmk, hdist] at this
      linarith
  have hmint : m ∈ interior D.target.carrier := by rw [hm]; exact hint t₀ ht₀pos ht₀ε
  obtain ⟨R, hR, hRt⟩ := Metric.isOpen_iff.mp isOpen_interior m hmint
  have hRt' : Metric.ball m R ⊆ D.target.carrier := hRt.trans interior_subset
  have hθt0 : 0 < θ + t₀ := by linarith
  obtain ⟨m₁, hm₁k, hm₁l, hm₁0, hm₁pos⟩ := onEdge_of_edge (D.tile i₀) hkl hθt0 ht₀θ
  rw [hw, hP, ← hm] at hm₁0 hm₁pos
  have hN : 0 < N := Fin.pos i₀
  obtain ⟨j, hj, k₂, hk₂0, hk₂pos⟩ :=
    D.second_tile_at_edge_point hN hmv hR hRt' (i₀ := i₀) ⟨m₁, hm₁0, hm₁pos⟩
  obtain ⟨c, hc, hlr⟩ := D.leftDir_antiparallel (Ne.symm hj) hm₁0 hm₁pos hk₂0 hk₂pos
  obtain ⟨i11, i12, i21, i22, hne1, hne2, hne12⟩ := fin3_idx k₂
  -- the edge of `i₀` through `m` is `± w`
  have h1 : ∃ r₁ : ℝ, r₁ ≠ 0 ∧ (D.tile i₀).leftDir (m₁ + 1) = r₁ • w := by
    unfold Tri.leftDir
    rw [(fin3_idx m₁).1]
    rcases fin3_cases m₁ k₀ l₀ hm₁k hm₁l hkl with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [← e1, ← e2]
      split
      · exact ⟨1, one_ne_zero, by rw [one_smul, hw]⟩
      · exact ⟨-1, by norm_num, by rw [neg_one_smul, ← hw]; abel⟩
    · rw [← e1, ← e2]
      split
      · exact ⟨-1, by norm_num, by rw [neg_one_smul, ← hw]; abel⟩
      · exact ⟨1, one_ne_zero, by rw [one_smul, hw]⟩
  have h2 : ∃ r₂ : ℝ, r₂ ≠ 0 ∧ (D.tile j).leftDir (k₂ + 1)
      = r₂ • ((D.tile j).pts (k₂ + 2) - (D.tile j).pts (k₂ + 1)) := by
    unfold Tri.leftDir
    rw [i11]
    split
    · exact ⟨1, one_ne_zero, by rw [one_smul]⟩
    · exact ⟨-1, by norm_num, by rw [neg_one_smul]; abel⟩
  obtain ⟨r₁, hr₁, e₁⟩ := h1
  obtain ⟨r₂, hr₂, e₂⟩ := h2
  obtain ⟨E, hEdef⟩ : ∃ E : Plane, E = (D.tile j).pts (k₂ + 2) - (D.tile j).pts (k₂ + 1) := ⟨_, rfl⟩
  rw [← hEdef] at e₂
  have hE : E = (c * r₁ / r₂) • w := by
    have h3 : r₂ • E = (c * r₁) • w := by rw [← e₂, hlr, e₁, smul_smul]
    have h4 : E = r₂⁻¹ • (r₂ • E) := by rw [smul_smul, inv_mul_cancel₀ hr₂, one_smul]
    rw [h4, h3, smul_smul]
    congr 1
    field_simp
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = c * r₁ / r₂ := ⟨_, rfl⟩
  rw [← hr] at hE
  have hr0 : r ≠ 0 := by rw [hr]; exact div_ne_zero (mul_ne_zero hc.ne hr₁) hr₂
  -- the position of `m` on the edge of `j`
  have hsum := coord_sum3 (D.tile j) k₂ m
  have hc1 : 0 < (D.tile j).basis.coord (k₂ + 1) m := hk₂pos _ hne1
  have hc2 : 0 < (D.tile j).basis.coord (k₂ + 2) m := hk₂pos _ hne2
  have e1 := Erdos634.RouteOne.sub_vertex_eq_combo (D.tile j) (k₂ + 1) m
  rw [i11, i12, hk₂0, zero_smul, add_zero, ← hEdef] at e1
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℝ, c₁ = (D.tile j).basis.coord (k₂ + 1) m := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : ℝ, c₂ = (D.tile j).basis.coord (k₂ + 2) m := ⟨_, rfl⟩
  rw [← hc₁] at hc1 hsum
  rw [← hc₂] at hc2 hsum e1
  rw [hk₂0] at hsum
  have hm1 : m = (D.tile j).pts (k₂ + 1) + c₂ • E := by rw [← e1]; abel
  have hA : (D.tile j).pts (k₂ + 2) = (D.tile j).pts (k₂ + 1) + E := by rw [hEdef]; abel
  obtain ⟨k, l, hkl', s, hs, hE', μ, hμ0, hμ1, hmk⟩ : ∃ k l : Fin 3, k ≠ l ∧ ∃ s : ℝ, 0 < s ∧
      (D.tile j).pts l - (D.tile j).pts k = s • w ∧ ∃ μ : ℝ, 0 < μ ∧ μ < 1 ∧
      m = (D.tile j).pts k + μ • (s • w) := by
    rcases lt_or_gt_of_ne hr0 with hneg | hpos
    · refine ⟨k₂ + 2, k₂ + 1, Ne.symm hne12, -r, by linarith, ?_, c₁, hc1, by linarith, ?_⟩
      · rw [hA, neg_smul, ← hE]; abel
      · rw [hm1, hA, neg_smul, ← hE]
        have : c₂ = 1 - c₁ := by linarith
        rw [this]
        module
    · refine ⟨k₂ + 1, k₂ + 2, hne12, r, hpos, ?_, c₂, hc2, by linarith, ?_⟩
      · rw [hA, ← hE]; abel
      · rw [hm1, hE]
  refine ⟨j, hj, k, l, hkl', s, hs, hE', ?_⟩
  by_cases hpk : (D.tile j).pts k = p
  · left; exact hpk
  · right
    have hk_eq : (D.tile j).pts k = p + (t₀ - μ * s) • w := by
      have h5 : (D.tile j).pts k = m - μ • (s • w) := by rw [hmk]; abel
      rw [h5, hmp]
      module
    have hσ : t₀ - μ * s < -t₀ := by
      by_contra hcon
      push_neg at hcon
      have hd := hgap j k hpk
      rw [hk_eq, dist_eq_norm, show p - (p + (t₀ - μ * s) • w) = -((t₀ - μ * s) • w) by abel, norm_neg,
        norm_smul, Real.norm_eq_abs] at hd
      have habs : |t₀ - μ * s| ≤ t₀ := abs_le.mpr ⟨hcon, by nlinarith [mul_pos hμ0 hs]⟩
      have : |t₀ - μ * s| * ‖w‖ ≤ t₀ * ‖w‖ := mul_le_mul_of_nonneg_right habs hwn.le
      linarith
    refine ⟨(μ * s - t₀) / s, div_pos (by linarith) hs, ?_, ?_⟩
    · rw [div_lt_one hs]
      nlinarith [mul_pos (sub_pos.mpr hμ1) hs]
    · have h6 : ((μ * s - t₀) / s) • (s • w) = (μ * s - t₀) • w := by
        rw [← mul_smul, div_mul_cancel₀ _ hs.ne']
      calc p = (p + (t₀ - μ * s) • w) + (μ * s - t₀) • w := by module
        _ = (D.tile j).pts k + ((μ * s - t₀) / s) • (s • w) := by rw [← hk_eq, h6]

/-- **The next tile at a junction.**  `p = P + θ w` lies strictly inside the edge `[P, P + w]` of the tile `i₀`
and is a vertex of the tile `i₁`.  Then a tile `j ≠ i₀` has an edge `[p, p + s w]`, `s > 0`. -/
theorem next_at_junction (D : Dissection N) (i₀ : Fin N) {k₀ l₀ : Fin 3} (hkl : k₀ ≠ l₀) {P w : Plane}
    (hP : (D.tile i₀).pts k₀ = P) (hw : (D.tile i₀).pts l₀ - (D.tile i₀).pts k₀ = w) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (i₁ : Fin N) (k₁ : Fin 3) (h1 : (D.tile i₁).pts k₁ = P + θ • w) :
    ∃ j, j ≠ i₀ ∧ ∃ k l : Fin 3, k ≠ l ∧ ∃ s : ℝ, 0 < s ∧
      (D.tile j).pts l - (D.tile j).pts k = s • w ∧ (D.tile j).pts k = P + θ • w := by
  have hpi₀ : (D.tile i₀).localAngle (P + θ • w) = Real.pi := by
    rw [← hP, ← hw]; exact localAngle_pi_on_edge (D.tile i₀) hkl hθ0 hθ1
  have hv := localAngle_vertex_bounds (D.tile i₁) k₁
  rw [h1] at hv
  have h01 : i₀ ≠ i₁ := by
    intro h; rw [h] at hpi₀; linarith [hv.2]
  have hint : P + θ • w ∈ interior D.target.carrier :=
    interior_of_through_and_vertex D h01 hpi₀ hv.1
  obtain ⟨ε, hε, hray⟩ := interior_ray hint w
  have hint' : ∀ t : ℝ, 0 < t → t < ε → P + (θ + t) • w ∈ interior D.target.carrier := by
    intro t ht0 ht
    have := hray t ht0 ht
    rwa [show P + θ • w + t • w = P + (θ + t) • w by module] at this
  obtain ⟨j, hj, k, l, hkl', s, hs, hE, hcase⟩ := second_along D i₀ hkl hP hw hθ0.le hθ1 hε hint'
  refine ⟨j, hj, k, l, hkl', s, hs, hE, ?_⟩
  rcases hcase with h | ⟨ν, hν0, hν1, hν⟩
  · exact h
  · exfalso
    have hpij : (D.tile j).localAngle (P + θ • w) = Real.pi := by
      rw [hν, ← hE]; exact localAngle_pi_on_edge (D.tile j) hkl' hν0 hν1
    have hj1 : j ≠ i₁ := by
      intro h; rw [h] at hpij; linarith [hv.2]
    exact Erdos634.RouteOne.two_through_excludes_third D hint i₀ j i₁ (Ne.symm hj) h01 hj1 hpi₀ hpij hv.1.ne'

end Erdos634.Draft.E60Second

#print axioms Erdos634.Draft.E60Second.second_along
#print axioms Erdos634.Draft.E60Second.next_at_junction

-- Draft/FluxERow2R.lean — ROW 2, LEMMA R ((private working notes, not included) §5 "Lemma R (the
-- longest side; BeesonI Lemma 11)") on a REAL `CongruentDissection`.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- Statement (file): `T` with `α < β < γ`, the side `AB` of a tile-similar target carrying no `c`-edge
-- ⇒ `γ = π/2`.  Credit: the pigeonhole is Beeson's (BeesonI Lemma 11, second paragraph; the file
-- restates and checks it).  Here: `Row2.lemmaR : 2 · model.angleAt 2 = π`.
--
-- The ORDERED SIDE WORD the file uses ("AB = P₀P₁ ∪ … ∪ P_{k−1}P_k") is not in the corpus as an
-- ordered chain (EdgeChain/FluxBoundary give the side edges as an unordered `Finset` that covers the
-- side with pairwise one-point overlaps).  It is NOT built here either: the pigeonhole is replaced by
-- an EXTREMAL argument on that finset (same content, no ordering needed; named):
-- * position on `AB`: `Row2.tau` = the barycentric coordinate of `B`, injective on `AB`
--   (`Row2.tau_inj`), onto `[0, 1]` (`Row2.tau_surj`); a side edge `e` is the `tau`-interval
--   `[lo e, hi e]` (`Row2.mem_eSet_iff`), `lo e < hi e`, and two side edges share no interior
--   parameter (`Row2.interiors_disjoint`, from `Dissection.sameside_edges_subsingleton`).
-- * every edge on `AB` has an `a`- or `b`-length, so the `γ`-vertex of its tile is one of its ends
--   (`Row2.gamma_endpoint`), and never `A` or `B` (`Row2.no_gamma_corner`: the corner sums are
--   `α, β < γ`).
-- * among the edges whose `γ`-end is the FAR end (`tau = hi`; the edge at `A` is one), take `e*` with
--   `hi` maximal, `s = hi e* < 1`; among the edges reaching past `s`, take `e'` with `lo` minimal.
--   Covering gives `lo e' ≤ s`, disjoint interiors give `lo e' = s`, and maximality of `e*` puts the
--   `γ`-end of `e'` at its near end: two `γ`-vertices at the point `P` of `AB` with `tau = s`, from two
--   DIFFERENT tiles (`Row2.distinct_tiles`: one tile cannot have two edges on a line).
-- * at `P` the local angles sum to `π` (`PinPlumbing.pin_angle_sum`), each other one is `0` or `≥ α`
--   (`Dissection.congruentDissection_localAngle_mem_boundary`), and `2γ + α > π` since `γ > β`
--   (`Row2.two_gamma`): so `2γ = π`.
--
-- Witness: see Draft/FluxERow2S.lean's header (Lemma R's joint hypotheses — scalene sorted tile,
-- tile-similar target, no `c`-edge on `AB` — hold for right-triangle rep-tilings; no such REAL Lean
-- dissection is in the corpus; `FluxRow2Witness.D2` has `c`-edges on `AB`).
--
-- Formalization debt; not progress on the three /goal outcomes.
import Erdos634.Draft.FluxERow2C
import Erdos634.SideWall

open scoped Classical

namespace Erdos634.Geometry

open Real

variable {N : ℕ}

/-! ## The position along side `0` (`AB = [pts 0, pts 1]`) -/

/-- Position along `AB`: the barycentric coordinate of `B`. -/
noncomputable def Row2.tau (T : Tri) (x : Plane) : ℝ := T.basis.coord 1 x

theorem Row2.tau_A (T : Tri) : Row2.tau T (T.pts 0) = 0 :=
  T.basis.coord_apply_ne (show (1 : Fin 3) ≠ 0 by decide)

theorem Row2.tau_B (T : Tri) : Row2.tau T (T.pts 1) = 1 := T.basis.coord_apply_eq 1

theorem Row2.edge0_coord (T : Tri) {x : Plane} (hx : x ∈ T.edge 0) :
    T.basis.coord 2 x = 0 ∧ 0 ≤ T.basis.coord 0 x ∧ 0 ≤ Row2.tau T x ∧
      T.basis.coord 0 x + Row2.tau T x = 1 := by
  have h2 : T.basis.coord 2 x = 0 := T.coord_eq_zero_of_mem_edge 0 hx
  have hc := T.edge_subset_carrier 0 hx
  rw [T.carrier_eq_nonneg_coord] at hc
  have hs := T.basis.sum_coord_apply_eq_one x
  rw [Fin.sum_univ_three, h2] at hs
  exact ⟨h2, hc 0, hc 1, by unfold Row2.tau; linarith⟩

theorem Row2.tau_inj (T : Tri) {x y : Plane} (hx : x ∈ T.edge 0) (hy : y ∈ T.edge 0)
    (h : Row2.tau T x = Row2.tau T y) : x = y := by
  obtain ⟨hx2, -, -, hx1⟩ := Row2.edge0_coord T hx
  obtain ⟨hy2, -, -, hy1⟩ := Row2.edge0_coord T hy
  unfold Row2.tau at h hx1 hy1
  apply T.basis.ext_elem
  intro i
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 by fin_cases i <;> simp) with rfl | rfl | rfl
  · linarith
  · exact h
  · rw [hx2, hy2]

theorem Row2.tau_surj (T : Tri) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    ∃ x ∈ T.edge 0, Row2.tau T x = s := by
  refine ⟨AffineMap.lineMap (T.pts 0) (T.pts 1) s, ?_, ?_⟩
  · show _ ∈ segment ℝ (T.pts 0) (T.pts (0 + 1))
    rw [segment_eq_image_lineMap]
    exact ⟨s, ⟨h0, h1⟩, rfl⟩
  · unfold Row2.tau
    rw [AffineMap.apply_lineMap]
    rw [show T.basis.coord 1 (T.pts 0) = 0 from Row2.tau_A T,
      show T.basis.coord 1 (T.pts 1) = 1 from Row2.tau_B T]
    simp [AffineMap.lineMap_apply]

theorem Row2.tau_image_segment (T : Tri) (X Y : Plane) :
    Row2.tau T '' segment ℝ X Y = Set.uIcc (Row2.tau T X) (Row2.tau T Y) := by
  rw [← segment_eq_uIcc]
  exact image_segment (f := T.basis.coord 1) (a := X) (b := Y)

theorem Row2.mem_seg_iff (T : Tri) {X Y z : Plane} (hseg : segment ℝ X Y ⊆ T.edge 0)
    (hz : z ∈ T.edge 0) :
    z ∈ segment ℝ X Y ↔ Row2.tau T z ∈ Set.uIcc (Row2.tau T X) (Row2.tau T Y) := by
  rw [← Row2.tau_image_segment]
  constructor
  · intro h; exact ⟨z, h, rfl⟩
  · rintro ⟨w, hw, hwz⟩
    rw [← Row2.tau_inj T (hseg hw) hz hwz]; exact hw

/-! ## Side edges on `AB` as `tau`-intervals -/

theorem Row2.sideEdge_sub (D : Dissection N) {j : Fin 3} {e : Fin N × Fin 3}
    (he : e ∈ D.sideEdges j) : D.eSet e ⊆ D.target.edge j := by
  unfold Dissection.sideEdges at he
  exact (Finset.mem_filter.mp he).2

/-- The near end of a side edge. -/
noncomputable def Row2.lo (D : Dissection N) (e : Fin N × Fin 3) : ℝ :=
  Row2.tau D.target ((D.tile e.1).pts e.2) ⊓ Row2.tau D.target ((D.tile e.1).pts (e.2 + 1))

/-- The far end of a side edge. -/
noncomputable def Row2.hi (D : Dissection N) (e : Fin N × Fin 3) : ℝ :=
  Row2.tau D.target ((D.tile e.1).pts e.2) ⊔ Row2.tau D.target ((D.tile e.1).pts (e.2 + 1))

theorem Row2.mem_eSet_iff (D : Dissection N) {e : Fin N × Fin 3} (he : e ∈ D.sideEdges 0)
    {z : Plane} (hz : z ∈ D.target.edge 0) :
    z ∈ D.eSet e ↔ Row2.lo D e ≤ Row2.tau D.target z ∧ Row2.tau D.target z ≤ Row2.hi D e := by
  have h := Row2.mem_seg_iff D.target (X := (D.tile e.1).pts e.2)
    (Y := (D.tile e.1).pts (e.2 + 1)) (Row2.sideEdge_sub D he) hz
  rw [Set.uIcc, Set.mem_Icc] at h
  exact h

theorem Row2.endpoints_mem (D : Dissection N) {e : Fin N × Fin 3} (he : e ∈ D.sideEdges 0) :
    (D.tile e.1).pts e.2 ∈ D.target.edge 0 ∧ (D.tile e.1).pts (e.2 + 1) ∈ D.target.edge 0 :=
  ⟨Row2.sideEdge_sub D he (left_mem_segment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))),
    Row2.sideEdge_sub D he (right_mem_segment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))⟩

theorem Row2.lo_hi_bounds (D : Dissection N) {e : Fin N × Fin 3} (he : e ∈ D.sideEdges 0) :
    0 ≤ Row2.lo D e ∧ Row2.hi D e ≤ 1 := by
  obtain ⟨h1, h2⟩ := Row2.endpoints_mem D he
  obtain ⟨-, a0, a1, a2⟩ := Row2.edge0_coord D.target h1
  obtain ⟨-, b0, b1, b2⟩ := Row2.edge0_coord D.target h2
  exact ⟨le_inf a1 b1, sup_le (by linarith) (by linarith)⟩

theorem Row2.lo_lt_hi (D : Dissection N) {e : Fin N × Fin 3} (he : e ∈ D.sideEdges 0) :
    Row2.lo D e < Row2.hi D e := by
  obtain ⟨h1, h2⟩ := Row2.endpoints_mem D he
  have hne : Row2.tau D.target ((D.tile e.1).pts e.2)
      ≠ Row2.tau D.target ((D.tile e.1).pts (e.2 + 1)) := by
    intro h
    have := Row2.tau_inj D.target h1 h2 h
    have hsucc : ∀ i : Fin 3, i ≠ i + 1 := by decide
    exact hsucc e.2 ((D.tile e.1).indep.injective this)
  unfold Row2.lo Row2.hi
  rcases lt_or_gt_of_ne hne with h | h
  · rw [inf_of_le_left h.le, sup_of_le_right h.le]; exact h
  · rw [inf_of_le_right h.le, sup_of_le_left h.le]; exact h

theorem Row2.eq_inf_or_sup (a b : ℝ) : (a = a ⊓ b ∨ a = a ⊔ b) ∧ (b = a ⊓ b ∨ b = a ⊔ b) := by
  rcases le_total a b with h | h
  · exact ⟨Or.inl (inf_of_le_left h).symm, Or.inr (sup_of_le_right h).symm⟩
  · exact ⟨Or.inr (sup_of_le_left h).symm, Or.inl (inf_of_le_right h).symm⟩

/-- Two edges on the same target side meet in at most one point (EdgeChain). -/
theorem Row2.sideEdges_inter_subsingleton (D : Dissection N) (j : Fin 3) {e₁ e₂ : Fin N × Fin 3}
    (h₁ : e₁ ∈ D.sideEdges j) (h₂ : e₂ ∈ D.sideEdges j) (hne : e₁ ≠ e₂) :
    (D.eSet e₁ ∩ D.eSet e₂).Subsingleton := by
  obtain ⟨g, c, hg, hle, hj, hj1, hj2⟩ := exists_supporting D.target j
  have hS : {x ∈ D.target.carrier | g x = c} = D.target.edge j :=
    target_contact_side D.target g c hle hj hj1 hj2
  have hon : ∀ e ∈ D.sideEdges j, ∀ y ∈ (D.tile e.1).edge e.2, g y = c := by
    intro e he y hy
    have hy' : y ∈ {x ∈ D.target.carrier | g x = c} := by
      rw [hS]; exact Row2.sideEdge_sub D he hy
    exact hy'.2
  have hleT : ∀ e : Fin N × Fin 3, ∀ y ∈ (D.tile e.1).carrier, g y ≤ c :=
    fun e y hy => hle y (tile_subset_target D e.1 hy)
  exact D.sameside_edges_subsingleton g c hg hne (hleT e₁) (hleT e₂) (hon e₁ h₁) (hon e₂ h₂)

/-- **Distinct edges on `AB` have disjoint interiors** (as `tau`-intervals). -/
theorem Row2.interiors_disjoint (D : Dissection N) {e e' : Fin N × Fin 3}
    (he : e ∈ D.sideEdges 0) (he' : e' ∈ D.sideEdges 0) (hne : e ≠ e') {s : ℝ}
    (h1 : Row2.lo D e < s) (h2 : s < Row2.hi D e) (h3 : Row2.lo D e' < s) (h4 : s < Row2.hi D e') :
    False := by
  obtain ⟨hl0, hh1⟩ := Row2.lo_hi_bounds D he
  have hu : max (Row2.lo D e) (Row2.lo D e') < s := max_lt h1 h3
  have hm1 := le_max_left (Row2.lo D e) (Row2.lo D e')
  have hm2 := le_max_right (Row2.lo D e) (Row2.lo D e')
  obtain ⟨z1, hz1, hz1t⟩ := Row2.tau_surj D.target
    (s := (max (Row2.lo D e) (Row2.lo D e') + s) / 2) (by linarith) (by linarith)
  obtain ⟨z, hz, hzt⟩ := Row2.tau_surj D.target (s := s) (by linarith) (by linarith)
  have m1 : z1 ∈ D.eSet e := (Row2.mem_eSet_iff D he hz1).mpr ⟨by linarith, by linarith⟩
  have m1' : z1 ∈ D.eSet e' := (Row2.mem_eSet_iff D he' hz1).mpr ⟨by linarith, by linarith⟩
  have m2 : z ∈ D.eSet e := (Row2.mem_eSet_iff D he hz).mpr ⟨by linarith, by linarith⟩
  have m2' : z ∈ D.eSet e' := (Row2.mem_eSet_iff D he' hz).mpr ⟨by linarith, by linarith⟩
  have := Row2.sideEdges_inter_subsingleton D 0 he he' hne ⟨m1, m1'⟩ ⟨m2, m2'⟩
  rw [this] at hz1t
  linarith

/-- **One tile has at most one edge on `AB`.** -/
theorem Row2.distinct_tiles (D : Dissection N) {e e' : Fin N × Fin 3}
    (he : e ∈ D.sideEdges 0) (he' : e' ∈ D.sideEdges 0) (hne : e ≠ e') : e.1 ≠ e'.1 := by
  intro h1
  have h2 : e.2 ≠ e'.2 := fun h2 => hne (Prod.ext h1 h2)
  have hcov : ∀ a b m : Fin 3, a ≠ b → m = a ∨ m = a + 1 ∨ m = b ∨ m = b + 1 := by decide
  have hall : ∀ m : Fin 3, (D.tile e.1).pts m ∈ D.target.edge 0 := by
    intro m
    obtain ⟨p1, p2⟩ := Row2.endpoints_mem D he
    obtain ⟨q1, q2⟩ := Row2.endpoints_mem D he'
    rw [← h1] at q1 q2
    rcases hcov e.2 e'.2 m h2 with rfl | rfl | rfl | rfl
    · exact p1
    · exact p2
    · exact q1
    · exact q2
  have hline : ∀ m, (D.tile e.1).pts m ∈ line[ℝ, D.target.pts 0, D.target.pts 1] := fun m =>
    (mem_segment_iff_wbtw.mp (hall m)).mem_affineSpan
  have hcol : Collinear ℝ (Set.range (D.tile e.1).pts) := by
    rw [(D.tile e.1).range_pts_eq' 0]
    refine (collinear_insert_insert_insert_of_mem_affineSpan_pair (hline (0 + 1)) (hline 0)
      (hline (0 + 2))).subset ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  exact (affineIndependent_iff_not_collinear.mp (D.tile e.1).indep) hcol

/-! ## The `γ`-vertices -/

/-- **The `γ`-vertex of a tile with an edge of length `≠ c` on it is an end of that edge.** -/
theorem Row2.gamma_endpoint (D : CongruentDissection N) {e : Fin N × Fin 3}
    (hl : D.eLen e ≠ D.model.oppLen 2) :
    ∃ k, (D.tile e.1).angleAt k = D.model.angleAt 2 ∧ (k = e.2 ∨ k = e.2 + 1) := by
  obtain ⟨σ, hσ⟩ := (D.tiles_congruent e.1).exists_perm
  refine ⟨σ.symm 2, by rw [(hσ _).1, Equiv.apply_symm_apply],
    Row2.fin3_ne_add_two _ _ fun h => hl ?_⟩
  rw [D.toDissection.eLen_eq_oppLen e, ← h, (hσ _).2, Equiv.apply_symm_apply]

/-- **No `γ`-vertex at a corner of angle `< γ`.** -/
theorem Row2.no_gamma_corner (D : CongruentDissection N) (t : Fin 3) (i : Fin N) (k : Fin 3)
    (hk : (D.tile i).angleAt k = D.model.angleAt 2) (hlt : D.target.angleAt t < D.model.angleAt 2) :
    (D.tile i).pts k ≠ D.target.pts t := by
  intro h
  have hloc : (D.tile i).localAngle (D.target.pts t) = D.model.angleAt 2 := by
    rw [← h, (D.tile i).localAngle_vertex k]; exact hk
  have hle : (D.tile i).localAngle (D.target.pts t) ≤ ∑ j, (D.tile j).localAngle (D.target.pts t) :=
    Finset.single_le_sum (fun j _ => (D.tile j).localAngle_nonneg _) (Finset.mem_univ i)
  rw [Row2.corner_sum D t, hloc] at hle
  linarith

/-- **Two `γ`'s at a side point force `2γ = π`** (the sum there is `π`, any further angle is
`≥ α`, and `2γ + α > α + β + γ = π` as `γ > β`). -/
theorem Row2.two_gamma (f : Fin N → ℝ) {θ0 θ1 θ2 : ℝ} (hnn : ∀ i, 0 ≤ f i)
    (hge : ∀ i, f i ≠ 0 → θ0 ≤ f i) (hsum : ∑ i, f i = π) (hθ : θ0 + θ1 + θ2 = π)
    (h12 : θ1 < θ2) {i1 i2 : Fin N} (hne : i1 ≠ i2) (h1 : f i1 = θ2) (h2 : f i2 = θ2) :
    2 * θ2 = π := by
  have hi2 : i2 ∈ Finset.univ.erase i1 := Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩
  have hsplit : ∑ i, f i = f i1 + (f i2 + ∑ i ∈ (Finset.univ.erase i1).erase i2, f i) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i1), ← Finset.add_sum_erase _ _ hi2]
  have hS0 : 0 ≤ ∑ i ∈ (Finset.univ.erase i1).erase i2, f i := Finset.sum_nonneg (fun i _ => hnn i)
  by_contra hne2
  have hSpos : ∑ i ∈ (Finset.univ.erase i1).erase i2, f i ≠ 0 := by
    intro h; apply hne2; rw [hsplit, h1, h2, h] at hsum; linarith
  obtain ⟨i3, hi3, hf3⟩ := Finset.exists_ne_zero_of_sum_ne_zero hSpos
  have h3 : f i3 ≤ ∑ i ∈ (Finset.univ.erase i1).erase i2, f i :=
    Finset.single_le_sum (fun i _ => hnn i) hi3
  have := hge i3 hf3
  rw [hsplit, h1, h2] at hsum
  linarith

/-! ## Lemma R -/

/-- **Lemma R (row 2; BeesonI Lemma 11's argument).**  For a real `CongruentDissection` whose target
has the model's angles (same labels), with `angleAt 0 < angleAt 1 < angleAt 2`, if the side
`AB = [pts 0, pts 1]` carries no tile edge of length `model.oppLen 2`, then `2γ = π`. -/
theorem Row2.lemmaR (D : CongruentDissection N)
    (hang : ∀ k, D.target.angleAt k = D.model.angleAt k)
    (h01 : D.model.angleAt 0 < D.model.angleAt 1) (h12 : D.model.angleAt 1 < D.model.angleAt 2)
    (hnoc : ∀ e ∈ D.sideEdges 0, D.eLen e ≠ D.model.oppLen 2) :
    2 * D.model.angleAt 2 = π := by
  classical
  have A_mem : D.target.pts 0 ∈ D.target.edge 0 := left_mem_segment ℝ _ _
  have B_mem : D.target.pts 1 ∈ D.target.edge 0 := right_mem_segment ℝ _ _
  have hnA : ∀ i k, (D.tile i).angleAt k = D.model.angleAt 2 →
      (D.tile i).pts k ≠ D.target.pts 0 :=
    fun i k hk => Row2.no_gamma_corner D 0 i k hk (by rw [hang 0]; linarith)
  have hnB : ∀ i k, (D.tile i).angleAt k = D.model.angleAt 2 →
      (D.tile i).pts k ≠ D.target.pts 1 :=
    fun i k hk => Row2.no_gamma_corner D 1 i k hk (by rw [hang 1]; exact h12)
  -- a `γ`-vertex on `AB` lies strictly between `A` and `B`
  have tau_lt : ∀ i k, (D.tile i).angleAt k = D.model.angleAt 2 →
      (D.tile i).pts k ∈ D.target.edge 0 →
      0 < Row2.tau D.target ((D.tile i).pts k) ∧ Row2.tau D.target ((D.tile i).pts k) < 1 := by
    intro i k hk hmem
    obtain ⟨-, h0, h1, h2⟩ := Row2.edge0_coord D.target hmem
    constructor
    · rcases h1.lt_or_eq with h | h
      · exact h
      · exact absurd (Row2.tau_inj D.target hmem A_mem (h.symm.trans (Row2.tau_A D.target).symm))
          (hnA i k hk)
    · rcases (show Row2.tau D.target ((D.tile i).pts k) ≤ 1 by linarith).lt_or_eq with h | h
      · exact h
      · exact absurd (Row2.tau_inj D.target hmem B_mem (h.trans (Row2.tau_B D.target).symm))
          (hnB i k hk)
  -- the `γ`-end of each edge on `AB`
  have gend : ∀ e ∈ D.sideEdges 0, ∃ k, (D.tile e.1).angleAt k = D.model.angleAt 2 ∧
      (D.tile e.1).pts k ∈ D.eSet e ∧
      (Row2.tau D.target ((D.tile e.1).pts k) = Row2.lo D.toDissection e ∨
        Row2.tau D.target ((D.tile e.1).pts k) = Row2.hi D.toDissection e) := by
    intro e he
    obtain ⟨k, hk, hke⟩ := Row2.gamma_endpoint D (hnoc e he)
    obtain ⟨hX, hY⟩ := Row2.eq_inf_or_sup (Row2.tau D.target ((D.tile e.1).pts e.2))
      (Row2.tau D.target ((D.tile e.1).pts (e.2 + 1)))
    rcases hke with rfl | rfl
    · exact ⟨_, hk, left_mem_segment ℝ _ _, hX⟩
    · exact ⟨_, hk, right_mem_segment ℝ _ _, hY⟩
  -- `R`: the edges whose `γ`-end is the far end; the edge at `A` is one
  obtain ⟨R, hR⟩ : ∃ R : Finset (Fin N × Fin 3), R = (D.sideEdges 0).filter (fun e =>
      ∃ k, (D.tile e.1).angleAt k = D.model.angleAt 2 ∧ (D.tile e.1).pts k ∈ D.eSet e ∧
        Row2.tau D.target ((D.tile e.1).pts k) = Row2.hi D.toDissection e) := ⟨_, rfl⟩
  obtain ⟨eA, heA, hAe⟩ := D.toDissection.exists_sideEdge_mem 0 A_mem
  have hReA : eA ∈ R := by
    obtain ⟨k, hk, hkm, hlh⟩ := gend eA heA
    have hpos := (tau_lt _ _ hk (Row2.sideEdge_sub D.toDissection heA hkm)).1
    have hlo : Row2.lo D.toDissection eA ≤ 0 := by
      have := ((Row2.mem_eSet_iff D.toDissection heA A_mem).mp hAe).1
      rwa [Row2.tau_A] at this
    rw [hR, Finset.mem_filter]
    refine ⟨heA, k, hk, hkm, ?_⟩
    rcases hlh with h | h
    · exfalso; linarith
    · exact h
  obtain ⟨eS, heSR, hmax⟩ := R.exists_max_image (Row2.hi D.toDissection) ⟨eA, hReA⟩
  rw [hR, Finset.mem_filter] at heSR
  obtain ⟨heS, kS, hkS, hkSm, hkSt⟩ := heSR
  obtain ⟨s, hs⟩ : ∃ s, s = Row2.hi D.toDissection eS := ⟨_, rfl⟩
  have hkSedge := Row2.sideEdge_sub D.toDissection heS hkSm
  have hs1 : s < 1 := by rw [hs, ← hkSt]; exact (tau_lt _ _ hkS hkSedge).2
  have hs0 : 0 < s := by rw [hs, ← hkSt]; exact (tau_lt _ _ hkS hkSedge).1
  -- `F`: the edges reaching past `s`; the edge at `B` is one
  obtain ⟨F, hF⟩ : ∃ F : Finset (Fin N × Fin 3),
      F = (D.sideEdges 0).filter (fun e => s < Row2.hi D.toDissection e) := ⟨_, rfl⟩
  obtain ⟨eB, heB, hBe⟩ := D.toDissection.exists_sideEdge_mem 0 B_mem
  have hFB : eB ∈ F := by
    rw [hF, Finset.mem_filter]
    refine ⟨heB, ?_⟩
    have := ((Row2.mem_eSet_iff D.toDissection heB B_mem).mp hBe).2
    rw [Row2.tau_B] at this
    linarith
  obtain ⟨e', he'F, hmin⟩ := F.exists_min_image (Row2.lo D.toDissection) ⟨eB, hFB⟩
  have he'F' := he'F
  rw [hF, Finset.mem_filter] at he'F'
  obtain ⟨he', he's⟩ := he'F'
  -- `lo e' ≤ s` (covering)
  have hlo' : Row2.lo D.toDissection e' ≤ s := by
    by_contra hc
    push Not at hc
    obtain ⟨-, hhi1⟩ := Row2.lo_hi_bounds D.toDissection he'
    have hlohi := Row2.lo_lt_hi D.toDissection he'
    obtain ⟨z, hz, hzw⟩ := Row2.tau_surj D.target (s := (s + Row2.lo D.toDissection e') / 2)
      (by linarith) (by linarith)
    obtain ⟨e'', he'', hze''⟩ := D.toDissection.exists_sideEdge_mem 0 hz
    have hz'' := (Row2.mem_eSet_iff D.toDissection he'' hz).mp hze''
    rw [hzw] at hz''
    have he''F : e'' ∈ F := by
      rw [hF, Finset.mem_filter]; exact ⟨he'', by linarith [hz''.2]⟩
    have := hmin e'' he''F
    linarith [hz''.1]
  have hne : e' ≠ eS := by
    intro h; rw [h, ← hs] at he's; exact lt_irrefl _ he's
  -- `lo e' = s` (disjoint interiors)
  have hlo'eq : Row2.lo D.toDissection e' = s := by
    by_contra hc
    have hlt : Row2.lo D.toDissection e' < s := lt_of_le_of_ne hlo' hc
    have hSlo := Row2.lo_lt_hi D.toDissection heS
    rw [← hs] at hSlo
    have hm1 := le_max_left (Row2.lo D.toDissection eS) (Row2.lo D.toDissection e')
    have hm2 := le_max_right (Row2.lo D.toDissection eS) (Row2.lo D.toDissection e')
    have hus : max (Row2.lo D.toDissection eS) (Row2.lo D.toDissection e') < s := max_lt hSlo hlt
    exact Row2.interiors_disjoint D.toDissection heS he' hne.symm
      (s := (max (Row2.lo D.toDissection eS) (Row2.lo D.toDissection e') + s) / 2)
      (by linarith) (by rw [← hs]; linarith) (by linarith) (by linarith)
  -- the `γ`-end of `e'` is its near end, at `s`
  obtain ⟨k', hk', hk'm, hk't⟩ := gend e' he'
  have hk's : Row2.tau D.target ((D.tile e'.1).pts k') = s := by
    rcases hk't with h | h
    · rw [h, hlo'eq]
    · exfalso
      have he'R : e' ∈ R := by
        rw [hR, Finset.mem_filter]; exact ⟨he', k', hk', hk'm, h⟩
      have := hmax e' he'R
      rw [← hs] at this
      linarith
  -- the two `γ`-vertices are one point `P`, of two different tiles
  have hk'edge := Row2.sideEdge_sub D.toDissection he' hk'm
  have hP : (D.tile e'.1).pts k' = (D.tile eS.1).pts kS :=
    Row2.tau_inj D.target hk'edge hkSedge (hk's.trans (hs.trans hkSt.symm))
  have htiles : eS.1 ≠ e'.1 := Row2.distinct_tiles D.toDissection heS he' hne.symm
  -- the angle sum at `P`
  have hPfr : (D.tile eS.1).pts kS ∈ frontier D.target.carrier :=
    Erdos634.SideWall.edge_subset_frontier D.target 0 hkSedge
  have hPnv : (D.tile eS.1).pts kS ∉ Set.range D.target.pts := by
    rintro ⟨m, hm⟩
    have hsP : Row2.tau D.target ((D.tile eS.1).pts kS) = s := hkSt.trans hs.symm
    rcases (show m = 0 ∨ m = 1 ∨ m = 2 by fin_cases m <;> simp) with rfl | rfl | rfl
    · rw [← hm, Row2.tau_A] at hsP; linarith
    · rw [← hm, Row2.tau_B] at hsP; linarith
    · have h2 := (Row2.edge0_coord D.target hkSedge).1
      rw [← hm] at h2
      have h1 : D.target.basis.coord 2 (D.target.pts 2) = 1 := D.target.basis.coord_apply_eq 2
      rw [h1] at h2; exact one_ne_zero h2
  have hsum := Erdos634.PinPlumbing.pin_angle_sum D.toDissection hPfr hPnv
  have hS : (D.tile eS.1).localAngle ((D.tile eS.1).pts kS) = D.model.angleAt 2 := by
    rw [(D.tile eS.1).localAngle_vertex kS]; exact hkS
  have h' : (D.tile e'.1).localAngle ((D.tile eS.1).pts kS) = D.model.angleAt 2 := by
    rw [← hP, (D.tile e'.1).localAngle_vertex k']; exact hk'
  have h2π := Row2.angle2_lt_pi D.model
  refine Row2.two_gamma (fun i => (D.tile i).localAngle ((D.tile eS.1).pts kS))
    (θ0 := D.model.angleAt 0) (θ1 := D.model.angleAt 1)
    (fun i => (D.tile i).localAngle_nonneg _) ?_ hsum D.model.angleAt_sum h12 htiles hS h'
  intro i hi
  have hi' : (D.tile i).localAngle ((D.tile eS.1).pts kS) ≠ 0 := hi
  show D.model.angleAt 0 ≤ (D.tile i).localAngle ((D.tile eS.1).pts kS)
  have hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = D.model.angleAt 0 := rfl
  have hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = D.model.angleAt 1 := rfl
  have hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = D.model.angleAt 2 := rfl
  have hv := Dissection.congruentDissection_localAngle_mem_boundary D
    (D.model.angleAt 0) (D.model.angleAt 1) (D.model.angleAt 2) hα' hβ' hγ' hPfr hPnv i
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with h | h | h | h | h
  · rw [h]
  · rw [h]; linarith
  · rw [h]; linarith
  · rw [h]; linarith
  · exact absurd h hi'

/-- `D_cc = 0` (no `c`-edge on `AB`) in the form Lemma R takes. -/
theorem Row2.noc_of_sideCount (D : CongruentDissection N) (h : D.sideCount 2 2 = 0) :
    ∀ e ∈ D.sideEdges 0, D.eLen e ≠ D.model.oppLen 2 := by
  intro e he hl
  have : 0 < D.sideCount 2 2 := Row2.sideCount_pos D (i := 2) he hl
  omega

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Row2.tau_inj
#print axioms Erdos634.Geometry.Row2.tau_surj
#print axioms Erdos634.Geometry.Row2.mem_eSet_iff
#print axioms Erdos634.Geometry.Row2.interiors_disjoint
#print axioms Erdos634.Geometry.Row2.distinct_tiles
#print axioms Erdos634.Geometry.Row2.gamma_endpoint
#print axioms Erdos634.Geometry.Row2.two_gamma
#print axioms Erdos634.Geometry.Row2.lemmaR

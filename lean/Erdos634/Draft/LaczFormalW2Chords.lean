import Erdos634.Draft.LaczFormalW2Lines

/-!
# Rule W2: the horizontal chord `[G₁, G₂]` and the chord `[P₂, V₂]`

Erdős #634, band program, rule W2 (`PROOF_W2.md`).  Credit: AI assistant (item 3, band program), Beeson–Roșu, Beeson,
Laczkovich (chord covers), Paliy.  UNAUDITED.

`w2_horizontal`: the far side (above) of the tile edge `[G₁, G₂]` of `T'` is a single tile edge `[G₁, G₂]`
(arithmetic `D3`, `e ≥ 2`), provided no tile edge above passes through `G₂`.
`w2_chord2b`: the far side (right) of the chord `[P₂, V₂]`, whose near side is the edges `[P₂, G₂]`, `[G₂, V₂]`,
consists of two `b`-edges `[P₂, G₂]`, `[G₂, V₂]` (arithmetic `D2`, `f ≥ 3`), provided no tile edge passes through `V₂`.
-/

namespace Erdos634.LaczJunction.Walk

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Grammar
open Erdos634.Draft.TraceCovering

variable {N : ℕ}

theorem w2_habc {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r) (i : Fin N) (k : Fin 3) :
    dist ((D.tile i).pts k) ((D.tile i).pts (k+1)) = (ta e f : ℝ) ∨
    dist ((D.tile i).pts k) ((D.tile i).pts (k+1)) = (tb e f : ℝ) ∨
    dist ((D.tile i).pts k) ((D.tile i).pts (k+1)) = (tc e f : ℝ) := by
  rcases edge_length_mem D i k with h | h | h
  · exact Or.inr (Or.inr (by rw [h, S.hsc]))
  · exact Or.inr (Or.inl (by rw [h, S.hsb]))
  · exact Or.inl (by rw [h, S.hsa])

theorem w2_horizontal {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r) (he2 : 2 ≤ e)
    (hori : 0 < cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p))
    {e0 v G1 G2 : Plane} (hG2 : G2 = G1 + e0) (hG1v : G1 = D.target.pts p + v)
    (he0n : ‖e0‖ = (tc e f : ℝ)) (hcr : 0 < cross e0 v)
    (hAP : ∃ μ : ℝ, 0 < μ ∧ D.target.pts r - D.target.pts p = μ • v)
    (hG1seg : G1 ∈ openSegment ℝ (D.target.pts p) (D.target.pts r))
    (hG2int : G2 ∈ interior D.target.carrier)
    (i' : Fin N) (kG kH : Fin 3) (hkGH : kH ≠ kG) (hG' : (D.tile i').pts kG = G1)
    (hH' : (D.tile i').pts kH = G2)
    (hGend : ¬ Straddled D.toDissection (-(crossL e0)) (-(cross e0 G1)) G2) :
    ∃ (i : Fin N) (k : Fin 3), (((D.tile i).pts k = G1 ∧ (D.tile i).pts (k + 1) = G2) ∨
      ((D.tile i).pts k = G2 ∧ (D.tile i).pts (k + 1) = G1)) ∧
      (∀ j, 0 ≤ cross e0 ((D.tile i).pts j - G1)) := by
  classical
  set LC := D.target.pts p with hLC
  set AP := D.target.pts r with hAP'
  have he0 : e0 ≠ 0 := by
    intro h; rw [h] at hcr; simp [cross] at hcr
  have hne : G1 ≠ G2 := by
    intro h; apply he0
    have : e0 = G2 - G1 := by rw [hG2]; abel
    rw [this, ← h]; simp
  have hlm : ∀ t : ℝ, AffineMap.lineMap G1 G2 t = G1 + t • e0 := by
    intro t; rw [AffineMap.lineMap_apply]; simp [hG2, add_comm]
  have hdist : dist G1 G2 = ((tc e f : ℕ) : ℝ) := by
    rw [dist_comm, dist_eq_norm, hG2, add_sub_cancel_left, he0n]
  have hg0 : (-(crossL e0) : Plane →ₗ[ℝ] ℝ) ≠ 0 := by
    intro h
    apply he0
    apply eq_zero_of_cross_eq_zero
    intro w
    have := congrArg (fun g : Plane →ₗ[ℝ] ℝ => g w) h
    simpa using this
  have hgP : (-(crossL e0) : Plane →ₗ[ℝ] ℝ) G1 = -(cross e0 G1) := by simp [crossL_apply]
  have hgG : (-(crossL e0) : Plane →ₗ[ℝ] ℝ) G2 = -(cross e0 G1) := by
    simp only [LinearMap.neg_apply, crossL_apply]
    rw [hG2, cross_add_right, Erdos634.Geometry.cross_self]; ring
  -- positions
  obtain ⟨μ, hμ, hAPv⟩ := hAP
  have hLCmem : LC ∈ D.target.carrier := subset_convexHull ℝ _ (Set.mem_range_self p)
  have hAPmem : AP ∈ D.target.carrier := subset_convexHull ℝ _ (Set.mem_range_self r)
  have hG1mem : G1 ∈ D.target.carrier := D.target.convex.openSegment_subset hLCmem hAPmem hG1seg
  have hint : ∀ t : ℝ, 0 < t → t < 1 → AffineMap.lineMap G1 G2 t ∈ interior D.target.carrier := by
    intro t ht0 ht1
    rw [D.target.mem_interior_iff_coord_pos]
    intro j
    rw [coord_lineMap]
    have h1 : 0 ≤ D.target.basis.coord j G1 := by
      have := hG1mem
      rw [D.target.carrier_eq_nonneg_coord] at this
      exact this j
    have h2 : 0 < D.target.basis.coord j G2 := (D.target.mem_interior_iff_coord_pos G2).mp hG2int j
    nlinarith
  have hbef : ∀ t : ℝ, t < 0 → AffineMap.lineMap G1 G2 t ∉ D.target.carrier := by
    intro t ht hmem
    have h1 := target_right_leg S.hpq S.hpr S.hqr hori _ hmem
    rw [hlm, hAPv] at h1
    have e1 : G1 + t • e0 - LC = v + t • e0 := by rw [hG1v]; abel
    rw [e1, cross_smul_left, cross_add_right, cross_smul_right, Erdos634.Geometry.cross_self,
      cross_swap v e0] at h1
    nlinarith [mul_pos hμ hcr]
  have hnear : ∀ t : ℝ, 0 < t → t < 1 → ∃ (i : Fin N) (k : Fin 3),
      AffineMap.lineMap G1 G2 t ∈ (D.tile i).edge k := by
    intro t ht0 ht1
    obtain ⟨idx, hidx⟩ := edge_idx (D.tile i') kG kH hkGH
    refine ⟨i', idx, ?_⟩
    rw [hidx, hG', hH', segment_eq_image_lineMap]
    exact ⟨t, ⟨ht0.le, ht1.le⟩, rfl⟩
  have hcover : ∀ x y z : ℕ, x * ta e f + y * tb e f + z * tc e f = tc e f → x + y + z = 1 := by
    intro x y z h
    obtain ⟨hx, hy, hz⟩ := D3_c_unique e f x y z he2 S.hef S.hcop h
    omega
  obtain ⟨i, k, hk, hall⟩ := L3_one_g D.toDissection (ta e f) (tb e f) (tc e f) (tc e f) hcover
    (fun i k => w2_habc S i k) hne hdist (-(crossL e0)) (-(cross e0 G1)) hg0 hgP hgG hint hbef hnear hGend
  refine ⟨i, k, hk, fun j => ?_⟩
  have := hall j
  simp only [LinearMap.neg_apply, crossL_apply] at this
  have e1 : cross e0 ((D.tile i).pts j - G1) = cross e0 ((D.tile i).pts j) - cross e0 G1 := cross_sub_right _ _ _
  rw [e1]; linarith


/-- **No tile edge on the line `PV` passes through `V` when the line leaves the target just beyond `V`.** -/
theorem no_straddle_beyond (D : Dissection N) {P V : Plane} (hne : P ≠ V)
    (hbey : ∀ t : ℝ, 1 < t → AffineMap.lineMap P V t ∉ D.target.carrier) :
    ¬ Straddled D (crossL (V - P)) (cross (V - P) P) V := by
  classical
  rintro ⟨e, he, a', b', ha', hb', hab', hV⟩
  have hu : V - P ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hch := Dissection.mem_lineChain.mp he
  obtain ⟨hX, hY, -⟩ := hch
  simp only [crossL_apply] at hX hY
  set X := (D.tile e.1).pts e.2 with hXdef
  set Y := (D.tile e.1).pts (e.2 + 1) with hYdef
  have cX : cross (V - P) (X - P) = 0 := by rw [cross_sub_right]; linarith
  have cY : cross (V - P) (Y - P) = 0 := by rw [cross_sub_right]; linarith
  obtain ⟨sX, hsX⟩ := on_line_param hu cX
  obtain ⟨sY, hsY⟩ := on_line_param hu cY
  have hXe : X = P + sX • (V - P) := by rw [← hsX]; abel
  have hYe : Y = P + sY • (V - P) := by rw [← hsY]; abel
  have hXY : X ≠ Y := by
    intro h
    have : e.2 = e.2 + 1 := (D.tile e.1).indep.injective h
    exact (by decide : ∀ k : Fin 3, k ≠ k + 1) e.2 this
  have hsne : sX ≠ sY := by
    intro h; apply hXY; rw [hXe, hYe, h]
  have h1 : 1 = a' * sX + b' * sY := by
    have : V - P = (a' * sX + b' * sY) • (V - P) := by
      calc V - P = (a' • X + b' • Y) - P := by rw [hV]
        _ = a' • (X - P) + b' • (Y - P) := by
            have : P = (a' + b') • P := by rw [hab', one_smul]
            calc a' • X + b' • Y - P = a' • X + b' • Y - (a' + b') • P := by rw [← this]
              _ = a' • (X - P) + b' • (Y - P) := by module
        _ = (a' * sX + b' * sY) • (V - P) := by rw [hsX, hsY]; module
    have := smul_injective_of_ne hu (show (1:ℝ) • (V - P) = (a' * sX + b' * sY) • (V - P) by rw [one_smul]; exact this)
    exact this
  have hex : 1 < sX ∨ 1 < sY := by
    by_contra hh; push_neg at hh
    obtain ⟨h0, h0'⟩ := hh
    rcases lt_or_gt_of_ne hsne with hl | hl
    · nlinarith
    · nlinarith
  have hXmem : X ∈ D.target.carrier :=
    Erdos634.BaseSelection.tile_subset_target D e.1 (subset_convexHull ℝ _ (Set.mem_range_self _))
  have hYmem : Y ∈ D.target.carrier :=
    Erdos634.BaseSelection.tile_subset_target D e.1 (subset_convexHull ℝ _ (Set.mem_range_self _))
  rcases hex with hx | hy
  · apply hbey sX hx
    have : AffineMap.lineMap P V sX = X := by rw [hXe, AffineMap.lineMap_apply]; simp [add_comm]
    rw [this]; exact hXmem
  · apply hbey sY hy
    have : AffineMap.lineMap P V sY = Y := by rw [hYe, AffineMap.lineMap_apply]; simp [add_comm]
    rw [this]; exact hYmem


theorem w2_chord2b {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r) (hf3 : 3 ≤ f)
    {P2 G2 V2 u : Plane} (hu : u = G2 - P2) (hV2 : V2 = P2 + (2 : ℝ) • u) (hun : ‖u‖ = (tb e f : ℝ))
    (hP2seg : P2 ∈ openSegment ℝ (D.target.pts p) (D.target.pts q))
    (hV2seg : V2 ∈ openSegment ℝ (D.target.pts p) (D.target.pts r))
    (i2 : Fin N) (k2 : Fin 3) (hT1 : (D.tile i2).edge k2 = segment ℝ P2 G2)
    (iY : Fin N) (kY : Fin 3) (hY : (D.tile iY).edge kY = segment ℝ G2 V2) :
    ∃ (ia ka ib kb : _), (ia, ka) ≠ (ib, kb) ∧
      (((D.tile ia).pts ka = P2 ∧ (D.tile ia).pts (ka + 1) = G2) ∨
        ((D.tile ia).pts ka = G2 ∧ (D.tile ia).pts (ka + 1) = P2)) ∧
      (((D.tile ib).pts kb = G2 ∧ (D.tile ib).pts (kb + 1) = V2) ∨
        ((D.tile ib).pts kb = V2 ∧ (D.tile ib).pts (kb + 1) = G2)) ∧
      (∀ j, cross u ((D.tile ia).pts j - P2) ≤ 0) ∧ (∀ j, cross u ((D.tile ib).pts j - P2) ≤ 0) := by
  classical
  have hbpos : (0:ℝ) < tb e f := by exact_mod_cast b_pos e f S.he S.hef
  have hun0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hun; linarith
  have hw : V2 - P2 = (2:ℝ) • u := by rw [hV2]; abel
  have hne : P2 ≠ V2 := by
    intro h; rw [h, sub_self] at hw
    have : (2:ℝ) • u = 0 := hw.symm
    exact hun0 (by simpa using this)
  have hG2 : G2 = P2 + u := by rw [hu]; abel
  have hmid : midpoint ℝ P2 V2 = G2 := by
    rw [midpoint_eq_smul_add, hV2, hG2]
    simp only [invOf_eq_inv]; module
  have hlm : ∀ t : ℝ, AffineMap.lineMap P2 V2 t = P2 + (2 * t) • u := by
    intro t; rw [AffineMap.lineMap_apply]; simp only [vsub_eq_sub, vadd_eq_add]; rw [hw]; module
  have hdist : dist P2 V2 = 2 * ((tb e f : ℕ) : ℝ) := by
    rw [dist_comm, dist_eq_norm, hw, norm_smul, hun]; simp
  have hPG2 : dist P2 G2 = (tb e f : ℝ) := by
    rw [dist_comm, dist_eq_norm, ← hu, hun]
  have hVG : V2 - G2 = u := by rw [hV2, hG2]; module
  have hdG : dist G2 V2 = (tb e f : ℝ) := by
    rw [dist_comm, dist_eq_norm, hVG, hun]
  obtain ⟨hint, hbef, hbey⟩ := chord_geometry D.target S.hpq S.hpr S.hqr hP2seg hV2seg
  set w := V2 - P2 with hwdef
  have hw0 : w ≠ 0 := by rw [hw]; intro h; exact hun0 (by simpa using h)
  have hg0 : (crossL w : Plane →ₗ[ℝ] ℝ) ≠ 0 := by
    intro h
    apply hw0
    apply eq_zero_of_cross_eq_zero
    intro v
    have := congrArg (fun g : Plane →ₗ[ℝ] ℝ => g v) h
    simpa using this
  have hgP : (crossL w : Plane →ₗ[ℝ] ℝ) P2 = cross w P2 := by simp [crossL_apply]
  have hgG : (crossL w : Plane →ₗ[ℝ] ℝ) V2 = cross w P2 := by
    simp only [crossL_apply]
    have hV2' : V2 = P2 + w := by rw [hwdef]; abel
    rw [hV2', cross_add_right, Erdos634.Geometry.cross_self, add_zero]
  have hwall : ∀ t : ℝ, 0 < t → t < 1 → ∀ i, AffineMap.lineMap P2 V2 t ∉ interior (D.tile i).carrier := by
    intro t ht0 ht1 i
    by_cases ht : t ≤ 1 / 2
    · have hmem : AffineMap.lineMap P2 V2 t ∈ (D.tile i2).edge k2 := by
        rw [hT1, segment_eq_image_lineMap]
        refine ⟨2 * t, ⟨by linarith, by linarith⟩, ?_⟩
        rw [hlm, AffineMap.lineMap_apply, hG2]; simp only [vsub_eq_sub, vadd_eq_add]; module
      exact D.edge_point_not_interior hmem i
    · have hmem : AffineMap.lineMap P2 V2 t ∈ (D.tile iY).edge kY := by
        rw [hY, segment_eq_image_lineMap]
        refine ⟨2 * t - 1, ⟨by linarith, by linarith⟩, ?_⟩
        rw [hlm, AffineMap.lineMap_apply, hG2, hV2]; simp only [vsub_eq_sub, vadd_eq_add]; module
      exact D.edge_point_not_interior hmem i
  have hGend := no_straddle_beyond D.toDissection hne hbey
  obtain ⟨e₁, e₂, hne12, h1, h2, hl1, hl2, hpos⟩ := L3_two_g D.toDissection (ta e f) (tb e f) (tc e f)
    (fun x y z h => D2_two_b e f x y z S.he S.hef hf3 S.hcop h) (fun i k => w2_habc S i k) hne hdist
    (crossL w) (cross w P2) hg0 hgP hgG hint hbef hwall hGend
  rw [hmid] at hpos
  have hfin : ∀ ea eb : Fin N × Fin 3, ea ≠ eb → ea ∈ D.lineChain (crossL w) (cross w P2) →
      eb ∈ D.lineChain (crossL w) (cross w P2) →
      dist ((D.tile ea.1).pts ea.2) ((D.tile ea.1).pts (ea.2 + 1)) = (tb e f : ℝ) →
      dist ((D.tile eb.1).pts eb.2) ((D.tile eb.1).pts (eb.2 + 1)) = (tb e f : ℝ) →
      (D.tile ea.1).edge ea.2 = segment ℝ P2 G2 → (D.tile eb.1).edge eb.2 = segment ℝ G2 V2 →
      ∃ (ia ka ib kb : _), (ia, ka) ≠ (ib, kb) ∧
      (((D.tile ia).pts ka = P2 ∧ (D.tile ia).pts (ka + 1) = G2) ∨
        ((D.tile ia).pts ka = G2 ∧ (D.tile ia).pts (ka + 1) = P2)) ∧
      (((D.tile ib).pts kb = G2 ∧ (D.tile ib).pts (kb + 1) = V2) ∨
        ((D.tile ib).pts kb = V2 ∧ (D.tile ib).pts (kb + 1) = G2)) ∧
      (∀ j, cross u ((D.tile ia).pts j - P2) ≤ 0) ∧ (∀ j, cross u ((D.tile ib).pts j - P2) ≤ 0) := by
    intro ea eb hne' ha hb la lb sa sb
    have hneG : P2 ≠ G2 := by
      intro h; rw [h, dist_self] at hPG2; linarith
    have hneG2 : G2 ≠ V2 := by
      intro h; rw [h, dist_self] at hdG; linarith
    have ha1 : (D.tile ea.1).pts ea.2 ∈ segment ℝ P2 G2 := by
      rw [← sa]; exact left_mem_segment ℝ _ _
    have ha2 : (D.tile ea.1).pts (ea.2 + 1) ∈ segment ℝ P2 G2 := by
      rw [← sa]; exact right_mem_segment ℝ _ _
    have hb1 : (D.tile eb.1).pts eb.2 ∈ segment ℝ G2 V2 := by
      rw [← sb]; exact left_mem_segment ℝ _ _
    have hb2 : (D.tile eb.1).pts (eb.2 + 1) ∈ segment ℝ G2 V2 := by
      rw [← sb]; exact right_mem_segment ℝ _ _
    have ea' := ends_of_segment hneG ha1 ha2 (by rw [la, hPG2])
    have eb' := ends_of_segment hneG2 hb1 hb2 (by rw [lb, hdG])
    have hca := Dissection.mem_lineChain.mp ha
    have hcb := Dissection.mem_lineChain.mp hb
    have side : ∀ (i : Fin N), (∀ j, (crossL w) ((D.tile i).pts j) ≤ cross w P2) →
        ∀ j, cross u ((D.tile i).pts j - P2) ≤ 0 := by
      intro i hh j
      have := hh j
      simp only [crossL_apply] at this
      have e1 : cross w ((D.tile i).pts j - P2) = cross w ((D.tile i).pts j) - cross w P2 := cross_sub_right _ _ _
      have e2 : cross w ((D.tile i).pts j - P2) = 2 * cross u ((D.tile i).pts j - P2) := by
        rw [hw, cross_smul_left]
      linarith
    exact ⟨ea.1, ea.2, eb.1, eb.2, by simpa using hne', ea', eb', side ea.1 hca.2.2, side eb.1 hcb.2.2⟩
  rcases hpos with ⟨q1, q2⟩ | ⟨q1, q2⟩
  · exact hfin e₁ e₂ hne12 h1 h2 hl1 hl2 (by rw [q1]) (by rw [q2])
  · exact hfin e₂ e₁ hne12.symm h2 h1 hl2 hl1 (by rw [q1]) (by rw [q2])

end Erdos634.LaczJunction.Walk

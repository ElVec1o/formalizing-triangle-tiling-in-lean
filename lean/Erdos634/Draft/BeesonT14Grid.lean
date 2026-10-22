import Erdos634.Draft.BeesonT14Piece

/-!
# Beeson Theorem 14, general parameters: parallelogram of cells

A parallelogram `O + s U + t V`, `0 <= s <= m`, `0 <= t <= n`, is tiled when every cell is (hypothesis `hcell`);
the grid is built by induction with `glueR`.  Credit Beeson (arXiv 1206.2229), Zhang (arXiv 2512.22696).  UNAUDITED.
-/

namespace Erdos634.BeesonT14Grid

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.GlueCut Erdos634.SssCongruent Erdos634.ZhangL1 Erdos634.ZhangPara
  Erdos634.ZhangSporadic Erdos634.ZhangThm4 Erdos634.BeesonT14Chart Erdos634.BeesonT14Abs
  Erdos634.BeesonT14Piece

noncomputable def cxf (vx vw Ox Ow X W : ℝ) : ℝ := (X - Ox) * vw - (W - Ow) * vx
noncomputable def cyf (ux uw Ox Ow X W : ℝ) : ℝ := ux * (W - Ow) - uw * (X - Ox)

def PgP (ux uw vx vw Ox Ow m n : ℝ) (X W : ℝ) : Prop :=
  0 ≤ cxf vx vw Ox Ow X W ∧ cxf vx vw Ox Ow X W ≤ (ux * vw - uw * vx) * m ∧
  0 ≤ cyf ux uw Ox Ow X W ∧ cyf ux uw Ox Ow X W ≤ (ux * vw - uw * vx) * n

section grid
variable {Rt : Tri} {α β : ℝ} {ux uw vx vw : ℝ}

theorem strip_dis (hα : 0 < α) (hβ : 0 < β) (hu : ux ≠ 0 ∨ uw ≠ 0)
    (hcell : ∀ Ox Ow, Dis Rt (CS α β (PgP ux uw vx vw Ox Ow 1 1)) 2) (n : ℕ) :
    ∀ Ox Ow : ℝ, Dis Rt (CS α β (PgP ux uw vx vw Ox Ow 1 ((n + 1 : ℕ) : ℝ))) (2 * (n + 1)) := by
  induction n with
  | zero => intro Ox Ow; exact (hcell Ox Ow).congr (by simp) (by norm_num)
  | succ n ih =>
    intro Ox Ow
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have g := glueR hα hβ (ih Ox Ow)
      (hcell (Ox + ((n + 1 : ℕ) : ℝ) * vx) (Ow + ((n + 1 : ℕ) : ℝ) * vw))
      (Ox + ((n + 1 : ℕ) : ℝ) * vx) (Ow + ((n + 1 : ℕ) : ℝ) * vw)
      (Ox + ((n + 1 : ℕ) : ℝ) * vx + ux) (Ow + ((n + 1 : ℕ) : ℝ) * vw + uw)
      (hu.imp (fun h e => h (by linarith)) (fun h e => h (by linarith)))
      (fun X W h => by
        obtain ⟨a1, a2, a3, a4⟩ := h
        simp only [PgP, cxf, cyf, lnR] at *; push_cast at *; nlinarith)
      (fun X W h => by
        obtain ⟨a1, a2, a3, a4⟩ := h
        simp only [PgP, cxf, cyf, lnR] at *; push_cast at *; nlinarith)
    refine g.congr ?_ (by push_cast; ring)
    ext q
    simp only [CS, Set.mem_setOf_eq]
    constructor
    · rintro (h | h) <;> simp only [PgP, cxf, cyf] at * <;> push_cast at * <;>
        refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [h.1, h.2.1, h.2.2.1, h.2.2.2]
    · intro h
      simp only [PgP, cxf, cyf] at h
      push_cast at h
      rcases le_total (ux * (q 1 / β - Ow) - uw * (q 0 / α - Ox))
        ((ux * vw - uw * vx) * ((n : ℝ) + 1)) with h' | h'
      · left; simp only [PgP, cxf, cyf]; push_cast
        refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [h.1, h.2.1, h.2.2.1, h.2.2.2]
      · right; simp only [PgP, cxf, cyf]; push_cast
        refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [h.1, h.2.1, h.2.2.1, h.2.2.2]

theorem grid_dis (hα : 0 < α) (hβ : 0 < β) (hu : ux ≠ 0 ∨ uw ≠ 0) (hv : vx ≠ 0 ∨ vw ≠ 0)
    (hcell : ∀ Ox Ow, Dis Rt (CS α β (PgP ux uw vx vw Ox Ow 1 1)) 2) (n m : ℕ) :
    ∀ Ox Ow : ℝ, Dis Rt (CS α β (PgP ux uw vx vw Ox Ow ((m + 1 : ℕ) : ℝ) ((n + 1 : ℕ) : ℝ)))
      (2 * (m + 1) * (n + 1)) := by
  induction m with
  | zero => intro Ox Ow; exact (strip_dis hα hβ hu hcell n Ox Ow).congr (by simp) (by ring)
  | succ m ih =>
    intro Ox Ow
    have hn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have g := glueR hα hβ (strip_dis hα hβ hu hcell n (Ox + ((m + 1 : ℕ) : ℝ) * ux)
        (Ow + ((m + 1 : ℕ) : ℝ) * uw)) (ih Ox Ow)
      (Ox + ((m + 1 : ℕ) : ℝ) * ux) (Ow + ((m + 1 : ℕ) : ℝ) * uw)
      (Ox + ((m + 1 : ℕ) : ℝ) * ux + vx) (Ow + ((m + 1 : ℕ) : ℝ) * uw + vw)
      (hv.imp (fun h e => h (by linarith)) (fun h e => h (by linarith)))
      (fun X W h => by
        obtain ⟨a1, a2, a3, a4⟩ := h
        simp only [cxf, cyf, lnR] at *; push_cast at *; nlinarith)
      (fun X W h => by
        obtain ⟨a1, a2, a3, a4⟩ := h
        simp only [cxf, cyf, lnR] at *; push_cast at *; nlinarith)
    refine g.congr ?_ (by push_cast; ring)
    ext q
    simp only [CS, Set.mem_setOf_eq]
    constructor
    · rintro (h | h) <;> simp only [PgP, cxf, cyf] at * <;> push_cast at * <;>
        refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [h.1, h.2.1, h.2.2.1, h.2.2.2]
    · intro h
      simp only [PgP, cxf, cyf] at h
      push_cast at h
      rcases le_total ((q 0 / α - Ox) * vw - (q 1 / β - Ow) * vx)
        ((ux * vw - uw * vx) * ((m : ℝ) + 1)) with h' | h'
      · right; simp only [PgP, cxf, cyf]; push_cast
        refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [h.1, h.2.1, h.2.2.1, h.2.2.2]
      · left; simp only [PgP, cxf, cyf]; push_cast
        refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [h.1, h.2.1, h.2.2.1, h.2.2.2]

/-- the unit cell is two triangles glued along the diagonal -/
theorem cell_of_tris (hα : 0 < α) (hβ : 0 < β) (hδ : 0 < ux * vw - uw * vx)
    (t1 : ∀ Ox Ow, Dis Rt (CS α β (TriR Ox Ow (Ox + ux) (Ow + uw) (Ox + vx) (Ow + vw))) 1)
    (t2 : ∀ Ox Ow, Dis Rt (CS α β (TriR (Ox + ux) (Ow + uw) (Ox + ux + vx) (Ow + uw + vw)
      (Ox + vx) (Ow + vw))) 1) :
    ∀ Ox Ow, Dis Rt (CS α β (PgP ux uw vx vw Ox Ow 1 1)) 2 := by
  intro Ox Ow
  have hne : ux + vx ≠ 0 ∨ uw + vw ≠ 0 ∨ True := Or.inr (Or.inr trivial)
  have hUV : (Ox + ux) ≠ (Ox + vx) ∨ (Ow + uw) ≠ (Ow + vw) := by
    by_contra hc
    push_neg at hc
    obtain ⟨e1, e2⟩ := hc
    have h1 : ux = vx := by linarith
    have h2 : uw = vw := by linarith
    rw [h1, h2] at hδ
    nlinarith
  have g := glueR hα hβ (t2 Ox Ow) (t1 Ox Ow) (Ox + ux) (Ow + uw) (Ox + vx) (Ow + vw) hUV
    (fun X W h => by
      have hD : 0 < detR (Ox + ux) (Ow + uw) (Ox + ux + vx) (Ow + uw + vw) (Ox + vx) (Ow + vw) := by
        simp only [detR]; nlinarith
      rw [show lnR (Ox + ux) (Ow + uw) (Ox + vx) (Ow + vw) X W =
        detR (Ox + ux) (Ow + uw) (Ox + vx) (Ow + vw) X W from rfl]
      refine bary_nonpos hD h ?_ ?_ ?_
      · simp only [detR]; nlinarith
      · simp only [detR]; nlinarith
      · simp only [detR]; nlinarith)
    (fun X W h => by
      have hD : 0 < detR Ox Ow (Ox + ux) (Ow + uw) (Ox + vx) (Ow + vw) := by
        simp only [detR]; nlinarith
      rw [show lnR (Ox + ux) (Ow + uw) (Ox + vx) (Ow + vw) X W =
        detR (Ox + ux) (Ow + uw) (Ox + vx) (Ow + vw) X W from rfl]
      refine bary_nonneg hD h ?_ ?_ ?_
      · simp only [detR]; nlinarith
      · simp only [detR]; nlinarith
      · simp only [detR]; nlinarith)
  refine g.congr ?_ (by norm_num)
  ext q
  simp only [CS, Set.mem_setOf_eq]
  constructor
  · rintro (⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩) <;> simp only [detR, TriR, PgP, cxf, cyf] at * <;>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  · intro h
    simp only [PgP, cxf, cyf] at h
    rcases le_total (((q 0 / α - Ox) * vw - (q 1 / β - Ow) * vx) +
        (ux * (q 1 / β - Ow) - uw * (q 0 / α - Ox))) (ux * vw - uw * vx) with h' | h'
    · right; simp only [detR, TriR]; refine ⟨?_, ?_, ?_⟩ <;> nlinarith [h.1, h.2.2.1]
    · left; simp only [detR, TriR]; refine ⟨?_, ?_, ?_⟩ <;> nlinarith [h.2.1, h.2.2.2]

end grid

/-- the parallelogram `Q, S = Q + mU, R = S + nV, T = Q + nV` as four edge inequalities -/
theorem pgp_iff {ux uw vx vw Qx Qw Sx Sw Rx Rw Tx Tw m n : ℝ} (hm : 0 < m) (hn : 0 < n)
    (hSx : Sx = Qx + m * ux) (hSw : Sw = Qw + m * uw) (hRx : Rx = Sx + n * vx)
    (hRw : Rw = Sw + n * vw) (hTx : Tx = Qx + n * vx) (hTw : Tw = Qw + n * vw) (X W : ℝ) :
    PgP ux uw vx vw Qx Qw m n X W ↔
      (0 ≤ detR Qx Qw Sx Sw X W ∧ 0 ≤ detR Sx Sw Rx Rw X W ∧ 0 ≤ detR Rx Rw Tx Tw X W ∧
        0 ≤ detR Tx Tw Qx Qw X W) := by
  have e1 : detR Qx Qw Sx Sw X W = m * cyf ux uw Qx Qw X W := by
    simp only [detR, cyf, hSx, hSw]; ring
  have e2 : detR Sx Sw Rx Rw X W = n * ((ux * vw - uw * vx) * m - cxf vx vw Qx Qw X W) := by
    simp only [detR, cxf, hSx, hSw, hRx, hRw]; ring
  have e3 : detR Rx Rw Tx Tw X W = m * ((ux * vw - uw * vx) * n - cyf ux uw Qx Qw X W) := by
    simp only [detR, cyf, hSx, hSw, hRx, hRw, hTx, hTw]; ring
  have e4 : detR Tx Tw Qx Qw X W = n * cxf vx vw Qx Qw X W := by
    simp only [detR, cxf, hTx, hTw]; ring
  rw [e1, e2, e3, e4, mul_nonneg_iff_of_pos_left hm, mul_nonneg_iff_of_pos_left hn,
    mul_nonneg_iff_of_pos_left hm, mul_nonneg_iff_of_pos_left hn]
  simp only [PgP]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h3, by linarith, by linarith, h1⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h4, by linarith, h1, by linarith⟩

end Erdos634.BeesonT14Grid

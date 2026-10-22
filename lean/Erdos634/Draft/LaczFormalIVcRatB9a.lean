-- Draft/LaczFormalIVcRatB9a.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, rational branch), BLUEPRINT Part B, item B9, stage a: `corner_cone`.
--   T a VWTiling of a convex A (0 < b), X with area angle pi/3 (hX as in `corner_piece`).  Then there is a Frame F = (X; p, q)
--   (|p| = |q| = b, p.q = b^2/2; p, q the two edges at X of the unique cell through X) with F.pt 0 0 = X and A inside the quadrant
--   {fa >= 0, fb >= 0}; also (interior A) is nonempty.
--   Route: `corner_cell` (one cell c0 through X, X a vertex); the other cells form a closed set missing X, so A near X equals c0 near X;
--   convexity scales a point y of A to X + s (y - X) in c0, and fa, fb are affine with fa X = fb X = 0.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcRatB6
import Erdos634.Draft.LaczFormalIVcRatB8c

open scoped Classical Fin.NatCast
open MeasureTheory
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

theorem convex_fa_ge {b : ℝ} (F : Frame b) (c : ℝ) : Convex ℝ {y : Plane | c ≤ F.fa y} := by
  intro y hy z hz a b' ha hb' hab
  simp only [Set.mem_setOf_eq] at hy hz ⊢
  rw [F.fa_eq] at hy hz ⊢
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hb'' : b' = 1 - a := by linarith
  subst hb''
  nlinarith [mul_le_mul_of_nonneg_left hy ha, mul_le_mul_of_nonneg_left hz hb']

theorem fa_lineMap {b : ℝ} (F : Frame b) (y w : Plane) (s : ℝ) : F.fa (AffineMap.lineMap y w s) = F.fa y + s * (F.fa w - F.fa y) := by
  rw [F.fa_eq, F.fa_eq y, F.fa_eq w, AffineMap.lineMap_apply]
  simp only [vsub_eq_sub, vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  ring

/-- Frame from a cell of side `b` at its vertex `j`. -/
noncomputable def cellFrame {b : ℝ} (hb : 0 < b) (c : Tri) (hc : c.Congruent (eqT b hb)) (j : Fin 3) : Frame b where
  U0 := (c.pts j) 0
  U1 := (c.pts j) 1
  p0 := (c.pts (j + 1)) 0 - (c.pts j) 0
  p1 := (c.pts (j + 1)) 1 - (c.pts j) 1
  q0 := (c.pts (j + 2)) 0 - (c.pts j) 0
  q1 := (c.pts (j + 2)) 1 - (c.pts j) 1
  hp := by
    obtain ⟨h1, _, _⟩ := fin3_ne7 j
    have := dist_sq7 (c.pts (j + 1)) (c.pts j)
    rw [congr_dist_eqT hb hc h1] at this
    linarith
  hq := by
    obtain ⟨_, h2, _⟩ := fin3_ne7 j
    have := dist_sq7 (c.pts (j + 2)) (c.pts j)
    rw [congr_dist_eqT hb hc h2] at this
    linarith
  hpq := by
    obtain ⟨h1, h2, h3⟩ := fin3_ne7 j
    have e1 := dist_sq7 (c.pts (j + 1)) (c.pts j)
    have e2 := dist_sq7 (c.pts (j + 2)) (c.pts j)
    have e3 := dist_sq7 (c.pts (j + 1)) (c.pts (j + 2))
    rw [congr_dist_eqT hb hc h1] at e1
    rw [congr_dist_eqT hb hc h2] at e2
    rw [congr_dist_eqT hb hc h3] at e3
    nlinarith

theorem cellFrame_pt0 {b : ℝ} (hb : 0 < b) (c : Tri) (hc : c.Congruent (eqT b hb)) (j : Fin 3) :
    (cellFrame hb c hc j).pt 0 0 = c.pts j := by
  apply plane_ext' <;> simp [Frame.pt, cellFrame, mkPt]

theorem cellFrame_pt1 {b : ℝ} (hb : 0 < b) (c : Tri) (hc : c.Congruent (eqT b hb)) (j : Fin 3) :
    (cellFrame hb c hc j).pt 1 0 = c.pts (j + 1) := by
  apply plane_ext' <;> simp [Frame.pt, cellFrame, mkPt]

theorem cellFrame_pt2 {b : ℝ} (hb : 0 < b) (c : Tri) (hc : c.Congruent (eqT b hb)) (j : Fin 3) :
    (cellFrame hb c hc j).pt 0 1 = c.pts (j + 2) := by
  apply plane_ext' <;> simp [Frame.pt, cellFrame, mkPt]

theorem fin3_cases_j (j n : Fin 3) : n = j ∨ n = j + 1 ∨ n = j + 2 := by revert j n; decide

/-- A cell lies in the quadrant of its own corner frame. -/
theorem cell_quadrant {b : ℝ} (hb : 0 < b) (c : Tri) (hc : c.Congruent (eqT b hb)) (j : Fin 3) :
    ∀ y ∈ c.carrier, 0 ≤ (cellFrame hb c hc j).fa y ∧ 0 ≤ (cellFrame hb c hc j).fb y := by
  set F := cellFrame hb c hc j with hF
  have hcv : Convex ℝ ({y : Plane | 0 ≤ F.fa y} ∩ {y : Plane | 0 ≤ F.fb y}) := (convex_fa_ge F 0).inter (convex_fb_ge F 0)
  have hsub : c.carrier ⊆ {y : Plane | 0 ≤ F.fa y} ∩ {y : Plane | 0 ≤ F.fb y} := by
    refine convexHull_min ?_ hcv
    rintro _ ⟨n, rfl⟩
    have hn := fin3_cases_j j n
    rcases hn with rfl | rfl | rfl
    · rw [← cellFrame_pt0 hb c hc n]
      simp [← hF, F.fa_pt hb, F.fb_pt hb]
    · rw [← cellFrame_pt1 hb c hc j]
      simp [← hF, F.fa_pt hb, F.fb_pt hb]
    · rw [← cellFrame_pt2 hb c hc j]
      simp [← hF, F.fa_pt hb, F.fb_pt hb]
  exact fun y hy => hsub hy

namespace VWTiling
variable {b : ℝ} {A : Set Plane} {ιK ιR : Type} [Fintype ιK] [Fintype ιR] (T : VWTiling b A ιK ιR)

include T in
/-- **B9a (corner cone).** -/
theorem corner_cone (hb : 0 < b) (hconv : Convex ℝ A) {X : Plane} {ρ : ℝ} (hρ : 0 < ρ)
    (hX : ∀ r, 0 < r → r ≤ ρ → volume (A ∩ Metric.ball X r) = ENNReal.ofReal (Real.pi / 3 / 2 * r ^ 2)) :
    ∃ F : Frame b, F.pt 0 0 = X ∧ (∀ y ∈ A, 0 ≤ F.fa y ∧ 0 ≤ F.fb y) ∧ (interior A).Nonempty := by
  obtain ⟨c0, ⟨j, hXj⟩, U⟩ := T.corner_cell hb hρ hX
  have hc := T.cell_congruent hb
  have hsubA : ∀ c, (T.cellT c).carrier ⊆ A := fun c =>
    (Set.subset_iUnion (fun c => (T.cellT c).carrier) c).trans T.cells_cover.subset
  set F := cellFrame hb (T.cellT c0) (hc c0) j with hF
  have hF0 : F.pt 0 0 = X := by rw [hF, cellFrame_pt0, hXj]
  have hXA : X ∈ A := by
    rw [hXj]; exact hsubA c0 (pts_mem _ _)
  -- other cells form a closed set missing X
  have hclosed : IsClosed (⋃ c : {c // c ≠ c0}, (T.cellT c.1).carrier) :=
    isClosed_iUnion_of_finite fun c => (T.cellT c.1).isCompact.isClosed
  have hXnot : X ∉ ⋃ c : {c // c ≠ c0}, (T.cellT c.1).carrier := by
    intro h
    obtain ⟨⟨c, hne⟩, hmem⟩ := Set.mem_iUnion.mp h
    exact hne (U c hmem)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl X hXnot
  have hloc : ∀ z ∈ A, dist z X < ε → z ∈ (T.cellT c0).carrier := by
    intro z hzA hz
    have hz' := hzA
    rw [← T.cells_cover] at hz'
    obtain ⟨c, hc'⟩ := Set.mem_iUnion.mp hz'
    by_cases hcc : c = c0
    · rw [← hcc]; exact hc'
    · exfalso
      have : z ∈ (⋃ c : {c // c ≠ c0}, (T.cellT c.1).carrier)ᶜ := hball (Metric.mem_ball.mpr hz)
      exact this (Set.mem_iUnion.mpr ⟨⟨c, hcc⟩, hc'⟩)
  refine ⟨F, hF0, ?_, ?_⟩
  · intro y hyA
    set s : ℝ := min 1 (ε / (2 * (dist X y + 1))) with hs
    have hsp : 0 < s := lt_min one_pos (by positivity)
    have hs1 : s ≤ 1 := min_le_left _ _
    have hzA : AffineMap.lineMap X y s ∈ A := hconv.lineMap_mem hXA hyA ⟨hsp.le, hs1⟩
    have hd : dist (AffineMap.lineMap X y s) X < ε := by
      rw [dist_lineMap_left, Real.norm_eq_abs, abs_of_pos hsp]
      have h1 : s * dist X y ≤ ε / (2 * (dist X y + 1)) * dist X y :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) dist_nonneg
      have h2 : ε / (2 * (dist X y + 1)) * dist X y < ε := by
        have hd0 := dist_nonneg (x := X) (y := y)
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
      linarith
    obtain ⟨h1, h2⟩ := cell_quadrant hb _ (hc c0) j _ (hloc _ hzA hd)
    have e0 : F.fa X = 0 := by rw [← hF0, F.fa_pt hb]
    have e1 : F.fb X = 0 := by rw [← hF0, F.fb_pt hb]
    rw [fa_lineMap, e0] at h1
    rw [fb_lineMap, e1] at h2
    constructor <;> nlinarith
  · exact ⟨_, Set.mem_of_mem_of_subset (T.cellT c0).interior_nonempty.choose_spec (interior_mono (hsubA c0))⟩

end VWTiling

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.VWTiling.corner_cone

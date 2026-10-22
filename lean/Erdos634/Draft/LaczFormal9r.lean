import Erdos634.Draft.LaczFormal9q

/-!
# Laczkovich DM 140 (1995), Theorem 2.3: the four tiles and the trapezoid of Fig. 3 are rational triangles similar to `Δ`

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.3, Fig. 3, Lemma 2.2 (iii)), Beeson, Beeson-Zhang, Zhang.
Formalization debt, not /goal progress.

`Δ = R` is a rational triangle with `R.b = 2 k R.a`, `R.c = (4k² - 1) R.a` (`k = cos α` rational, `1/2 < k < 1`; the angles at the vertices
`0, 1, 2` are `α, 2α, π - 3α`).  Chart `(G; w = GE, d = GA)` with `|w| = W = a(c²+1)/c`, `|d| = D = a/(2kc)`, `⟨w,d⟩ = W D k`, `c = 4k² - 1`.
The tiles `ABC, BCD, BDE, DEF` of `LaczFormal9o` have squared sides `ρ²·(a², b², c²)` with `ρ = 1, 1/c, 1/(2kc), 1/(2k)` (checked
by `field_simp; ring`); the trapezoid `GEBA` is Lemma 2.2 (iii) (`trap_iii`) for the relabelled triangle `R.sw01`.
-/

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL24 Erdos634.LaczL21 Erdos634.Realizable
  Erdos634.Laczkovich9n Erdos634.Laczkovich9o

namespace Erdos634.Laczkovich9r

noncomputable def cR (k : ℚ) : ℝ := ((4 * k ^ 2 - 1 : ℚ) : ℝ)
def qW (ra k : ℚ) : ℚ := ra * ((4 * k ^ 2 - 1) ^ 2 + 1) / (4 * k ^ 2 - 1)
def qD (ra k : ℚ) : ℚ := ra / (2 * k * (4 * k ^ 2 - 1))
def qG (ra k : ℚ) : ℚ := qW ra k * qD ra k * k

theorem cR_eq (k : ℚ) : cR k = 4 * (k : ℝ) ^ 2 - 1 := by unfold cR; push_cast; ring

theorem cR_pos {k : ℚ} (hk : (1 : ℚ) / 2 < k) : 0 < cR k := by
  unfold cR
  have : (0 : ℚ) < 4 * k ^ 2 - 1 := by nlinarith
  exact_mod_cast this

local macro "tcl" : tactic =>
  `(tactic| (simp only [wt, wh, wp, wq, wf, cR_eq]; push_cast; field_simp; ring))

section tiles
variable (R : RTri) (k : ℚ) (hk : (1 : ℚ) / 2 < k)
  (hB : R.b = 2 * k * R.a) (hC : R.c = (4 * k ^ 2 - 1) * R.a)
  (A w d : Plane) (h : w 0 * d 1 - w 1 * d 0 ≠ 0)
  (hw : inner ℝ w w = ((qW R.a k : ℚ) : ℝ) ^ 2) (hd : inner ℝ d d = ((qD R.a k : ℚ) : ℝ) ^ 2)
  (hwd : inner ℝ w d = ((qG R.a k : ℚ) : ℝ))

private theorem e_swap0 : (Equiv.swap (0 : Fin 3) 1) 0 = 1 := by decide
private theorem e_swap1 : (Equiv.swap (0 : Fin 3) 1) 1 = 0 := by decide
private theorem e_swap2 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
private theorem e_rot0 : (finRotate 3) 0 = 1 := by decide
private theorem e_rot1 : (finRotate 3) 1 = 2 := by decide
private theorem e_rot2 : (finRotate 3) 2 = 0 := by decide
private theorem e_rs0 : (finRotate 3).symm 0 = 2 := by decide
private theorem e_rs1 : (finRotate 3).symm 1 = 0 := by decide
private theorem e_rs2 : (finRotate 3).symm 2 = 1 := by decide

/-- Real forms of the side relations. -/
theorem real_facts (R : RTri) (k : ℚ) (hB : R.b = 2 * k * R.a) (hC : R.c = (4 * k ^ 2 - 1) * R.a) :
    (R.b : ℝ) = 2 * (k : ℝ) * (R.a : ℝ) ∧ (R.c : ℝ) = (4 * (k : ℝ) ^ 2 - 1) * (R.a : ℝ) ∧
    ((qW R.a k : ℚ) : ℝ) = (R.a : ℝ) * ((4 * (k : ℝ) ^ 2 - 1) ^ 2 + 1) / (4 * (k : ℝ) ^ 2 - 1) ∧
    ((qD R.a k : ℚ) : ℝ) = (R.a : ℝ) / (2 * (k : ℝ) * (4 * (k : ℝ) ^ 2 - 1)) ∧
    ((qG R.a k : ℚ) : ℝ) = (R.a : ℝ) * ((4 * (k : ℝ) ^ 2 - 1) ^ 2 + 1) / (4 * (k : ℝ) ^ 2 - 1)
      * ((R.a : ℝ) / (2 * (k : ℝ) * (4 * (k : ℝ) ^ 2 - 1))) * k := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hB]; push_cast; ring
  · rw [hC]; push_cast; ring
  · unfold qW; push_cast; ring
  · unfold qD; push_cast; ring
  · unfold qG qW qD; push_cast; ring

include hk hB hC hw hd hwd

theorem tile_ABC :
    RatSimTile R.Δ (Erdos634.DissectionMap.mapTri (chartEquiv A w d h) (triABC (cR k) (cR_pos hk))) := by
  obtain ⟨rb, rc, rW, rD, rG⟩ := real_facts R k hB hC
  have hcp := cR_pos hk
  have hc0 : (4 * (k : ℝ) ^ 2 - 1) ≠ 0 := by rw [← cR_eq]; exact hcp.ne'
  have hk0 : (k : ℝ) ≠ 0 := by
    have : (0 : ℝ) < k := by have : (0 : ℚ) < k := by linarith
                             exact_mod_cast this
    exact this.ne'
  have hra : (R.a : ℝ) ≠ 0 := by exact_mod_cast R.pa.ne'
  have hn0 : (4 * (k : ℝ) ^ 2 - 1) ^ 2 + 1 ≠ 0 := by positivity
  have hn1 : (cR k) ^ 2 + 1 ≠ 0 := by positivity
  unfold triABC
  refine chart_tile R A w d h (qW R.a k) (qD R.a k) hw hd _ hwd _ _ _ _ _ _ _ (Equiv.refl (Fin 3)) 1 one_pos ?_ ?_ ?_
  · show _ = _ * dist (R.Δ.pts 0) (R.Δ.pts 1) ^ 2
    rw [R.hc, rc, rW, rD, rG]
    tcl
  · show _ = _ * dist (R.Δ.pts 1) (R.Δ.pts 2) ^ 2
    rw [R.ha, rW, rD, rG]
    tcl
  · show _ = _ * dist (R.Δ.pts 2) (R.Δ.pts 0) ^ 2
    rw [R.hb, rb, rW, rD, rG]
    tcl

theorem tile_BCD :
    RatSimTile R.Δ (Erdos634.DissectionMap.mapTri (chartEquiv A w d h) (triBCD (cR k) (cR_pos hk))) := by
  obtain ⟨rb, rc, rW, rD, rG⟩ := real_facts R k hB hC
  have hcp := cR_pos hk
  have hc0 : (4 * (k : ℝ) ^ 2 - 1) ≠ 0 := by rw [← cR_eq]; exact hcp.ne'
  have hk0 : (k : ℝ) ≠ 0 := by
    have : (0 : ℝ) < k := by have : (0 : ℚ) < k := by linarith
                             exact_mod_cast this
    exact this.ne'
  have hra : (R.a : ℝ) ≠ 0 := by exact_mod_cast R.pa.ne'
  have hn0 : (4 * (k : ℝ) ^ 2 - 1) ^ 2 + 1 ≠ 0 := by positivity
  have hn1 : (cR k) ^ 2 + 1 ≠ 0 := by positivity
  have hcq : (0 : ℚ) < 4 * k ^ 2 - 1 := by nlinarith
  unfold triBCD
  refine chart_tile R A w d h (qW R.a k) (qD R.a k) hw hd _ hwd _ _ _ _ _ _ _ (Equiv.swap 0 1)
    (1 / (4 * k ^ 2 - 1)) (by positivity) ?_ ?_ ?_
  · show _ = _ * dist (R.Δ.pts ((Equiv.swap 0 1) 0)) (R.Δ.pts ((Equiv.swap 0 1) 1)) ^ 2
    rw [e_swap0, e_swap1, dist_comm (R.Δ.pts 1) (R.Δ.pts 0), R.hc, rc, rW, rD, rG]
    tcl
  · show _ = _ * dist (R.Δ.pts ((Equiv.swap 0 1) 1)) (R.Δ.pts ((Equiv.swap 0 1) 2)) ^ 2
    rw [e_swap1, e_swap2, dist_comm (R.Δ.pts 0) (R.Δ.pts 2), R.hb, rb, rW, rD, rG]
    tcl
  · show _ = _ * dist (R.Δ.pts ((Equiv.swap 0 1) 2)) (R.Δ.pts ((Equiv.swap 0 1) 0)) ^ 2
    rw [e_swap2, e_swap0, dist_comm (R.Δ.pts 2) (R.Δ.pts 1), R.ha, rW, rD, rG]
    tcl

theorem tile_BDE :
    RatSimTile R.Δ (Erdos634.DissectionMap.mapTri (chartEquiv A w d h) (triBDE (cR k) (cR_pos hk))) := by
  obtain ⟨rb, rc, rW, rD, rG⟩ := real_facts R k hB hC
  have hcp := cR_pos hk
  have hc0 : (4 * (k : ℝ) ^ 2 - 1) ≠ 0 := by rw [← cR_eq]; exact hcp.ne'
  have hk0 : (k : ℝ) ≠ 0 := by
    have : (0 : ℝ) < k := by have : (0 : ℚ) < k := by linarith
                             exact_mod_cast this
    exact this.ne'
  have hra : (R.a : ℝ) ≠ 0 := by exact_mod_cast R.pa.ne'
  have hn0 : (4 * (k : ℝ) ^ 2 - 1) ^ 2 + 1 ≠ 0 := by positivity
  have hn1 : (cR k) ^ 2 + 1 ≠ 0 := by positivity
  have hcq : (0 : ℚ) < 4 * k ^ 2 - 1 := by nlinarith
  have hkq : (0 : ℚ) < k := by linarith
  unfold triBDE
  refine chart_tile R A w d h (qW R.a k) (qD R.a k) hw hd _ hwd _ _ _ _ _ _ _ (finRotate 3).symm
    (1 / (2 * k * (4 * k ^ 2 - 1))) (by positivity) ?_ ?_ ?_
  · show _ = _ * dist (R.Δ.pts ((finRotate 3).symm 0)) (R.Δ.pts ((finRotate 3).symm 1)) ^ 2
    rw [e_rs0, e_rs1, R.hb, rb, rW, rD, rG]
    tcl
  · show _ = _ * dist (R.Δ.pts ((finRotate 3).symm 1)) (R.Δ.pts ((finRotate 3).symm 2)) ^ 2
    rw [e_rs1, e_rs2, R.hc, rc, rW, rD, rG]
    tcl
  · show _ = _ * dist (R.Δ.pts ((finRotate 3).symm 2)) (R.Δ.pts ((finRotate 3).symm 0)) ^ 2
    rw [e_rs2, e_rs0, R.ha, rW, rD, rG]
    tcl

theorem tile_DEF :
    RatSimTile R.Δ (Erdos634.DissectionMap.mapTri (chartEquiv A w d h) (triDEF (cR k) (cR_pos hk))) := by
  obtain ⟨rb, rc, rW, rD, rG⟩ := real_facts R k hB hC
  have hcp := cR_pos hk
  have hc0 : (4 * (k : ℝ) ^ 2 - 1) ≠ 0 := by rw [← cR_eq]; exact hcp.ne'
  have hk0 : (k : ℝ) ≠ 0 := by
    have : (0 : ℝ) < k := by have : (0 : ℚ) < k := by linarith
                             exact_mod_cast this
    exact this.ne'
  have hra : (R.a : ℝ) ≠ 0 := by exact_mod_cast R.pa.ne'
  have hn0 : (4 * (k : ℝ) ^ 2 - 1) ^ 2 + 1 ≠ 0 := by positivity
  have hn1 : (cR k) ^ 2 + 1 ≠ 0 := by positivity
  have hkq : (0 : ℚ) < k := by linarith
  unfold triDEF
  refine chart_tile R A w d h (qW R.a k) (qD R.a k) hw hd _ hwd _ _ _ _ _ _ _ (finRotate 3)
    (1 / (2 * k)) (by positivity) ?_ ?_ ?_
  · show _ = _ * dist (R.Δ.pts ((finRotate 3) 0)) (R.Δ.pts ((finRotate 3) 1)) ^ 2
    rw [e_rot0, e_rot1, R.ha, rW, rD, rG]
    tcl
  · show _ = _ * dist (R.Δ.pts ((finRotate 3) 1)) (R.Δ.pts ((finRotate 3) 2)) ^ 2
    rw [e_rot1, e_rot2, R.hb, rb, rW, rD, rG]
    tcl
  · show _ = _ * dist (R.Δ.pts ((finRotate 3) 2)) (R.Δ.pts ((finRotate 3) 0)) ^ 2
    rw [e_rot2, e_rot0, R.hc, rc, rW, rD, rG]
    tcl

end tiles

end Erdos634.Laczkovich9r

#print axioms Erdos634.Laczkovich9r.tile_ABC

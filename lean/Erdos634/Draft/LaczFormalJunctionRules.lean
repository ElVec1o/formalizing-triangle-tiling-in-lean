import Erdos634.Draft.LaczFormalJunctionTok

/-!
# Band junction rules S, E, I, Im, stated for tokens

Erdős #634, base-`β` band.  Credit: AI assistant (band lemma / item-3 proposal), Beeson–Roșu, Beeson,
Laczkovich, Paliy.  Token semantics: see `LaczFormalJunctionTok.lean`.

* `band_S_tok`: no tiling has base word beginning `cBA, bGA`.
* `band_E_tok`: no tiling has base word ending `bAG, cAB`.  Proved from `band_S_tok` by reflecting
  the base (`BaseTok.reflect`), swapping the roles of the two base corners.
* `band_I_tok`: no tiling has `X, cBA, bGA` consecutive, `X ∈ {cAB, bAG}` (any token whose right
  angle is `β` or `γ`), `cBA` not at the corner.
* `band_Im_tok`: no tiling has `bAG, cAB, Y` consecutive, `Y` a token whose left angle is `β` or
  `γ`.  Proved from `band_I_tok` by reflection.

The vertex labelling of the tiles is arbitrary (`TileVerts`); the case of the opposite cyclic
orientation is reduced to the oriented one by `CongruentDissection.revAt`.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.LaczJunction

open Erdos634.Geometry Erdos634.TilePlacement

variable {N : ℕ}

def angOf (α β γ : ℝ) : Corner → ℝ | .A => α | .B => β | .G => γ
def lenOf (a b c : ℝ) : Side → ℝ | .a => a | .b => b | .c => c

theorem edge_of_verts {T : Tri} {P E Z : Plane} (h : TileVerts T P E Z) :
    ∃ j : Fin 3, (T.pts j = P ∧ T.pts (j+1) = E) ∨ (T.pts j = E ∧ T.pts (j+1) = P) := by
  obtain ⟨j, h | h⟩ := h
  · exact ⟨j, Or.inl ⟨h.1, h.2.1⟩⟩
  · refine ⟨j+2, Or.inr ⟨h.2.2, ?_⟩⟩
    have : j + 2 + 1 = j := by fin_cases j <;> rfl
    rw [this]; exact h.1

/-- **Rule S** (base word begins `cBA, bGA`). -/
theorem band_S_tok (D : CongruentDissection N) (e f : ℕ) (he : 1 ≤ e)
    (hef : e < f) (hcop : Nat.Coprime e f) (α β γ : ℝ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hα0 : 0 < α) (hβ0 : 0 < β)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hsa : sideOpp D.model 0 = (ta e f : ℝ)) (hsb : sideOpp D.model 1 = (tb e f : ℝ))
    (hsc : sideOpp D.model 2 = (tc e f : ℝ))
    {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hcB : (tc e f : ℝ) < dist (D.target.pts p) (D.target.pts q))
    (haL : (ta e f : ℝ) < dist (D.target.pts p) (D.target.pts r))
    {P G E Z2 : Plane} (i1 i2 : Fin N) (hne : i2 ≠ i1)
    (t1 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .c .B .A i1
      (D.target.pts p) P G)
    (hGl : G ∈ segment ℝ (D.target.pts p) (D.target.pts r))
    (t2 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .b .G .A i2 P E Z2) :
    False := by
  classical
  obtain ⟨j2, hj2⟩ := edge_of_verts t2.verts
  have hb2 : dist ((D.tile i2).pts j2) ((D.tile i2).pts (j2+1)) = (tb e f : ℝ) := by
    have := t2.length
    simp only [lenOf] at this
    rcases hj2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact this
    · rw [h1, h2, dist_comm]; exact this
  have hb2P : ((D.tile i2).pts j2 = P ∧
        (D.tile i2).pts (j2+1) ∈ segment ℝ (D.target.pts p) (D.target.pts q)) ∨
      ((D.tile i2).pts (j2+1) = P ∧
        (D.tile i2).pts j2 ∈ segment ℝ (D.target.pts p) (D.target.pts q)) := by
    rcases hj2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, by rw [h2]; exact t2.right_mem⟩
    · exact Or.inr ⟨h2, by rw [h1]; exact t2.right_mem⟩
  have hγ2 : (D.tile i2).localAngle P = γ := t2.left_angle
  have hα1 : (D.tile i1).localAngle P = α := t1.right_angle
  have hβ1 : (D.tile i1).localAngle (D.target.pts p) = β := t1.left_angle
  have hPb := t1.right_mem
  have hv : TileVerts (D.tile i1) P G (D.target.pts p) := t1.verts.swap12.swap23
  rcases hv.oriented with ⟨j1, hP, hG, hQ⟩ | ⟨j1, hP, hG, hQ⟩
  · exact band_S_word D e f he hef hcop α β γ hγdef hrel hirr hα0 hβ0 hα' hβ' hγ' hsa hsb hsc
      hpq hpr hqr hcB haL i1 j1 hQ hP hG hPb hGl hα1 hβ1 i2 j2 hb2P hb2 hγ2
  · refine band_S_word (D.revAt i1) e f he hef hcop α β γ hγdef hrel hirr hα0 hβ0 hα' hβ' hγ'
      hsa hsb hsc hpq hpr hqr hcB haL i1 j1 ?_ ?_ ?_ hPb hGl ?_ ?_ i2 j2 ?_ ?_ ?_
    · rw [revAt_tile_self]; exact hQ
    · rw [revAt_tile_self]; exact hP
    · rw [revAt_tile_self]; exact hG
    · rw [revAt_tile_self, rev_localAngle]; exact hα1
    · rw [revAt_tile_self, rev_localAngle]; exact hβ1
    · rw [revAt_tile_ne D hne]; exact hb2P
    · rw [revAt_tile_ne D hne]; exact hb2
    · rw [revAt_tile_ne D hne]; exact hγ2

/-- **Rule E** (base word ends `bAG, cAB`): the reflection of rule S.  The base is read from the
other corner `pts q`; `cAB` is `cBA` seen from that end, `bAG` is `bGA`. -/
theorem band_E_tok (D : CongruentDissection N) (e f : ℕ) (he : 1 ≤ e)
    (hef : e < f) (hcop : Nat.Coprime e f) (α β γ : ℝ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hα0 : 0 < α) (hβ0 : 0 < β)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hsa : sideOpp D.model 0 = (ta e f : ℝ)) (hsb : sideOpp D.model 1 = (tb e f : ℝ))
    (hsc : sideOpp D.model 2 = (tc e f : ℝ))
    {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hcB : (tc e f : ℝ) < dist (D.target.pts p) (D.target.pts q))
    (haR : (ta e f : ℝ) < dist (D.target.pts q) (D.target.pts r))
    {P G E Z2 : Plane} (i1 i2 : Fin N) (hne : i2 ≠ i1)
    (t2 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .b .A .G i2 E P Z2)
    (t1 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .c .A .B i1
      P (D.target.pts q) G)
    (hGr : G ∈ segment ℝ (D.target.pts q) (D.target.pts r)) : False := by
  have hcB' : (tc e f : ℝ) < dist (D.target.pts q) (D.target.pts p) := by
    rw [dist_comm]; exact hcB
  exact band_S_tok D e f he hef hcop α β γ hγdef hrel hirr hα0 hβ0 hα' hβ' hγ' hsa hsb hsc
    hpq.symm hqr hpr hcB' haR i1 i2 hne t1.reflect hGr t2.reflect

/-- Three points of a segment in increasing distance from its start: the first lies on the opposite
side of the second from the third. -/
theorem neg_ratio {A B Y Q P : Plane} (hY : Y ∈ segment ℝ A B) (hQ : Q ∈ segment ℝ A B)
    (hP : P ∈ segment ℝ A B) (h1 : dist A Y < dist A Q) (h2 : dist A Q < dist A P) :
    ∃ s : ℝ, 0 < s ∧ Y - Q = (-s) • (P - Q) := by
  rw [segment_eq_image_lineMap] at hY hQ hP
  obtain ⟨ty, ⟨hy0, hy1⟩, rfl⟩ := hY
  obtain ⟨tq, ⟨hq0, hq1⟩, rfl⟩ := hQ
  obtain ⟨tp, ⟨hp0, hp1⟩, rfl⟩ := hP
  simp only [dist_left_lineMap, Real.norm_eq_abs, abs_of_nonneg hy0, abs_of_nonneg hq0,
    abs_of_nonneg hp0] at h1 h2
  have hd : 0 < dist A B := by
    rcases (dist_nonneg (x := A) (y := B)).lt_or_eq with h | h
    · exact h
    · rw [← h] at h1; simp at h1
  have hyq : ty < tq := lt_of_mul_lt_mul_right h1 hd.le
  have hqp : tq < tp := lt_of_mul_lt_mul_right h2 hd.le
  refine ⟨(tq - ty) / (tp - tq), div_pos (by linarith) (by linarith), ?_⟩
  have hne : tp - tq ≠ 0 := by linarith
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  have key : (-((tq - ty) / (tp - tq))) • ((tp • (B - A) + A) - (tq • (B - A) + A)) =
      ((-((tq - ty) / (tp - tq))) * (tp - tq)) • (B - A) := by
    rw [mul_smul]; congr 1; module
  rw [key]
  have : (-((tq - ty) / (tp - tq))) * (tp - tq) = ty - tq := by field_simp; ring
  rw [this]; module

/-- **Rule I** (`X, cBA, bGA` consecutive, `cBA` not at the corner). -/
theorem band_I_tok (D : CongruentDissection N) (e f : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hband : ta e f < tb e f) (α β γ : ℝ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hα0 : 0 < α) (hβ0 : 0 < β)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hsa : sideOpp D.model 0 = (ta e f : ℝ)) (hsb : sideOpp D.model 1 = (tb e f : ℝ))
    (hsc : sideOpp D.model 2 = (tc e f : ℝ))
    {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {Y Q P G E Zx Z2 : Plane} (i1 i2 iX : Fin N) (hne2 : i2 ≠ i1) (hneX : iX ≠ i1)
    (xs : Side) (lX rX : Corner) (hrX : rX = .B ∨ rX = .G)
    (tX : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) xs lX rX iX Y Q Zx)
    (t1 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .c .B .A i1 Q P G)
    (t2 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .b .G .A i2 P E Z2) :
    False := by
  classical
  -- positions on the base
  have hEle : dist (D.target.pts p) E ≤ dist (D.target.pts p) (D.target.pts q) := by
    have e2 : dist (D.target.pts p) E + dist E (D.target.pts q) =
        dist (D.target.pts p) (D.target.pts q) :=
      dist_add_dist_eq_iff.mpr (mem_segment_iff_wbtw.mp t2.right_mem)
    have := dist_nonneg (x := E) (y := D.target.pts q)
    linarith
  have hQopen : Q ∈ openSegment ℝ (D.target.pts p) (D.target.pts q) :=
    openSegment_of_dist t1.left_mem
      (lt_of_le_of_lt dist_nonneg tX.order) (by linarith [t1.order, t2.order])
  have hPopen : P ∈ openSegment ℝ (D.target.pts p) (D.target.pts q) :=
    openSegment_of_dist t1.right_mem
      (lt_trans (lt_of_le_of_lt dist_nonneg tX.order) t1.order) (by linarith [t2.order])
  obtain ⟨s, hs, hYQ⟩ := neg_ratio tX.left_mem t1.left_mem t1.right_mem tX.order t1.order
  -- the tile `X`
  obtain ⟨kX, mX, hXQ, hXY, hmk⟩ : ∃ kX mX : Fin 3, (D.tile iX).pts kX = Q ∧
      (D.tile iX).pts mX = Y ∧ mX ≠ kX := by
    obtain ⟨j, h | h⟩ := tX.verts
    · exact ⟨j+1, j, h.2.1, h.1, by fin_cases j <;> decide⟩
    · exact ⟨j+2, j, h.2.2, h.1, by fin_cases j <;> decide⟩
  have hXang : (D.tile iX).localAngle Q = β ∨ (D.tile iX).localAngle Q = γ := by
    have := tX.right_angle
    rcases hrX with rfl | rfl
    · exact Or.inl this
    · exact Or.inr this
  -- the tile `bGA`
  obtain ⟨j2, hj2⟩ := edge_of_verts t2.verts
  have hb2 : dist ((D.tile i2).pts j2) ((D.tile i2).pts (j2+1)) = (tb e f : ℝ) := by
    have := t2.length
    simp only [lenOf] at this
    rcases hj2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact this
    · rw [h1, h2, dist_comm]; exact this
  have hb2a : D.target.basis.coord r ((D.tile i2).pts j2) = 0 := by
    rcases hj2 with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1]; exact segment_coord_zero D.target hpr hqr t1.right_mem
    · rw [h1]; exact segment_coord_zero D.target hpr hqr t2.right_mem
  have hb2b : D.target.basis.coord r ((D.tile i2).pts (j2+1)) = 0 := by
    rcases hj2 with ⟨_, h2⟩ | ⟨_, h2⟩
    · rw [h2]; exact segment_coord_zero D.target hpr hqr t2.right_mem
    · rw [h2]; exact segment_coord_zero D.target hpr hqr t1.right_mem
  have hγ2 : (D.tile i2).localAngle P = γ := t2.left_angle
  have hα1 : (D.tile i1).localAngle P = α := t1.right_angle
  have hβ1 : (D.tile i1).localAngle Q = β := t1.left_angle
  have hv : TileVerts (D.tile i1) P G Q := t1.verts.swap12.swap23
  rcases hv.oriented with ⟨j1, hP, hG, hQ⟩ | ⟨j1, hP, hG, hQ⟩
  · exact band_I_word D e f he hef hcop hband α β γ hγdef hrel hirr hα0 hβ0 hα' hβ' hγ' hsa hsb hsc
      hpq hpr hqr hPopen hQopen i1 j1 hP hG hQ hα1 hβ1 iX kX mX Y hXQ hXY hmk s hs hYQ hneX hXang
      i2 j2 hγ2 hb2 hb2a hb2b
  · refine band_I_word (G := G) (D.revAt i1) e f he hef hcop hband α β γ hγdef hrel hirr hα0 hβ0 hα' hβ'
      hγ' hsa hsb hsc hpq hpr hqr hPopen hQopen i1 j1 ?_ ?_ ?_ ?_ ?_ iX kX mX Y ?_ ?_ hmk s hs hYQ
      hneX ?_ i2 j2 ?_ ?_ ?_ ?_
    · rw [revAt_tile_self]; exact hP
    · rw [revAt_tile_self]; exact hG
    · rw [revAt_tile_self]; exact hQ
    · rw [revAt_tile_self, rev_localAngle]; exact hα1
    · rw [revAt_tile_self, rev_localAngle]; exact hβ1
    · rw [revAt_tile_ne D hneX]; exact hXQ
    · rw [revAt_tile_ne D hneX]; exact hXY
    · show ((D.revAt i1).tile iX).localAngle Q = β ∨ ((D.revAt i1).tile iX).localAngle Q = γ
      rw [revAt_tile_ne D hneX]; exact hXang
    · rw [revAt_tile_ne D hne2]; exact hγ2
    · rw [revAt_tile_ne D hne2]; exact hb2
    · rw [revAt_tile_ne D hne2]; exact hb2a
    · rw [revAt_tile_ne D hne2]; exact hb2b

/-- **Rule Im** (`bAG, cAB, Y` consecutive): the reflection of rule I. -/
theorem band_Im_tok (D : CongruentDissection N) (e f : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hband : ta e f < tb e f) (α β γ : ℝ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hα0 : 0 < α) (hβ0 : 0 < β)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hsa : sideOpp D.model 0 = (ta e f : ℝ)) (hsb : sideOpp D.model 1 = (tb e f : ℝ))
    (hsc : sideOpp D.model 2 = (tc e f : ℝ))
    {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {Y Q P G E Zy Z2 : Plane} (i1 i2 iY : Fin N) (hne2 : i2 ≠ i1) (hneY : iY ≠ i1)
    (ys : Side) (lY rY : Corner) (hlY : lY = .B ∨ lY = .G)
    (t2 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .b .A .G i2 E P Z2)
    (t1 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .c .A .B i1 P Q G)
    (tY : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) ys lY rY iY Q Y Zy) :
    False :=
  band_I_tok D e f he hef hcop hband α β γ hγdef hrel hirr hα0 hβ0 hα' hβ' hγ' hsa hsb hsc
    hpq.symm hqr hpr i1 i2 iY hne2 hneY ys rY lY (by rcases hlY with h | h <;> simp [h])
    tY.reflect t1.reflect t2.reflect

#print axioms band_S_tok
#print axioms band_E_tok
#print axioms band_I_tok
#print axioms band_Im_tok

end Erdos634.LaczJunction

-- Draft/ApexR2Frame.lean — the mirror-branch frame `MirrorStripR2Glue.R2Frame` from a REAL
-- congruent dissection of the m = 1 base-β target in branch (M).  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- `split_real`: every real m = 1 dissection (`ApexFrameReal.M1Data`) carries an apex frame `F`
-- (`HFrame`) and is either in branch (H) (`Present D F.K`) or carries the mirror frame `R2Frame` of
-- branch (M) — Lemma G's (H)/(M) split (`TileIdent.lemmaG_frame`) composed with
-- `r2frame_of_mirror`, which builds every `R2Frame` field from the apex frame, its cone coordinates
-- (`ApexPlacement.FrameCoords`) and the mirror tile.  New metric content: the mirror `M` of `A`
-- across `VP′` is `P′ + b·uL` (two-circle uniqueness, `EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_
-- finrank_eq_two`, plus the Gram identity `mirror_alg`); the line `L = P′ + ℝuL` leaves the target at
-- `Q_{f−1}` (cone coordinates sum `1/f + x/f³`); `g(P′) < g(V)` is `b < 2f² − e²`.
--
-- REDISCOVERY: `A* = P′ + b·uL` (the mirror of A across VP′ lies on L) and `L` meets the base at
-- `Q_{f−1}` are `MirrorStripR2.pAstar_mirror`, `pAstar_eq_pQ`, `pQ_on_base_iff`, `Qbase_on_base` in
-- fixed coordinates (P32); here they are re-derived for the frame of an arbitrary real dissection.
--
-- Build: ApexFrameReal, MirrorStripR2Glue oleans in $S, then
--   lake env bash -c 'LEAN_PATH=$S:$LEAN_PATH lean Erdos634/Draft/ApexR2Frame.lean'
import Erdos634.Draft.ApexFrameReal
import Erdos634.Draft.MirrorStripR2Glue

namespace Erdos634.Draft.ApexR2Frame

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.ApexPlacement
open Erdos634.Draft.CornerAdjacency

variable {N : ℕ}

/-- The Gram identity behind `dist (P′ + b·uL) V = c` (cone coordinates at their exact values). -/
theorem mirror_alg {e f s1 t1 s3 t3 G : ℝ} (he : 0 < e) (hef : e < f)
    (hs1 : s1 * (3 * f ^ 2 - e ^ 2) = f) (ht1 : s1 + t1 = 1 / f)
    (ht3 : t3 * (3 * f ^ 2 - e ^ 2) = f) (hs3 : s3 + t3 = 1 / f)
    (hG : G = f ^ 6 - (e * (3 * f ^ 2 - e ^ 2)) ^ 2 / 2) :
    (s3 + (f ^ 2 - e ^ 2) / f ^ 3 - f ^ 2 / (f ^ 2 - e ^ 2) * s1) ^ 2 * f ^ 6
      + 2 * (s3 + (f ^ 2 - e ^ 2) / f ^ 3 - f ^ 2 / (f ^ 2 - e ^ 2) * s1)
        * (t3 - f ^ 2 / (f ^ 2 - e ^ 2) * t1) * G
      + (t3 - f ^ 2 / (f ^ 2 - e ^ 2) * t1) ^ 2 * f ^ 6 = (f ^ 2) ^ 2 := by
  have hf : 0 < f := by linarith
  have hK : 0 < 3 * f ^ 2 - e ^ 2 := by nlinarith
  have hb : 0 < f ^ 2 - e ^ 2 := by nlinarith
  have es1 : s1 = f / (3 * f ^ 2 - e ^ 2) := by rw [eq_div_iff hK.ne']; exact hs1
  have et3 : t3 = f / (3 * f ^ 2 - e ^ 2) := by rw [eq_div_iff hK.ne']; exact ht3
  have et1 : t1 = 1 / f - f / (3 * f ^ 2 - e ^ 2) := by rw [← es1]; linarith
  have es3 : s3 = 1 / f - f / (3 * f ^ 2 - e ^ 2) := by rw [← et3]; linarith
  subst es1 et3 et1 es3 hG
  have h1 := hK.ne'
  have h1' : f ^ 2 * 3 - e ^ 2 ≠ 0 := by intro h; apply h1; linarith
  have h2 := hb.ne'
  have h3 := hf.ne'
  field_simp
  ring

theorem norm_comb_sq (v u : Plane) (p q : ℝ) :
    ‖p • v + q • u‖ ^ 2 = p ^ 2 * ‖v‖ ^ 2 + 2 * p * q * inner ℝ v u + q ^ 2 * ‖u‖ ^ 2 := by
  rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
    mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  ring

/-- **The mirror of `A` across `VP′` is `P′ + b·uL`** (in any frame with its cone coordinates). -/
theorem mirror_eq {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ}
    (F : HalfTurnR3R4Glue.HFrame D e f α β γ) (FC : FrameCoords F) {M : Plane}
    (hMir : HalfTurnR3R4Glue.IsMirror F.A F.V F.P M) :
    M = F.P + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uL := by
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast F.he
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast F.hef
  have he0 : (0 : ℝ) < e := by linarith
  have hf0 : (0 : ℝ) < f := by linarith
  have hb0 : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  obtain ⟨s3, t3, hs3, ht3, hP, hv3, hsum3⟩ := FC.hP
  obtain ⟨s1, t1, hs1, ht1, hV, hv1, hsum1⟩ := FC.hV
  set b : ℝ := (f : ℝ) ^ 2 - (e : ℝ) ^ 2 with hbdef
  obtain ⟨v, hvdef⟩ : ∃ v : Plane, v = ((f : ℝ) ^ 3) • F.uL := ⟨_, rfl⟩
  obtain ⟨u, hudef⟩ : ∃ u : Plane, u = F.R - F.A := ⟨_, rfl⟩
  rw [← hvdef, ← hudef] at hP hV
  set X : Plane := F.P + b • F.uL with hXdef
  have huL : F.uL = (1 / (f : ℝ) ^ 3) • v := by
    rw [hvdef, smul_smul, one_div_mul_cancel (by positivity), one_smul]
  have huR : F.uR = (1 / b) • (s1 • v + t1 • u) := by
    rw [← hV, smul_smul, one_div_mul_cancel hb0.ne', one_smul]
  have hPe : F.P = F.A + (s3 • v + t3 • u) := by rw [← hP]; abel
  -- `X − V` in cone coordinates
  set p : ℝ := s3 + b / (f : ℝ) ^ 3 - (f : ℝ) ^ 2 / b * s1 with hpdef
  set q : ℝ := t3 - (f : ℝ) ^ 2 / b * t1 with hqdef
  have hXV : X - F.V = p • v + q • u := by
    rw [hXdef, F.hV, hPe, huL, huR, hpdef, hqdef]
    module
  -- the Gram data
  have hvn : ‖v‖ = (f : ℝ) ^ 3 := by
    rw [hvdef, norm_smul, F.huL, mul_one, Real.norm_of_nonneg (by positivity)]
  have hun : ‖u‖ = (f : ℝ) ^ 3 := by rw [hudef, ← dist_eq_norm, dist_comm]; exact F.hlegR
  have hvun : ‖v - u‖ = (e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
    rw [← FC.hbaseLen, dist_eq_norm, hudef, hvdef]; congr 1; abel
  have hinner : inner ℝ v u
      = (f : ℝ) ^ 6 - ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ^ 2 / 2 := by
    have h := norm_sub_sq_real v u
    rw [hvn, hun, hvun] at h
    linarith
  have hXVn : dist X F.V = (f : ℝ) ^ 2 := by
    rw [dist_eq_norm, hXV]
    have h2 : ‖p • v + q • u‖ ^ 2 = ((f : ℝ) ^ 2) ^ 2 := by
      rw [norm_comb_sq, hvn, hun, hinner]
      have := mirror_alg (G := (f : ℝ) ^ 6 - ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ^ 2 / 2)
        he0 (by linarith) hv1 hsum1 hv3 hsum3 rfl
      rw [hpdef, hqdef, hbdef]
      linear_combination this
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2
  have hAV : dist F.A F.V = (f : ℝ) ^ 2 := by
    rw [F.hV]; exact HalfTurnR3R4Glue.dist_self_add_unit F.huR (by positivity)
  have hXP : dist X F.P = b := by
    rw [hXdef, dist_comm, dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, F.huL, mul_one,
      Real.norm_of_nonneg hb0.le]
  have hXA : F.A ≠ X := by
    intro h
    have h0 : X - F.A = (s3 + b / (f : ℝ) ^ 3) • v + t3 • u := by
      rw [hXdef, hPe, huL]; module
    rw [← h, sub_self] at h0
    have hc := congrArg (cross v) h0
    simp only [cross_add_right, cross_smul_right, cross_self', mul_zero, zero_add] at hc
    have hz : cross v (0 : Plane) = 0 := by simp [cross_apply]
    rw [hz] at hc
    have hd : cross v u ≠ 0 := by
      have := FC.hcone.det
      rw [show F.A + ((f : ℝ) ^ 3) • F.uL - F.A = v by rw [hvdef]; abel, ← hudef] at this
      exact this
    rcases mul_eq_zero.mp hc.symm with h1 | h1
    · linarith
    · exact hd h1
  have hVP : F.V ≠ F.P := by
    intro h
    have := F.hVP
    rw [h, dist_self] at this
    have : (0 : ℝ) < (e : ℝ) * f := by positivity
    linarith
  obtain ⟨hMA, hMV, hMP⟩ := hMir
  have hAPb : dist F.A F.P = b := F.hAP
  have hd2 : Module.finrank ℝ Plane = 2 := finrank_euclideanSpace_fin
  rcases EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two hd2 hVP hXA
      hAV hXVn (hMV.trans hAV) hAPb hXP (hMP.trans hAPb) with h | h
  · exact absurd h hMA
  · exact h

set_option maxHeartbeats 1000000 in
/-- **The mirror frame from a real dissection in branch (M) — PROVED.** -/
theorem r2frame_of_mirror {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ}
    (F : HalfTurnR3R4Glue.HFrame D e f α β γ) (FC : FrameCoords F) {M : Plane}
    (hMir : HalfTurnR3R4Glue.IsMirror F.A F.V F.P M)
    (hMP : HalfTurnR3R4Glue.Present D {F.V, F.P, M}) :
    Nonempty (MirrorStripR2Glue.R2Frame D e f α β γ) := by
  classical
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast F.he
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast F.hef
  have he0 : (0 : ℝ) < e := by linarith
  have hf0 : (0 : ℝ) < f := by linarith
  have hb0 : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hK : (0 : ℝ) < 3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hMeq := mirror_eq F FC hMir
  obtain ⟨s3, t3, hs3, ht3, hP, hv3, hsum3⟩ := FC.hP
  obtain ⟨s1, t1, hs1, ht1, hV, hv1, hsum1⟩ := FC.hV
  set b : ℝ := (f : ℝ) ^ 2 - (e : ℝ) ^ 2 with hbdef
  have hbne := hb0.ne'
  obtain ⟨v, hvdef⟩ : ∃ v : Plane, v = ((f : ℝ) ^ 3) • F.uL := ⟨_, rfl⟩
  obtain ⟨u, hudef⟩ : ∃ u : Plane, u = F.R - F.A := ⟨_, rfl⟩
  rw [← hvdef, ← hudef] at hP hV
  have hd : cross v u ≠ 0 := by
    have := FC.hcone.det
    rw [show F.A + ((f : ℝ) ^ 3) • F.uL - F.A = v by rw [hvdef]; abel, ← hudef] at this
    exact this
  have huL : F.uL = (1 / (f : ℝ) ^ 3) • v := by
    rw [hvdef, smul_smul, one_div_mul_cancel (by positivity), one_smul]
  have hPe : F.P - F.A = s3 • v + t3 • u := hP
  have hVe : F.V - F.A = ((f : ℝ) ^ 2 / b) • (s1 • v + t1 • u) := by
    rw [F.hV, add_sub_cancel_left, ← hV, smul_smul, div_mul_cancel₀ _ hbne]
  -- `g`: the normal functional of the leg, positive into the target
  set g : Plane →ₗ[ℝ] ℝ := (cross v u) • Erdos634.Geometry.crossL v with hgdef
  have happ : ∀ w, g w = cross v u * cross v w := fun w => by
    rw [hgdef, LinearMap.smul_apply, Erdos634.Geometry.crossL_apply, smul_eq_mul]
  have hgcomb : ∀ x y : ℝ, g (x • v + y • u) = y * (cross v u) ^ 2 := by
    intro x y
    rw [happ, cross_add_right, cross_smul_right, cross_smul_right, cross_self']; ring
  have hd2 : 0 < (cross v u) ^ 2 := by positivity
  have hgP : g F.P - g F.A = t3 * (cross v u) ^ 2 := by
    rw [← map_sub, hPe, hgcomb]
  have hgV : g F.V - g F.A = (f : ℝ) ^ 2 / b * t1 * (cross v u) ^ 2 := by
    rw [← map_sub, hVe, map_smul, hgcomb, smul_eq_mul]; ring
  -- `t3 < (f²/b)·t1`
  have hlt : t3 < (f : ℝ) ^ 2 / b * t1 := by
    have es1 : s1 = f / (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by rw [eq_div_iff hK.ne']; exact hv1
    have et3 : t3 = f / (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by rw [eq_div_iff hK.ne']; exact hv3
    have et1 : t1 = 1 / (f : ℝ) - f / (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by rw [← es1]; linarith
    rw [et3, et1, hbdef, div_lt_iff₀ hK]
    have : (f : ℝ) ^ 2 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)
        * (1 / (f : ℝ) - f / (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
        = (f : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
      have hK1 : (f : ℝ) ^ 2 * 3 - (e : ℝ) ^ 2 ≠ 0 := by intro h; linarith
      have hK2 := hK.ne'
      have hb1 := hb0.ne'
      have hf1 := hf0.ne'
      field_simp; ring
    rw [this, lt_div_iff₀ hb0]
    nlinarith
  -- the line `L` through `P′` along `uL`, in cone coordinates
  have hLpt : ∀ x : ℝ, F.P + x • F.uL = F.A + ((s3 + x / (f : ℝ) ^ 3) • v + t3 • u) := by
    intro x
    have : F.P = F.A + (s3 • v + t3 • u) := by rw [← hPe]; abel
    rw [this, huL]; module
  have hgV' : g F.P < g F.V := by
    have := mul_lt_mul_of_pos_right hlt hd2
    linarith
  have hgA' : g F.A < g F.P := by
    have := mul_pos ht3 hd2
    linarith
  obtain ⟨i2, hi2⟩ := F.hT2
  obtain ⟨i3, hi3⟩ := F.hT3
  obtain ⟨iM, hiM⟩ := hMP
  refine ⟨{
    A := F.A
    P := F.P
    V := F.V
    R := F.R
    uL := F.uL
    g := g
    hco := F.hco
    he := by have := F.he; omega
    hef := by have := F.hef; omega
    hM := ⟨F.hM.hs0, F.hM.hs1, F.hM.hs2, F.hM.hα', F.hM.hβ', F.hM.hγ'⟩
    hA := F.hAng
    htarget := F.htarget
    hlegR := F.hlegR
    huL := F.huL
    hAP := F.hAP
    hAV := by rw [F.hV]; exact HalfTurnR3R4Glue.dist_self_add_unit F.huR (by positivity)
    hVP := F.hVP
    hPJ1 := F.hPJ1
    hg0 := ?_
    hguL := ?_
    hgV := hgV'
    hgA := hgA'
    hbase := ?_
    hLint := ?_
    hT2 := ⟨i2, hi2⟩
    hT3 := ⟨i3, hi3⟩
    hMir := ⟨iM, by rw [hiM, hMeq]⟩ }⟩
  · intro h0
    have := congrArg (fun φ : Plane →ₗ[ℝ] ℝ => φ u) h0
    simp only [LinearMap.zero_apply] at this
    have h1 := hgcomb 0 1
    rw [zero_smul, zero_add, one_smul, this] at h1
    linarith
  · rw [huL, map_smul, happ, cross_self', mul_zero, smul_zero]
  · intro t ht hmem
    rw [hLpt, hvdef, hudef] at hmem
    apply FC.hout (s3 + ((((f : ℝ) - 1) * (f : ℝ) ^ 2 + t)) / (f : ℝ) ^ 3) t3 _ hmem
    have : s3 + (((f : ℝ) - 1) * (f : ℝ) ^ 2 + t) / (f : ℝ) ^ 3 + t3
        = 1 + t / (f : ℝ) ^ 3 := by
      have hf3 : (f : ℝ) ^ 3 ≠ 0 := by positivity
      rw [show s3 + (((f : ℝ) - 1) * (f : ℝ) ^ 2 + t) / (f : ℝ) ^ 3 + t3
          = (s3 + t3) + (((f : ℝ) - 1) * (f : ℝ) ^ 2 + t) / (f : ℝ) ^ 3 by ring, hsum3]
      field_simp; ring
    rw [this]
    have : 0 < t / (f : ℝ) ^ 3 := by positivity
    linarith
  · intro t ht ht2
    rw [hLpt]
    have hC := FC.hcone
    have := hC.inter (s3 + t / (f : ℝ) ^ 3) t3 1 (by positivity) ht3 one_pos (by
      rw [one_mul, show s3 + t / (f : ℝ) ^ 3 + t3 = (s3 + t3) + t / (f : ℝ) ^ 3 by ring, hsum3]
      have hf3 : (0 : ℝ) < (f : ℝ) ^ 3 := by positivity
      have : t / (f : ℝ) ^ 3 < ((f : ℝ) - 1) / f := by
        rw [div_lt_div_iff₀ hf3 hf0]; nlinarith
      have : 1 / (f : ℝ) + ((f : ℝ) - 1) / f = 1 := by field_simp; ring
      linarith)
    rw [show F.A + ((f : ℝ) ^ 3) • F.uL - F.A = v by rw [hvdef]; abel, ← hudef,
      one_smul] at this
    exact this

/-- **Lemma G for a real dissection, both branches framed.**  Every real `m = 1` dissection carries
the apex frame `F` of branch (H) and either `K = T₂ + (VP′-half-turn)` is present (branch (H)), or
it carries the mirror-strip frame `R2Frame` of branch (M). -/
theorem split_real {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {k : Fin 3}
    (h : ApexFrameReal.M1Data D e f α β γ k) :
    ∃ F : HalfTurnR3R4Glue.HFrame D e f α β γ,
      HalfTurnR3R4Glue.Present D F.K ∨ Nonempty (MirrorStripR2Glue.R2Frame D e f α β γ) := by
  obtain ⟨F, FC⟩ := ApexLegWord.exists_hframe_coords_m1 D h.hco h.he h.hef h.hM h.hAng k h.hcorner
    h.hβ1 h.hβ2 h.hleg1 h.hleg2 h.hbase
  refine ⟨F, ?_⟩
  rcases TileIdent.lemmaG_frame F with hK | ⟨M, hMir, hMP⟩
  · exact Or.inl hK
  · exact Or.inr (r2frame_of_mirror F FC hMir hMP)

end Erdos634.Draft.ApexR2Frame

#print axioms Erdos634.Draft.ApexR2Frame.mirror_alg
#print axioms Erdos634.Draft.ApexR2Frame.mirror_eq
#print axioms Erdos634.Draft.ApexR2Frame.r2frame_of_mirror
#print axioms Erdos634.Draft.ApexR2Frame.split_real

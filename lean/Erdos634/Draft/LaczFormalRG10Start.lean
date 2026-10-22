-- Draft/LaczFormalRG10Start.lean -- Laczkovich DCG 48 (2012), Lemma 4.8, the LOCAL HALF at the START of a maximal segment: at a vertex `V` of the dissection of a convex polygon with a left tile
-- starting along `d`, no left tile arriving along `-d`, and a polygon-interior point ahead on the ray `V + t d`, a RIGHT tile also starts along `d` (no T-junction start, no exterior sector next to the ray).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 4), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRGExt
import Erdos634.Draft.LaczFormalGraphFour

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

namespace ExtFan

variable {D : RegionDissection N} {V : Plane} {κ : Type} [Fintype κ]

/-- Every sector of the fan has a clockwise neighbour: a sector whose end ray is the start ray of the given one. -/
theorem pred_exists (F : ExtFan D V κ) (o : AtV D V ⊕ κ) : ∃ o', Par (Sum.elim F.p F.pe o) (Sum.elim F.q F.qe o') := by
  obtain ⟨n, hn, hen⟩ := F.hsurj o
  have hk : 0 < Fintype.card (AtV D V ⊕ κ) := Fintype.card_pos_iff.mpr ⟨o⟩
  obtain ⟨m, hm⟩ : ∃ m, n + Fintype.card (AtV D V ⊕ κ) = m + 1 := ⟨n + Fintype.card (AtV D V ⊕ κ) - 1, by omega⟩
  refine ⟨F.e m, ?_⟩
  have h1 := F.hP m
  have h2 : F.e (m + 1) = o := by rw [← hm, F.hper n, hen]
  rw [h2] at h1
  exact h1

/-- A straight sector (`crs = 0`, `dt < 0`) whose end ray is along `d` has its start ray along `-d`. -/
theorem straight_par {p q d : V2} (hq : Par q d) (h0 : crs p q = 0) (hd : dt p q < 0) : Par p (-d.1, -d.2) := by
  obtain ⟨c, hc, hqc⟩ := hq.smul
  rw [hqc] at h0 hd
  refine ⟨?_, ?_⟩
  · unfold crs at h0 ⊢
    simp only at h0 ⊢
    have : c * (p.1 * d.2 - p.2 * d.1) = 0 := by linarith
    have h2 := (mul_eq_zero.mp this).resolve_left hc.ne'
    linarith
  · unfold dt at hd ⊢
    simp only at hd ⊢
    have : c * (p.1 * d.1 + p.2 * d.2) < 0 := by linarith
    have h2 : p.1 * d.1 + p.2 * d.2 < 0 := by
      by_contra hh; push Not at hh; nlinarith [mul_nonneg hc.le hh]
    linarith

/-- **Interior direction.**  If a polygon-interior point `Z = V + t0 d` lies ahead of `V`, then `zminus d τ` (slightly clockwise of `d`) is in the target cone for small `τ`. -/
theorem tgt_zminus (F : ExtFan D V κ) {d : V2} (hconv : Convex ℝ D.region) (hV : V ∈ D.region) {t0 : ℝ} (ht0 : 0 < t0) {Z : Plane}
    (hZ : Z ∈ interior D.region) (hZd : toV2 (Z - V) = (t0 * d.1, t0 * d.2)) :
    ∃ τ0 > 0, ∀ τ : ℝ, 0 < τ → τ < τ0 → zminus d τ ∈ F.Tgt := by
  classical
  have hZ' : Z = ptOf V d t0 := pt_eq_of_toV2 (H := V) (by rw [hZd, toV2_ptOf])
  obtain ⟨ε, hε, hεR⟩ := exists_ptOf_small V d F.hR
  have hdist : ∀ s : ℝ, dist (ptOf V d s) V = |s| * ‖Erdos634.CertCoord.mkPt d.1 d.2‖ := by
    intro s
    rw [dist_eq_norm]
    have : ptOf V d s - V = s • Erdos634.CertCoord.mkPt d.1 d.2 := by simp [ptOf]
    rw [this, norm_smul, Real.norm_eq_abs]
  obtain ⟨t, htpos, htε, htt0⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ ε ∧ t < t0 := ⟨min ε (t0 / 2), lt_min hε (by linarith), min_le_left _ _, by
    have := min_le_right ε (t0 / 2); linarith⟩
  have hZtR : dist (ptOf V d t) V < F.R := by
    rw [hdist] at hεR ⊢
    rw [abs_of_pos htpos]
    rw [abs_of_pos hε] at hεR
    have hn := norm_nonneg (Erdos634.CertCoord.mkPt d.1 d.2)
    nlinarith
  have hint : ptOf V d t ∈ interior D.region := by
    have hseg := hconv.openSegment_interior_self_subset_interior hZ hV
    obtain ⟨σ, hσdef⟩ : ∃ σ : ℝ, σ = t / t0 := ⟨_, rfl⟩
    have hσ0 : 0 < σ := by rw [hσdef]; exact div_pos htpos ht0
    have hσ1 : σ < 1 := by rw [hσdef, div_lt_one ht0]; exact htt0
    have hσm : t = σ * t0 := by rw [hσdef]; field_simp
    apply hseg
    refine ⟨σ, 1 - σ, hσ0, by linarith, by ring, ?_⟩
    rw [hZ']
    unfold ptOf
    rw [hσm]
    module
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hint)
  set w : Plane := Erdos634.CertCoord.mkPt d.2 (-d.1) with hw
  set K : ℝ := ‖w‖ with hK
  have hK0 : 0 ≤ K := norm_nonneg _
  set ρ' : ℝ := min ρ (F.R - dist (ptOf V d t) V) with hρ'
  have hρ'pos : 0 < ρ' := lt_min hρ (by linarith)
  refine ⟨ρ' / (t * K + 1), by positivity, ?_⟩
  intro τ hτ hτ0
  have hy : ptOf V (zminus d τ) t = ptOf V d t + (t * τ) • w := by
    unfold ptOf zminus
    rw [hw]
    simp only [Erdos634.CertCoord.mkPt]
    ext i
    fin_cases i <;> simp <;> ring
  have hdy : dist (ptOf V (zminus d τ) t) (ptOf V d t) < ρ' := by
    rw [hy, dist_eq_norm]
    simp only [add_sub_cancel_left]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos htpos hτ)]
    rw [lt_div_iff₀ (by positivity)] at hτ0
    nlinarith
  have hyin : ptOf V (zminus d τ) t ∈ interior D.region := hball (lt_of_lt_of_le hdy (min_le_left _ _))
  have hyR : dist (ptOf V (zminus d τ) t) V < F.R := by
    have h1 := lt_of_lt_of_le hdy (min_le_right _ _)
    have h2 := dist_triangle (ptOf V (zminus d τ) t) (ptOf V d t) V
    linarith
  have hmem := (F.hT _ hyR).mp (interior_subset hyin)
  rw [toV2_ptOf] at hmem
  exact F.Tgt_inv htpos hmem

/-- A fan with a half-plane `{crs d x ≤ 0}` in the target cone and one further target direction strictly to the left has the whole plane as target cone. -/
theorem tgt_univ (F : ExtFan D V κ) {d : V2} (s : AtV D V) (hsp : Par (F.p s) (-d.1, -d.2)) (hsq : Par (F.q s) d)
    {w : V2} (hw : w ∈ F.Tgt) (hwd : 0 < crs d w) (z : V2) : z ∈ F.Tgt := by
  obtain ⟨c1, hc1, hp1⟩ := hsp.smul
  obtain ⟨c2, hc2, hq2⟩ := hsq.smul
  set lam : ℝ := (|crs d z| + 1) / crs d w with hlam
  have hlam0 : 0 < lam := div_pos (by positivity) hwd
  have hlw : lam * crs d w = |crs d z| + 1 := by rw [hlam]; field_simp
  set x : V2 := (z.1 - lam * w.1, z.2 - lam * w.2) with hx
  have hcx : crs d x = crs d z - (|crs d z| + 1) := by
    rw [← hlw]; unfold crs; simp only [hx]; ring
  have hcx' : crs d x < 0 := by
    have := le_abs_self (crs d z); linarith
  have hxT : x ∈ F.Tgt := by
    apply F.tile_cone_sub s
    refine ⟨?_, ?_⟩
    · rw [hp1]; unfold crs at hcx' ⊢; simp only at hcx' ⊢; nlinarith [mul_pos hc1 (neg_pos.mpr hcx')]
    · rw [hq2]; unfold crs at hcx' ⊢; simp only at hcx' ⊢; nlinarith [mul_pos hc2 (neg_pos.mpr hcx')]
  have h2x := F.hTs x hxT 2 (by norm_num)
  have h2w := F.hTs w hw (2 * lam) (by positivity)
  have := F.hTc _ h2x _ h2w (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  convert this using 1
  ext <;> simp [hx] <;> ring

/-- **Start rule.**  At a vertex with a left corner `a` starting along `d`, with no left corner arriving along `-d`, and with the direction `d` interior to the target cone,
a right corner ends along `d` (a right tile starts along `d`). -/
theorem right_start (F : ExtFan D V κ) {d : V2} (a : AtV D V) (hca : 0 < crs (F.p a) (F.q a)) (hpa : Par (F.p a) d)
    (hnoL : ∀ c : AtV D V, 0 < crs (F.p c) (F.q c) → ¬ Par (F.q c) (-d.1, -d.2))
    (hint : ∃ τ0 > 0, ∀ τ : ℝ, 0 < τ → τ < τ0 → zminus d τ ∈ F.Tgt) :
    ∃ s : AtV D V, 0 < crs (F.p s) (F.q s) ∧ Par (F.q s) d := by
  classical
  obtain ⟨τ0, hτ0, hτ⟩ := hint
  have hd0 : d ≠ 0 := hpa.ne_right
  obtain ⟨o, ho⟩ := F.pred_exists (Sum.inl a)
  simp only [Sum.elim_inl] at ho
  have hqo : Par (Sum.elim F.q F.qe o) d := ho.symm.trans hpa
  -- a point of the open cone of `a` just counterclockwise of `d`
  obtain ⟨δa, hδa, Ha⟩ := plus_ray_int (F.hok a)
  set zA := zplus (F.p a) (δa / 2) with hzA
  have hzAint : inInt (F.p a) (F.q a) zA := Ha _ (by positivity) (by linarith)
  have hzAT : zA ∈ F.Tgt := F.tile_cone_sub a ⟨hzAint.1.le, hzAint.2.le⟩
  obtain ⟨cp, hcp, hpa'⟩ := hpa.smul
  have hzA_left : 0 < crs d zA := by
    have h := hzAint.1
    rw [hpa'] at h
    unfold crs at h ⊢; simp only at h ⊢
    by_contra hX; push Not at hX
    nlinarith [mul_nonneg hcp.le (neg_nonneg.mpr hX)]
  -- an exterior sector next to `d`, clockwise side or counterclockwise side, is impossible
  rcases o with s | j
  · simp only [Sum.elim_inl] at hqo
    rcases F.hok s with hs | ⟨hs0, hsd⟩
    · exact ⟨s, hs, hqo⟩
    · exfalso
      have hps : Par (F.p s) (-d.1, -d.2) := straight_par hqo hs0 hsd
      obtain ⟨o2, ho2⟩ := F.pred_exists (Sum.inl s)
      simp only [Sum.elim_inl] at ho2
      have hq2 : Par (Sum.elim F.q F.qe o2) (-d.1, -d.2) := ho2.symm.trans hps
      rcases o2 with c | j
      · simp only [Sum.elim_inl] at hq2
        rcases F.hok c with hc | ⟨hc0, hcd⟩
        · exact hnoL c hc hq2
        · have hpc : Par (F.p c) d := by
            have := straight_par (d := (-d.1, -d.2)) hq2 hc0 hcd
            simpa using (show Par (F.p c) (-(-d.1), -(-d.2)) from by simpa using this)
          obtain ⟨c3, hc3, hp3⟩ := hpc.smul
          obtain ⟨c4, hc4, hq4⟩ := hq2.smul
          have hzC : inInt (F.p c) (F.q c) zA := by
            constructor
            · rw [hp3]; unfold crs at hzA_left ⊢; simp only at hzA_left ⊢; nlinarith [mul_pos hc3 hzA_left]
            · rw [hq4]; unfold crs at hzA_left ⊢; simp only at hzA_left ⊢; nlinarith [mul_pos hc4 hzA_left]
          have hac : a ≠ c := by rintro rfl; linarith
          exact tiles_disjoint D V F.p F.q F.hloc a c hac zA ⟨hzAint, hzC⟩
      · simp only [Sum.elim_inr] at hq2
        obtain ⟨δ, hδ, Hm⟩ := minus_ray_int (F.hokE j)
        have hin := Hm (δ / 2) (by positivity) (by linarith)
        exact F.hextT j _ hin (F.tgt_univ s hps hqo hzAT hzA_left _)
  · exfalso
    simp only [Sum.elim_inr] at hqo
    obtain ⟨c, hc, hqc⟩ := hqo.smul
    obtain ⟨δ, hδ, Hm⟩ := minus_ray_int (F.hokE j)
    set ε : ℝ := min (δ / 2) (τ0 / 2) with hε
    have hε0 : 0 < ε := lt_min (by positivity) (by positivity)
    have hεδ : ε < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hετ : ε < τ0 := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hin := Hm ε hε0 hεδ
    have hzT := hτ ε hε0 hετ
    have hscaled : zminus (F.qe j) ε = (c * (zminus d ε).1, c * (zminus d ε).2) := by
      rw [hqc]; unfold zminus; simp only; ext <;> simp <;> ring
    rw [hscaled] at hin
    exact F.hextT j _ hin (F.hTs _ hzT c hc)

end ExtFan

end Erdos634.Draft.LaczFormal.RG

import Erdos634.Refl.CheckM
import Erdos634.Refl.SoundStage13
import Erdos634.PlacementCompletenessCone

/-! Refl/SoundM1.lean -- soundness of the local obligations of `CheckM.nodeLocalOkM`:
    `cone_soundM` (near `v` the unfilled region lies in the cone of `d`, `g`) and `hfree_soundM`
    (copy of Stage 7 for `NodeM`). -/

set_option linter.unusedSimpArgs false
open Erdos634.CertNode Erdos634.PlacementCompleteness
open Erdos634.Geometry (Plane cross)

namespace Refl

structure LocalFactsM (I : Inst) (cfg : List _root_.Tri) (n : NodeM) : Prop where
  vw : 0 < n.v.w
  dw : 0 < n.d.w
  unit : n.d.x * n.d.x + I.Dn * n.d.y * n.d.y = n.d.w * n.d.w
  tauN : 0 < n.tauN
  tauD : 0 < n.tauD
  flen : n.fedges.length = cfg.length
  gw : 0 < n.g.w
  eN : 0 < n.eN
  eD : 0 < n.eD
  dg : 0 < n.d.x * n.g.y - n.d.y * n.g.x
  r1 : Bsp.check cfg [] [] false (consM1 I n) [] n.t1 = true
  r2 : Bsp.check cfg [] [] false (consM2 I n) [] n.t2 = true
  tgtQ : ((tgtLinsM I).all fun l => okPos (quad I n.v n.d l) n.tauN n.tauD) = true
  tileQ : ((cfg.zip n.fedges).all fun x => okNeg (quad I n.v n.d (x.1.edge x.2)) n.tauN n.tauD) = true

theorem nodeLocalOkM_facts (I : Inst) (cfg : List _root_.Tri) (n : NodeM)
    (h : nodeLocalOkM I cfg n = true) : LocalFactsM I cfg n := by
  unfold nodeLocalOkM at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

theorem tgtLinsM_eq (I : Inst) : tgtLinsM I = tgtLins I := rfl

theorem abs_le_of_sq_le' {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : |a| ≤ b :=
  abs_le.mpr ⟨by nlinarith, by nlinarith⟩

/-- the ray form, in the rational coordinates -/
theorem evalL_rayL (v d : Pt) (hv : 0 < v.w) (hd : 0 < d.w) (X Y : ℝ) :
    evalL (rayL v d) X Y = (v.w : ℝ) * d.w * (d.X * (Y - v.Y) - d.Y * (X - v.X)) := by
  have a := Pt.w_ne v hv
  have b := Pt.w_ne d hd
  unfold evalL rayL Pt.X Pt.Y
  push_cast
  field_simp
  ring

theorem cross_re (Dn : ℝ) (v d : Pt) (X Y : ℝ) :
    cross (d.re Dn) (rp Dn X Y - v.re Dn) = sr Dn * (d.X * (Y - v.Y) - d.Y * (X - v.X)) := by
  show cross (rp Dn d.X d.Y) (rp Dn X Y - rp Dn v.X v.Y) = _
  simp only [cross, PiLp.sub_apply, rp_zero, rp_one]
  ring

theorem boxL_sat (v : Pt) (hv : 0 < v.w) (eN eD : Int) (heD : 0 < eD) (X Y : ℝ)
    (hX : |X - v.X| ≤ (eN : ℝ) / eD) (hY : |Y - v.Y| ≤ (eN : ℝ) / eD) :
    ∀ l ∈ boxL v eN eD, 0 ≤ evalL l X Y := by
  have hw := Pt.w_pos v hv
  have hwn := Pt.w_ne v hv
  have hD : (0 : ℝ) < eD := by exact_mod_cast heD
  obtain ⟨hX1, hX2⟩ := abs_le.mp hX
  obtain ⟨hY1, hY2⟩ := abs_le.mp hY
  have hwD : (0 : ℝ) < v.w * eD := mul_pos hw hD
  have ex : (v.x : ℝ) = v.X * v.w := by unfold Pt.X; field_simp
  have ey : (v.y : ℝ) = v.Y * v.w := by unfold Pt.Y; field_simp
  intro l hl
  simp only [boxL, List.mem_cons, List.mem_nil_iff, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl
  · have e : evalL ⟨v.w * eD, 0, eN * v.w - v.x * eD⟩ X Y
        = (v.w : ℝ) * eD * (X - v.X + (eN : ℝ) / eD) := by
      simp only [evalL]; push_cast; rw [ex]; field_simp; ring
    rw [e]; exact mul_nonneg hwD.le (by linarith)
  · have e : evalL ⟨-(v.w * eD), 0, eN * v.w + v.x * eD⟩ X Y
        = (v.w : ℝ) * eD * ((eN : ℝ) / eD - (X - v.X)) := by
      simp only [evalL]; push_cast; rw [ex]; field_simp; ring
    rw [e]; exact mul_nonneg hwD.le (by linarith)
  · have e : evalL ⟨0, v.w * eD, eN * v.w - v.y * eD⟩ X Y
        = (v.w : ℝ) * eD * (Y - v.Y + (eN : ℝ) / eD) := by
      simp only [evalL]; push_cast; rw [ey]; field_simp; ring
    rw [e]; exact mul_nonneg hwD.le (by linarith)
  · have e : evalL ⟨0, -(v.w * eD), eN * v.w + v.y * eD⟩ X Y
        = (v.w : ℝ) * eD * ((eN : ℝ) / eD - (Y - v.Y)) := by
      simp only [evalL]; push_cast; rw [ey]; field_simp; ring
    rw [e]; exact mul_nonneg hwD.le (by linarith)

/-- **cone**: near `v`, every unfilled point is on/left of `d` and on/right of `g`. -/
theorem cone_soundM (Dn : ℝ) (hD : 0 < Dn) (I : Inst) (htok : I.tgt.ok = true)
    (cfg : List _root_.Tri) (hcfg : ∀ t ∈ cfg, t.ok = true) (n : NodeM) (F : LocalFactsM I cfg n)
    {N : ℕ} (D : Erdos634.Geometry.CongruentDissection N)
    (htarget : D.target.carrier = I.tgt.carr Dn) (S : Finset (Fin N))
    (hS : ∀ t ∈ cfg, ∃ i ∈ S, (D.tile i).carrier = t.carr Dn) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ unfilled D.toDissection S, dist p (n.v.re Dn) < ε →
      0 ≤ cross (n.d.re Dn) (p - n.v.re Dn) ∧ 0 ≤ cross (p - n.v.re Dn) (n.g.re Dn) := by
  have heN : (0 : ℝ) < n.eN := by exact_mod_cast F.eN
  have heD : (0 : ℝ) < n.eD := by exact_mod_cast F.eD
  set e : ℝ := (n.eN : ℝ) / n.eD with he
  have hepos : 0 < e := div_pos heN heD
  have hsr : 0 < sr Dn := Real.sqrt_pos.mpr hD
  have hvw := Pt.w_pos n.v F.vw
  have hdw := Pt.w_pos n.d F.dw
  have hgw := Pt.w_pos n.g F.gw
  refine ⟨e * min 1 (sr Dn), mul_pos hepos (lt_min one_pos hsr), ?_⟩
  intro p hp hdist
  obtain ⟨X, Y, rfl⟩ := exists_rp hD p
  have hnt : ∀ t ∈ cfg, rp Dn X Y ∉ t.carr Dn := by
    intro t ht hpt
    obtain ⟨i, hi, hti⟩ := hS t ht
    exact hp.2 (Set.mem_iUnion₂.mpr ⟨i, hi, by rw [hti]; exact hpt⟩)
  have hpt : rp Dn X Y ∈ I.tgt.carr Dn := by rw [← htarget]; exact hp.1
  have hsatT := tgtLins_sat Dn hD I htok X Y hpt
  -- coordinate bounds from the distance
  have hd0 : 0 ≤ dist (rp Dn X Y) (n.v.re Dn) := dist_nonneg
  have hsq : dist (rp Dn X Y) (n.v.re Dn) ^ 2 = (X - n.v.X) ^ 2 + ((Y - n.v.Y) * sr Dn) ^ 2 := by
    rw [dist_sq_coord]
    show (rp Dn X Y 0 - rp Dn n.v.X n.v.Y 0) ^ 2 + (rp Dn X Y 1 - rp Dn n.v.X n.v.Y 1) ^ 2 = _
    simp only [rp_zero, rp_one]; ring
  have hm1 : e * min 1 (sr Dn) ≤ e := by
    have := min_le_left (1 : ℝ) (sr Dn); nlinarith
  have hm2 : e * min 1 (sr Dn) ≤ e * sr Dn := by
    have := min_le_right (1 : ℝ) (sr Dn); nlinarith
  have hX : |X - n.v.X| ≤ e := by
    have h1 : (X - n.v.X) ^ 2 ≤ dist (rp Dn X Y) (n.v.re Dn) ^ 2 := by
      rw [hsq]; nlinarith [sq_nonneg ((Y - n.v.Y) * sr Dn)]
    have := abs_le_of_sq_le' hd0 h1
    linarith
  have hY : |Y - n.v.Y| ≤ e := by
    have h1 : ((Y - n.v.Y) * sr Dn) ^ 2 ≤ dist (rp Dn X Y) (n.v.re Dn) ^ 2 := by
      rw [hsq]; nlinarith [sq_nonneg (X - n.v.X)]
    have h2 := abs_le_of_sq_le' hd0 h1
    rw [abs_mul, abs_of_pos hsr] at h2
    have h3 : |Y - n.v.Y| * sr Dn < e * sr Dn := by linarith
    exact (lt_of_mul_lt_mul_right h3 hsr.le).le
  have hbox := boxL_sat n.v F.vw n.eN n.eD F.eD X Y hX hY
  have hbase : ∀ c ∈ (tgtLinsM I ++ boxL n.v n.eN n.eD).map (fun l => (l, false)), Sat c X Y := by
    intro c hc
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hc
    rcases List.mem_append.mp hl with h | h
    · simpa [Sat] using hsatT l h
    · simpa [Sat] using hbox l h
  set K : ℝ := n.d.X * (Y - n.v.Y) - n.d.Y * (X - n.v.X) with hKdef
  set G : ℝ := n.g.X * (Y - n.v.Y) - n.g.Y * (X - n.v.X) with hGdef
  have eK : evalL (rayL n.v n.d) X Y = (n.v.w : ℝ) * n.d.w * K := evalL_rayL n.v n.d F.vw F.dw X Y
  have eG : evalL (rayL n.v n.g) X Y = (n.v.w : ℝ) * n.g.w * G := evalL_rayL n.v n.g F.vw F.gw X Y
  have hK : 0 ≤ K := by
    by_contra hneg
    push_neg at hneg
    rcases bsp_sound Dn hD cfg hcfg [] [] false n.t1 (consM1 I n) [] X Y F.r1 (by
        intro c hc
        rcases List.mem_append.mp hc with h | h
        · exact hbase c h
        · simp only [List.mem_singleton] at h; subst h
          have : 0 < evalL (rayL n.v n.d).neg X Y := by
            rw [evalL_neg, eK]
            have := mul_pos (mul_pos hvw hdw) (neg_pos.mpr hneg)
            linarith
          simpa [Sat] using this) (by simp) with ⟨t, ht, hm⟩ | ⟨h, _⟩
    · exact hnt t ht hm
    · simp at h
  have hG : G ≤ 0 := by
    by_contra hpos
    push_neg at hpos
    rcases bsp_sound Dn hD cfg hcfg [] [] false n.t2 (consM2 I n) [] X Y F.r2 (by
        intro c hc
        rcases List.mem_append.mp hc with h | h
        · exact hbase c h
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
          rcases h with h | h
          · subst h
            have : 0 ≤ evalL (rayL n.v n.d) X Y := by
              rw [eK]; exact mul_nonneg (mul_pos hvw hdw).le hK
            simpa [Sat] using this
          · subst h
            have : 0 < evalL (rayL n.v n.g) X Y := by
              rw [eG]; exact mul_pos (mul_pos hvw hgw) hpos
            simpa [Sat] using this) (by simp) with ⟨t, ht, hm⟩ | ⟨h, _⟩
    · exact hnt t ht hm
    · simp at h
  refine ⟨?_, ?_⟩
  · rw [cross_re]; exact mul_nonneg hsr.le hK
  · rw [cross_anticomm, cross_re]
    have := mul_nonneg hsr.le (neg_nonneg.mpr hG)
    linarith

#print axioms Refl.cone_soundM

/-- the cone is pointed: `0 < cross d g` -/
theorem dg_re (Dn : ℝ) (hD : 0 < Dn) (I : Inst) (cfg : List _root_.Tri) (n : NodeM)
    (F : LocalFactsM I cfg n) : 0 < cross (n.d.re Dn) (n.g.re Dn) := by
  have hsr : 0 < sr Dn := Real.sqrt_pos.mpr hD
  have hdw := Pt.w_pos n.d F.dw
  have hgw := Pt.w_pos n.g F.gw
  have h : (0 : ℝ) < (n.d.x : ℝ) * n.g.y - n.d.y * n.g.x := by exact_mod_cast F.dg
  show 0 < cross (rp Dn n.d.X n.d.Y) (rp Dn n.g.X n.g.Y)
  simp only [cross, rp_zero, rp_one]
  have e : n.d.X * (n.g.Y * sr Dn) - n.d.Y * sr Dn * n.g.X
      = sr Dn * (((n.d.x : ℝ) * n.g.y - n.d.y * n.g.x) / (n.d.w * n.g.w)) := by
    unfold Pt.X Pt.Y; field_simp
  rw [e]
  exact mul_pos hsr (div_pos h (mul_pos hdw hgw))

/-- **`hfree`** for `NodeM` (Stage 7 verbatim). -/
theorem hfree_soundM (Dn : ℝ) (hD : 0 < Dn) (I : Inst) (hDn : (I.Dn : ℝ) = Dn)
    (htok : I.tgt.ok = true) (cfg : List _root_.Tri) (hcfg : ∀ t ∈ cfg, t.ok = true)
    (n : NodeM) (F : LocalFactsM I cfg n)
    {N : ℕ} (D : Erdos634.Geometry.CongruentDissection N)
    (htarget : D.target.carrier = I.tgt.carr Dn) (S : Finset (Fin N))
    (hSt : ∀ i ∈ S, ∃ t ∈ cfg, (D.tile i).carrier = t.carr Dn) :
    ∀ ε : ℝ, 0 < ε → ∃ t s : ℝ, 0 < t ∧ t < ε ∧ 0 < s ∧ s < ε ∧
      (n.v.re Dn) + t • ((n.d.re Dn) + s • perp (n.d.re Dn))
        ∈ unfilled D.toDissection S := by
  have hτ : (0:ℝ) < (n.tauN : ℝ) / n.tauD := by
    have a : (0:ℝ) < n.tauN := by exact_mod_cast F.tauN
    have b : (0:ℝ) < n.tauD := by exact_mod_cast F.tauD
    positivity
  refine hfree_of (Dn := Dn) (B := max 1 (sr Dn + 1)) hD (le_max_left _ _)
    (lt_of_lt_of_le (by linarith) (le_max_right _ _)) hτ _ _ _ ?_
  intro t ht0 htτ
  have hcurve := pt_ccw_rp Dn hD n.v.X n.v.Y n.d.X n.d.Y t
  show (rp Dn n.v.X n.v.Y) + t • ((rp Dn n.d.X n.d.Y) + (t * sr Dn) • perp (rp Dn n.d.X n.d.Y)) ∈ _
  rw [hcurve]
  set X := n.v.X + n.d.X * t - Dn * n.d.Y * t ^ 2
  set Y := n.v.Y + n.d.Y * t + n.d.X * t ^ 2
  rw [unfilled]
  refine ⟨?_, fun hU => ?_⟩
  · rw [htarget]
    refine Tri.mem_of_edges Dn hD I.tgt htok X Y ?_
    intro i hi
    have hall := List.all_eq_true.mp F.tgtQ (I.tgt.edge i)
      (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    exact okPos_sound I Dn hDn n.v n.d F.vw F.dw _ _ _ F.tauN F.tauD hall t ht0 htτ
  · obtain ⟨i, hi, hm⟩ := Set.mem_iUnion₂.mp hU
    obtain ⟨T, hT, hTc⟩ := hSt i hi
    rw [hTc] at hm
    obtain ⟨e, he⟩ := zip_all_ex _ cfg n.fedges F.flen F.tileQ T hT
    have hneg := okNeg_sound I Dn hDn n.v n.d F.vw F.dw _ _ _ F.tauN F.tauD he t ht0 htτ
    have hnn := Tri.edge_nonneg Dn hD T (hcfg T hT) X Y hm (e % 3) (Nat.mod_lt _ (by norm_num))
    rw [← Tri.edge_mod] at hnn
    linarith

#print axioms Refl.hfree_soundM

end Refl

-- Draft/LaczFormalRG8Align.lean -- Laczkovich DCG 48 (2012), proof of Lemma 4.6: two maximal segments on the same line through a common inner point coincide.  Here the alignment of an edge's
-- walk with the walk of a maximal segment, for walks of arbitrary side (`WalkU`): same orientation => same start (`align_same`); opposite orientation => the start lies beyond the end (`align_opp`).
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Lemma 4.6), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG8Main

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

theorem noBack_walkU {D : RegionDissection N} {b : Bool} {d : V2} (hd : d ≠ 0) {X H X' : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkU D b d X H L) {T s : ℝ} (hT : toV2 (H - X) = (T * d.1, T * d.2)) (hs0 : 0 < s) (hsT : s ≤ T)
    (hX' : toV2 (X' - X) = (s * d.1, s * d.2)) (hnb : NoBack D d X') : False := by
  rcases walkU_cases W with ⟨-, W'⟩ | ⟨-, W'⟩
  · exact noBack_walkT hd W' hT hs0 hsT hX' hnb
  · exact noBack_walkR hd W' hT hs0 hsT hX' hnb

/-- Prefix of a walk up to the end of one of its elements. -/
theorem walkU_prefix_end {D : RegionDissection N} {b : Bool} {d : V2} {X Y W : Plane} {L : List (Fin N × Plane × Plane)} (hW : WalkU D b d X Y L)
    {f : Fin N × Plane × Plane} (hf : f ∈ L) (hfW : f.2.2 = W) : ∃ P : List (Fin N × Plane × Plane), WalkU D b d X W P ∧ P ≠ [] ∧ ∀ x ∈ P, x ∈ L := by
  obtain ⟨P0, Q, hdec⟩ := List.append_of_mem hf
  obtain ⟨w1, w2⟩ := walkU_split hW hdec
  obtain ⟨i, A, B⟩ := f
  simp only at hfW
  subst hfW
  cases w2 with
  | cons hS W' =>
    refine ⟨P0 ++ [(i, A, B)], ?_, by simp, ?_⟩
    · rw [walkU_append]; exact ⟨A, w1, WalkU.cons hS (WalkU.nil _)⟩
    · intro x hx
      rw [hdec]
      simp only [List.mem_append, List.mem_singleton] at hx ⊢
      rcases hx with hx | rfl
      · exact Or.inl hx
      · exact Or.inr (List.mem_cons_self ..)

theorem toV2_sub3 (A B C : Plane) : toV2 (A - C) = ((toV2 (A - B)).1 + (toV2 (B - C)).1, (toV2 (A - B)).2 + (toV2 (B - C)).2) := by
  unfold toV2; ext <;> simp

/-- **Same orientation**: a walk of direction `d2 ∥ d` ending at the same point as a walk of direction `d`, both starts having no tile behind them, have the same start. -/
theorem align_same (D : RegionDissection N) {b1 b2 : Bool} {d d2 : V2} {X Z W : Plane} {P1 P2 : List (Fin N × Plane × Plane)} (hd : d ≠ 0) (hpar : Par d2 d)
    (w1 : WalkU D b1 d X W P1) (h1 : P1 ≠ []) (w2 : WalkU D b2 d2 Z W P2) (h2 : P2 ≠ []) (nbX : NoBack D d X) (nbZ : NoBack D d2 Z) : Z = X := by
  obtain ⟨T1, -, hT1, hp1, -⟩ := walkU_pos w1
  obtain ⟨T2, -, hT2, hp2, -⟩ := walkU_pos w2
  have hT1p := hp1 h1
  have hT2p := hp2 h2
  obtain ⟨κ, hκ, hκd⟩ := hpar.smul
  have hd2 : d2 ≠ 0 := hpar.ne_left
  -- coordinates
  have hZ : toV2 (Z - X) = ((T1 - T2 * κ) * d.1, (T1 - T2 * κ) * d.2) := by
    have a1 := congrArg Prod.fst hT1
    have a2 := congrArg Prod.snd hT1
    have b1 := congrArg Prod.fst hT2
    have b2 := congrArg Prod.snd hT2
    have c1 := congrArg Prod.fst hκd
    have c2 := congrArg Prod.snd hκd
    simp only at c1 c2
    simp only [toV2, PiLp.sub_apply] at a1 a2 b1 b2 ⊢
    rw [c1] at b1
    rw [c2] at b2
    ext <;> simp only <;> linarith
  have nbZ' : NoBack D d Z := NoBack.of_par hpar.symm nbZ
  have nbX' : NoBack D d2 X := NoBack.of_par hpar nbX
  rcases lt_trichotomy (T1 - T2 * κ) 0 with hlt | heq | hgt
  · exfalso
    have hX : toV2 (X - Z) = ((-(T1 - T2 * κ) / κ) * d2.1, (-(T1 - T2 * κ) / κ) * d2.2) := by
      have a1 := congrArg Prod.fst hZ
      have a2 := congrArg Prod.snd hZ
      have c1 := congrArg Prod.fst hκd
      have c2 := congrArg Prod.snd hκd
      simp only at c1 c2
      simp only [toV2, PiLp.sub_apply] at a1 a2 ⊢
      rw [c1, c2]
      have hκ0 : κ ≠ 0 := hκ.ne'
      ext <;> simp only <;> field_simp <;> linarith
    exact noBack_walkU hd2 w2 hT2 (by apply div_pos <;> linarith) (by rw [div_le_iff₀ hκ]; nlinarith) hX nbX'
  · apply pt_eq_of_toV2 (H := X)
    rw [hZ, heq]
    unfold toV2; ext <;> simp
  · exfalso
    exact noBack_walkU hd w1 hT1 hgt (by nlinarith) hZ nbZ'

/-- Coordinates of a point of a step, read backwards. -/
theorem pt_rev {X A B P : Plane} {d : V2} {t0 t1 s : ℝ} (h0 : t0 ≤ s) (h1 : s < t1)
    (hA : toV2 (A - X) = (t0 * d.1, t0 * d.2)) (hB : toV2 (B - X) = (t1 * d.1, t1 * d.2))
    (hP : toV2 (P - X) = (s * d.1, s * d.2)) :
    P = B + ((t1 - s) / (t1 - t0)) • (A - B) := by
  have hne : t1 - t0 ≠ 0 := by intro h; linarith
  apply pt_eq_of_toV2 (H := X)
  have a1 := congrArg Prod.fst hA
  have a2 := congrArg Prod.snd hA
  have b1 := congrArg Prod.fst hB
  have b2 := congrArg Prod.snd hB
  simp only [toV2, PiLp.sub_apply] at a1 a2 b1 b2 hP ⊢
  rw [hP]
  ext <;> simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] <;> field_simp <;> nlinarith [a1, a2, b1, b2]

/-- **Opposite orientation**: a walk of direction `d2` with `d2` opposite to `d`, ending at `W` (on the segment of the walk `Lr` of side `false`), has its start at parameter `>= T`
(beyond the end of the segment) as soon as no tile lies behind its start. -/
theorem align_opp (D : RegionDissection N) {b2 : Bool} {d d2 : V2} {X Y Z W : Plane} {Lr P2 : List (Fin N × Plane × Plane)} (hd : d ≠ 0) (hpar : Par d2 (neg2 d))
    (wr : WalkU D false d X Y Lr) (w2 : WalkU D b2 d2 Z W P2) (h2 : P2 ≠ []) (nbZ : NoBack D d2 Z)
    {s T : ℝ} (hs : 0 ≤ s) (hW : toV2 (W - X) = (s * d.1, s * d.2)) (hT : toV2 (Y - X) = (T * d.1, T * d.2)) :
    ∃ z : ℝ, toV2 (Z - X) = (z * d.1, z * d.2) ∧ T ≤ z := by
  obtain ⟨T2, -, hT2, hp2, -⟩ := walkU_pos w2
  have hT2p := hp2 h2
  obtain ⟨κ, hκ, hκd⟩ := hpar.smul
  have hZ : toV2 (Z - X) = ((s + T2 * κ) * d.1, (s + T2 * κ) * d.2) := by
    have b1 := congrArg Prod.fst hT2
    have b2 := congrArg Prod.snd hT2
    have c1 := congrArg Prod.fst hκd
    have c2 := congrArg Prod.snd hκd
    have a1 := congrArg Prod.fst hW
    have a2 := congrArg Prod.snd hW
    simp only [neg2] at c1 c2
    simp only [toV2, PiLp.sub_apply] at a1 a2 b1 b2 ⊢
    rw [c1] at b1
    rw [c2] at b2
    ext <;> simp only <;> linarith
  refine ⟨s + T2 * κ, hZ, ?_⟩
  by_contra hlt
  push_neg at hlt
  have hz0 : 0 ≤ s + T2 * κ := by nlinarith
  obtain ⟨e, he, t0, t1, h0, h1, ht0, hz1⟩ := walkU_cover wr hd hT _ hz0 hlt
  have hS := walkU_mem_step wr e he
  simp only [StepU, Bool.false_eq_true, if_false] at hS
  have hS' : TriStep (D.tile e.1) d2 e.2.2 e.2.1 := TriStep.of_par hpar hS
  have hne : t0 < t1 := lt_of_le_of_lt ht0 hz1
  have hσ0 : 0 < (t1 - (s + T2 * κ)) / (t1 - t0) := div_pos (by linarith) (by linarith)
  have hσ1 : (t1 - (s + T2 * κ)) / (t1 - t0) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  exact nbZ.1 e.1 e.2.2 e.2.1 _ hS' hσ0 hσ1 (pt_rev ht0 hz1 h0 h1 hZ)

theorem stepU_end_vertex {D : RegionDissection N} {b : Bool} {d : V2} {e : Fin N × Plane × Plane} (h : StepU D b d e) :
    ∃ k, (D.tile e.1).pts k = e.2.2 := by
  cases b
  · simp only [StepU, Bool.false_eq_true, if_false] at h
    obtain ⟨kk, f, g, hk, hf, -⟩ := h
    exact ⟨kk, hk⟩
  · simp only [StepU, if_true] at h
    obtain ⟨kk, f, g, hk, hf, -⟩ := h
    exact ⟨f, hf⟩

/-- A straight sector at an inner point of a step: the fan at `W` has a tile with a straight sector along `±d`. -/
theorem straight_of_step {D : RegionDissection N} {b : Bool} {d : V2} {W : Plane} {κ : Type} [Fintype κ] (F : ExtFan D W κ)
    {g : Fin N × Plane × Plane} (hS : StepU D b d g) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hWg : W = g.2.1 + σ • (g.2.2 - g.2.1)) :
    ∃ sg : AtV D W, F.q sg = (-(F.p sg).1, -(F.p sg).2) ∧ (Par (F.p sg) d ∨ Par (F.p sg) (neg2 d)) := by
  cases b
  · simp only [StepU, Bool.false_eq_true, if_false] at hS
    obtain ⟨hmem, hnv, hline⟩ := step_interior_pt hS (σ := 1 - σ) (by linarith) (by linarith)
    have hWs : g.2.2 + (1 - σ) • (g.2.1 - g.2.2) = W := by rw [hWg]; ext i; simp; ring
    rw [hWs] at hmem hnv hline
    set sg : AtV D W := ⟨g.1, hmem⟩
    obtain ⟨hp, hq⟩ := straight_dir sg (F.hok sg) (F.hloc sg) (F.hspec sg) hnv hS hline
    exact ⟨sg, hq, Or.inr hp⟩
  · simp only [StepU, if_true] at hS
    obtain ⟨hmem, hnv, hline⟩ := step_interior_pt hS hσ0 hσ1
    rw [← hWg] at hmem hnv hline
    set sg : AtV D W := ⟨g.1, hmem⟩
    obtain ⟨hp, hq⟩ := straight_dir sg (F.hok sg) (F.hloc sg) (F.hspec sg) hnv hS hline
    exact ⟨sg, hq, Or.inl hp⟩

theorem par_dichotomy {p x y d d2 : V2} (hx : x = d ∨ x = neg2 d) (hy : y = d2 ∨ y = neg2 d2) (h1 : Par p x) (h2 : Par p y) :
    Par d2 d ∨ Par d2 (neg2 d) := by
  have hxy : Par x y := h1.symm.trans h2
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact Or.inl hxy.symm
  · right
    have := par_neg hxy
    have e : ((-(neg2 d2).1, -(neg2 d2).2) : V2) = d2 := neg2_neg2 d2
    rw [e] at this
    exact this.symm
  · exact Or.inr hxy.symm
  · left
    exact (par_neg2 hxy).symm

/-- **Arrival** (proof of Laczkovich's Lemma 4.6, "if an inner point `W` of `XY` is the endpoint of an edge `ZW` then `Z` is `X` or `Y`"). -/
theorem arrival_of_caseC (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx) : Arrival D := by
  classical
  intro d X Y W Z bA LA LB hd hnb wA wB hLA hLB nc1 nc2 hWB hWA hZW
  have hG := h.caseG
  haveI : HasFansC (relabelC D).toRegionDissection := (inferInstance : HasFansC D.toRegionDissection)
  obtain ⟨f, hf, hfW⟩ := hWB
  obtain ⟨g, hg, σ, hσ0, hσ1, hWg⟩ := hWA
  have hfS : StepU D.toRegionDissection (!bA) d f := walkU_mem_step wB f hf
  have hgS : StepU D.toRegionDissection bA d g := walkU_mem_step wA g hg
  obtain ⟨kf, hkf⟩ := stepU_end_vertex hfS
  rw [hfW] at hkf
  have hvert : ∃ j k, (D.tile j).pts k = W := ⟨f.1, kf, hkf⟩
  obtain ⟨κ, _, ⟨F⟩⟩ := HasFansC.fans (D := D.toRegionDissection) W hvert
  -- the straight sector of the segment at `W`, the corner of the other side
  obtain ⟨sg, hqg, hpg⟩ := straight_of_step F hgS hσ0 hσ1 hWg
  have hmemf : W ∈ (D.tile f.1).carrier := hkf ▸ subset_convexHull ℝ _ ⟨kf, rfl⟩
  set a : AtV D.toRegionDissection W := ⟨f.1, hmemf⟩
  have ha : 0 < crs (F.p a) (F.q a) := crs_pos_of_corner (F.hok a) (F.hspec a) ⟨kf, hkf⟩
  -- the edge `Z -> W`
  have hZW' := (gcEdge_iff D Z W).mp hZW
  obtain ⟨d2, hd2, nb2, hcase⟩ := ga_edge_data (relabelC D) (relabelCIdx idx) hG.hidx hG.hnc hZW' F
  -- both straight sectors coincide, hence `d2 ∥ d`
  have key : ∀ {y : V2} {s2 : AtV D.toRegionDissection W}, (y = d2 ∨ y = neg2 d2) → F.q s2 = (-(F.p s2).1, -(F.p s2).2) → Par (F.p s2) y →
      Par d2 d ∨ Par d2 (neg2 d) := by
    intro y s2 hy hq2 hp2
    have hss : sg = s2 := straight_unique F hqg hq2 ha
    subst hss
    rcases hpg with hpg | hpg
    · exact par_dichotomy (Or.inl rfl) hy hpg hp2
    · exact par_dichotomy (Or.inr rfl) hy hpg hp2
  obtain ⟨P1, w1, h1ne, -⟩ := walkU_prefix_end wB hf hfW
  obtain ⟨T, -, hT, -, -⟩ := walkU_pos wA
  obtain ⟨s, hs0, hsW, hsp, -⟩ := walkU_pos w1
  have hs : 0 < s := hsp h1ne
  -- the false-side division of the segment
  have hLr : ∃ Lr, WalkU D.toRegionDissection false d X Y Lr := by
    cases bA
    · exact ⟨LA, wA⟩
    · exact ⟨LB, by simpa using wB⟩
  obtain ⟨Lr, wr⟩ := hLr
  rcases hcase with ⟨P2, w2T, h2ne, a2, b2, s2, hLF⟩ | ⟨P2, w2R, h2ne, a2, b2, s2, hRF⟩
  · obtain ⟨-, -, -, -, hps, hqs, -⟩ := hLF
    have hdi := key (Or.inr rfl) hqs hps
    have w2 := walkU_of_T w2T
    rcases hdi with hpar | hpar
    · left
      exact align_same D.toRegionDissection hd hpar w1 h1ne w2 h2ne hnb nb2
    · right
      obtain ⟨z, hz, hTz⟩ := align_opp D.toRegionDissection hd hpar wr w2 h2ne nb2 hs0 hsW hT
      exact ⟨z, T, hz, hT, hTz⟩
  · obtain ⟨-, -, -, -, hps, hqs, -⟩ := hRF
    have hdi := key (Or.inl rfl) hqs hps
    have w2 := walkU_of_R w2R
    rcases hdi with hpar | hpar
    · left
      exact align_same D.toRegionDissection hd hpar w1 h1ne w2 h2ne hnb nb2
    · right
      obtain ⟨z, hz, hTz⟩ := align_opp D.toRegionDissection hd hpar wr w2 h2ne nb2 hs0 hsW hT
      exact ⟨z, T, hz, hT, hTz⟩

end Erdos634.Draft.LaczFormal.RG

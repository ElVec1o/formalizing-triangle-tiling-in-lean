import Erdos634.Refl.RunE120
import Erdos634.Refl.SoundE4
import Erdos634.NormalPosition

/-! Refl/BridgeE120.lean -- reflective refutation of the `(3,5,7)` tile in the equilateral side-15 target (GapE120 instance):
    target `(0,0),(15,0),(15/2, 15/2 √3)`, tile sides `(3,5,7)` (angle 2π/3 between the sides 3 and 5),
    `Refl.checkAllR_sound` on the chunked 1860-node certificate of `DataE120`/`RunE120` with the NormalPosition lift,
    mirroring `Refl.BridgeB`.  Result `not_dissection_refl`: no `CongruentDissection` (any `N`) has target congruent to `TGT`
    and model congruent to `MODEL`.  UNAUDITED. -/

open Erdos634.CertNode Erdos634.Geometry Erdos634.CertCoord

namespace Refl.BridgeE120

theorem hD3 : (0:ℝ) < 3 := by norm_num

theorem TGT_pos : 0 < ef 0 0 15 0 (15/2) (15/2) := by unfold ef; norm_num
/-- The target `(0, 0)`, `(15, 0)`, `(15/2, 15/2·r)` with `r = √3`: equilateral of side 15. -/
noncomputable def TGT : Erdos634.Geometry.Tri := rtri 3 hD3 0 0 15 0 (15/2) (15/2) TGT_pos
theorem MODEL_pos : 0 < ef 0 0 3 0 (11/2) (5/2) := by unfold ef; norm_num
/-- The model tile `(0, 0)`, `(3, 0)`, `(11/2, 5/2·r)`: sides `3, 5, 7`. -/
noncomputable def MODEL : Erdos634.Geometry.Tri := rtri 3 hD3 0 0 3 0 (11/2) (5/2) MODEL_pos
theorem MODEL_sides : dist (MODEL.pts 0) (MODEL.pts 1) = 3 ∧ dist (MODEL.pts 1) (MODEL.pts 2) = 5 ∧
    dist (MODEL.pts 0) (MODEL.pts 2) = 7 :=
  model_sides_rp hD3 MODEL_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem wE_base : instE120.baseY = true := by decide +kernel

theorem tgt_ok : instE120.tgt.ok = true := by decide +kernel

theorem tgt_carr : instE120.tgt.carr 3 = TGT.carrier := by
  obtain ⟨hp, h⟩ := Tri.ok_sem 3 hD3 instE120.tgt tgt_ok
  rw [h]
  have e1 : instE120.tgt.a.X = 0 := by simp [instE120, pt, Pt.X]
  have e2 : instE120.tgt.a.Y = 0 := by simp [instE120, pt, Pt.Y]
  have e3 : instE120.tgt.b.X = 15 := by simp [instE120, pt, Pt.X]
  have e4 : instE120.tgt.b.Y = 0 := by simp [instE120, pt, Pt.Y]
  have e5 : instE120.tgt.c.X = 15/2 := by simp [instE120, pt, Pt.X]
  have e6 : instE120.tgt.c.Y = 15/2 := by simp [instE120, pt, Pt.Y]
  unfold TGT
  simp only [e1, e2, e3, e4, e5, e6]

theorem hMa' : dist (MODEL.pts 0) (MODEL.pts 1) = (instE120.sides.1 : ℝ) := by simpa [instE120] using MODEL_sides.1
theorem hMb' : dist (MODEL.pts 1) (MODEL.pts 2) = (instE120.sides.2.1 : ℝ) := by simpa [instE120] using MODEL_sides.2.1
theorem hMc' : dist (MODEL.pts 0) (MODEL.pts 2) = (instE120.sides.2.2 : ℝ) := by simpa [instE120] using MODEL_sides.2.2
theorem sound_0 : Sound 3 instE120 MODEL chunkCfgE0 :=
  checkNodeE_sound 3 hD3 instE120 (by norm_num [instE120]) MODEL hMa' hMb' hMc' instE120_ok wE_base 400 chunkCfgE0 chunkE0
    (fun t ht => List.all_eq_true.mp cfgOkE120_0 t ht) chunkE120_0
theorem sound_1 : Sound 3 instE120 MODEL chunkCfgE1 :=
  checkNodeE_sound 3 hD3 instE120 (by norm_num [instE120]) MODEL hMa' hMb' hMc' instE120_ok wE_base 400 chunkCfgE1 chunkE1
    (fun t ht => List.all_eq_true.mp cfgOkE120_1 t ht) chunkE120_1
theorem sound_2 : Sound 3 instE120 MODEL chunkCfgE2 :=
  checkNodeE_sound 3 hD3 instE120 (by norm_num [instE120]) MODEL hMa' hMb' hMc' instE120_ok wE_base 400 chunkCfgE2 chunkE2
    (fun t ht => List.all_eq_true.mp cfgOkE120_2 t ht) chunkE120_2
theorem sound_3 : Sound 3 instE120 MODEL chunkCfgE3 :=
  checkNodeE_sound 3 hD3 instE120 (by norm_num [instE120]) MODEL hMa' hMb' hMc' instE120_ok wE_base 400 chunkCfgE3 chunkE3
    (fun t ht => List.all_eq_true.mp cfgOkE120_3 t ht) chunkE120_3
theorem sound_4 : Sound 3 instE120 MODEL chunkCfgE4 :=
  checkNodeE_sound 3 hD3 instE120 (by norm_num [instE120]) MODEL hMa' hMb' hMc' instE120_ok wE_base 400 chunkCfgE4 chunkE4
    (fun t ht => List.all_eq_true.mp cfgOkE120_4 t ht) chunkE120_4
theorem sound_5 : Sound 3 instE120 MODEL chunkCfgE5 :=
  checkNodeE_sound 3 hD3 instE120 (by norm_num [instE120]) MODEL hMa' hMb' hMc' instE120_ok wE_base 400 chunkCfgE5 chunkE5
    (fun t ht => List.all_eq_true.mp cfgOkE120_5 t ht) chunkE120_5
theorem sound_6 : Sound 3 instE120 MODEL chunkCfgE6 :=
  checkNodeE_sound 3 hD3 instE120 (by norm_num [instE120]) MODEL hMa' hMb' hMc' instE120_ok wE_base 400 chunkCfgE6 chunkE6
    (fun t ht => List.all_eq_true.mp cfgOkE120_6 t ht) chunkE120_6
theorem sound_7 : Sound 3 instE120 MODEL chunkCfgE7 :=
  checkNodeE_sound 3 hD3 instE120 (by norm_num [instE120]) MODEL hMa' hMb' hMc' instE120_ok wE_base 400 chunkCfgE7 chunkE7
    (fun t ht => List.all_eq_true.mp cfgOkE120_7 t ht) chunkE120_7
theorem sound_8 : Sound 3 instE120 MODEL chunkCfgE8 :=
  checkNodeE_sound 3 hD3 instE120 (by norm_num [instE120]) MODEL hMa' hMb' hMc' instE120_ok wE_base 400 chunkCfgE8 chunkE8
    (fun t ht => List.all_eq_true.mp cfgOkE120_8 t ht) chunkE120_8
theorem sound_9 : Sound 3 instE120 MODEL chunkCfgE9 :=
  checkNodeE_sound 3 hD3 instE120 (by norm_num [instE120]) MODEL hMa' hMb' hMc' instE120_ok wE_base 400 chunkCfgE9 chunkE9
    (fun t ht => List.all_eq_true.mp cfgOkE120_9 t ht) chunkE120_9
theorem sound_10 : Sound 3 instE120 MODEL chunkCfgE10 :=
  checkNodeE_sound 3 hD3 instE120 (by norm_num [instE120]) MODEL hMa' hMb' hMc' instE120_ok wE_base 400 chunkCfgE10 chunkE10
    (fun t ht => List.all_eq_true.mp cfgOkE120_10 t ht) chunkE120_10
theorem sound_11 : Sound 3 instE120 MODEL chunkCfgE11 :=
  checkNodeE_sound 3 hD3 instE120 (by norm_num [instE120]) MODEL hMa' hMb' hMc' instE120_ok wE_base 400 chunkCfgE11 chunkE11
    (fun t ht => List.all_eq_true.mp cfgOkE120_11 t ht) chunkE120_11
theorem sound_12 : Sound 3 instE120 MODEL chunkCfgE12 :=
  checkNodeE_sound 3 hD3 instE120 (by norm_num [instE120]) MODEL hMa' hMb' hMc' instE120_ok wE_base 400 chunkCfgE12 chunkE12
    (fun t ht => List.all_eq_true.mp cfgOkE120_12 t ht) chunkE120_12
theorem sound_13 : Sound 3 instE120 MODEL chunkCfgE13 :=
  checkNodeE_sound 3 hD3 instE120 (by norm_num [instE120]) MODEL hMa' hMb' hMc' instE120_ok wE_base 400 chunkCfgE13 chunkE13
    (fun t ht => List.all_eq_true.mp cfgOkE120_13 t ht) chunkE120_13
theorem sound_14 : Sound 3 instE120 MODEL chunkCfgE14 :=
  checkNodeE_sound 3 hD3 instE120 (by norm_num [instE120]) MODEL hMa' hMb' hMc' instE120_ok wE_base 400 chunkCfgE14 chunkE14
    (fun t ht => List.all_eq_true.mp cfgOkE120_14 t ht) chunkE120_14
theorem sound_15 : Sound 3 instE120 MODEL chunkCfgE15 :=
  checkNodeE_sound 3 hD3 instE120 (by norm_num [instE120]) MODEL hMa' hMb' hMc' instE120_ok wE_base 400 chunkCfgE15 chunkE15
    (fun t ht => List.all_eq_true.mp cfgOkE120_15 t ht) chunkE120_15
theorem sound_16 : Sound 3 instE120 MODEL chunkCfgE16 :=
  checkNodeE_sound 3 hD3 instE120 (by norm_num [instE120]) MODEL hMa' hMb' hMc' instE120_ok wE_base 400 chunkCfgE16 chunkE16
    (fun t ht => List.all_eq_true.mp cfgOkE120_16 t ht) chunkE120_16
theorem sound_17 : Sound 3 instE120 MODEL chunkCfgE17 :=
  checkNodeE_sound 3 hD3 instE120 (by norm_num [instE120]) MODEL hMa' hMb' hMc' instE120_ok wE_base 400 chunkCfgE17 chunkE17
    (fun t ht => List.all_eq_true.mp cfgOkE120_17 t ht) chunkE120_17
theorem sound_18 : Sound 3 instE120 MODEL chunkCfgE18 :=
  checkNodeE_sound 3 hD3 instE120 (by norm_num [instE120]) MODEL hMa' hMb' hMc' instE120_ok wE_base 400 chunkCfgE18 chunkE18
    (fun t ht => List.all_eq_true.mp cfgOkE120_18 t ht) chunkE120_18
theorem sound_19 : Sound 3 instE120 MODEL chunkCfgE19 :=
  checkNodeE_sound 3 hD3 instE120 (by norm_num [instE120]) MODEL hMa' hMb' hMc' instE120_ok wE_base 400 chunkCfgE19 chunkE19
    (fun t ht => List.all_eq_true.mp cfgOkE120_19 t ht) chunkE120_19
theorem sound_20 : Sound 3 instE120 MODEL chunkCfgE20 :=
  checkNodeE_sound 3 hD3 instE120 (by norm_num [instE120]) MODEL hMa' hMb' hMc' instE120_ok wE_base 400 chunkCfgE20 chunkE20
    (fun t ht => List.all_eq_true.mp cfgOkE120_20 t ht) chunkE120_20
theorem sound_21 : Sound 3 instE120 MODEL chunkCfgE21 :=
  checkNodeE_sound 3 hD3 instE120 (by norm_num [instE120]) MODEL hMa' hMb' hMc' instE120_ok wE_base 400 chunkCfgE21 chunkE21
    (fun t ht => List.all_eq_true.mp cfgOkE120_21 t ht) chunkE120_21

theorem known_sound : ∀ c ∈ knownE120, Sound 3 instE120 MODEL c := by
  intro c hc
  simp only [knownE120, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sound_0
  · exact sound_1
  · exact sound_2
  · exact sound_3
  · exact sound_4
  · exact sound_5
  · exact sound_6
  · exact sound_7
  · exact sound_8
  · exact sound_9
  · exact sound_10
  · exact sound_11
  · exact sound_12
  · exact sound_13
  · exact sound_14
  · exact sound_15
  · exact sound_16
  · exact sound_17
  · exact sound_18
  · exact sound_19
  · exact sound_20
  · exact sound_21

theorem not_dissection_refl {N : ℕ} (D : CongruentDissection N)
    (hT : D.target.Congruent TGT) (hM : D.model.Congruent MODEL) : False := by
  obtain ⟨g, D', hD'T, hD'M, -⟩ := Erdos634.NormalPosition.exists_normal_position_congruent D hT
  obtain ⟨hMa, hMb, hMc⟩ := MODEL_sides
  have S : Sound 3 instE120 MODEL [] := checkAllR_sound 3 hD3 instE120 (by norm_num [instE120]) MODEL
    (by simpa [instE120] using hMa) (by simpa [instE120] using hMb) (by simpa [instE120] using hMc)
    wE_base knownE120 known_sound 400 treeE120 topE120
  exact S (N := N) D' (by rw [hD'T, tgt_carr]) (by rw [hD'M]; exact hM) (by simp)

end Refl.BridgeE120
#print axioms Refl.BridgeE120.not_dissection_refl

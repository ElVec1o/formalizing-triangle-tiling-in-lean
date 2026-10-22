-- Draft/LaczFormalIIcIsoWitC.lean -- NON-VACUITY witness for `IIcIsoCore`, step C: covering, pairwise disjointness, congruence; `octDiss : CongruentRegionDissection 8`.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcIsoWitB

open Erdos634.Geometry Erdos634.CertCoord Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Thm21

namespace Erdos634.Draft.LaczFormal.IsoWit

/-- spoke functional `s_a(x) = cx a * x1 - cy a * x0` -/
noncomputable def sp (a : Fin 8) (x : Plane) : ℝ := cx a * x 1 - cy a * x 0

theorem sp_add4 (a : Fin 8) (x : Plane) : sp (a + 4) x = - sp a x := by
  unfold sp; rw [cx_add4, cy_add4]; ring

theorem sector_exists (x : Plane) : ∃ i : Fin 8, 0 ≤ sp i x ∧ sp (i + 1) x ≤ 0 := by
  by_contra H
  push_neg at H
  have hex : ∃ a : Fin 8, 0 ≤ sp a x := by
    by_cases h0 : 0 ≤ sp 0 x
    · exact ⟨0, h0⟩
    · refine ⟨4, ?_⟩
      have := sp_add4 0 x
      have e : (0 : Fin 8) + 4 = 4 := by decide
      rw [e] at this
      linarith [not_le.mp h0]
  obtain ⟨a, ha⟩ := hex
  have h1 := H a ha
  have h2 := H (a + 1) h1.le
  have h3 := H (a + 1 + 1) h2.le
  have h4 := H (a + 1 + 1 + 1) h3.le
  have e : a + 1 + 1 + 1 + 1 = a + 4 := (by decide : ∀ b : Fin 8, b + 1 + 1 + 1 + 1 = b + 4) a
  rw [e, sp_add4] at h4
  linarith

theorem oct_sub (x : Plane) (hx : x ∈ oct.carrier) : ∃ i, x ∈ (tile i).carrier := by
  obtain ⟨i, hi0, hi1⟩ := sector_exists x
  refine ⟨i, ?_⟩
  have hxe : x = mkPt (x 0) (x 1) := by
    ext m; fin_cases m <;> simp
  rw [mem_oct] at hx
  have hD : 0 < det3 (cx i) (cy i) (cx (i + 1)) (cy (i + 1)) 0 0 := by
    have : det3 (cx i) (cy i) (cx (i + 1)) (cy (i + 1)) 0 0 = hh := by
      rw [← cr_1 i]; unfold det3 cr; ring
    rw [this]; exact hh_pos
  have key := mem_carrier_of_dets (a := x 0) (b := x 1) hD ?_ ?_ ?_
  · rw [hxe]; exact key
  · unfold sp at hi1; unfold det3; nlinarith
  · unfold sp at hi0; unfold det3; nlinarith
  · have := hx i; unfold det3; nlinarith


theorem sep_exists (i j : Fin 8) (h : i ≠ j) : ∃ a : Fin 8, cr a i ≤ 0 ∧ cr a (i + 1) ≤ 0 ∧ 0 ≤ cr a j ∧ 0 ≤ cr a (j + 1) := by
  have := hh_pos
  fin_cases i <;> fin_cases j <;> first
    | exact absurd rfl h
    | (refine ⟨0, ?_⟩; simp [cr, cx, cy] <;> (try refine ⟨?_, ?_, ?_, ?_⟩) <;> linarith)
    | (refine ⟨1, ?_⟩; simp [cr, cx, cy] <;> (try refine ⟨?_, ?_, ?_, ?_⟩) <;> linarith)
    | (refine ⟨2, ?_⟩; simp [cr, cx, cy] <;> (try refine ⟨?_, ?_, ?_, ?_⟩) <;> linarith)
    | (refine ⟨3, ?_⟩; simp [cr, cx, cy] <;> (try refine ⟨?_, ?_, ?_, ?_⟩) <;> linarith)
    | (refine ⟨4, ?_⟩; simp [cr, cx, cy] <;> (try refine ⟨?_, ?_, ?_, ?_⟩) <;> linarith)
    | (refine ⟨5, ?_⟩; simp [cr, cx, cy] <;> (try refine ⟨?_, ?_, ?_, ?_⟩) <;> linarith)
    | (refine ⟨6, ?_⟩; simp [cr, cx, cy] <;> (try refine ⟨?_, ?_, ?_, ?_⟩) <;> linarith)
    | (refine ⟨7, ?_⟩; simp [cr, cx, cy] <;> (try refine ⟨?_, ?_, ?_, ?_⟩) <;> linarith)

end Erdos634.Draft.LaczFormal.IsoWit

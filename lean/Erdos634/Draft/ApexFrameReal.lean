-- Draft/ApexFrameReal.lean — the frame-conditioned results of Draft/HalfTurnR3R4Glue.lean and
-- Draft/TileIdent.lean, restated about a REAL congruent dissection of the m = 1 base-β target.
-- Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- `ApexLegWord.exists_hframe_m1` builds an `HFrame` from any such dissection (every field derived:
-- apex placement, clause (2) at m = 1, the metric of r).  Composing, each result below that used to
-- take `F : HFrame …` as a hypothesis becomes a statement about `D` alone, whose conclusion names
-- the frame's points (so it is stated as `∃ F : HFrame D e f α β γ, …`: the frame IS the apex
-- configuration of `D`, `F.A` its apex, `F.V`, `F.P` = P′ the vertices of `T₂`, `F.h` the normal of
-- the mismatch ray r).  All proofs are one-line compositions; nothing here is new mathematics.
--
-- Build (scratch oleans; never .lake): ApexPlacement, ApexLegWord, TileIdent oleans in $S, then
--   lake env bash -c 'LEAN_PATH=$S:$LEAN_PATH lean Erdos634/Draft/ApexFrameReal.lean'
import Erdos634.Draft.ApexLegWord
import Erdos634.Draft.TileIdent

namespace Erdos634.Draft.ApexFrameReal

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.HalfTurnR3R4Glue

variable {N : ℕ}

/-- **A congruent dissection of the `m = 1` base-β target, as the paper states it** (apex `k`,
coprime member `2 ≤ e ≤ f − 2`, tile `(ef, f² − e², f²)` with its angle data). -/
structure M1Data (D : CongruentDissection N) (e f : ℕ) (α β γ : ℝ) (k : Fin 3) : Prop where
  hco : Nat.Coprime e f
  he : 2 ≤ e
  hef : e + 2 ≤ f
  hM : ModelDataE D e f α β γ
  hAng : MarchSlots.AngleData α β γ
  hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = 3 * α
  hβ1 : cornerAngle (D.target.pts (k + 2)) (D.target.pts (k + 1)) (D.target.pts k) = β
  hβ2 : cornerAngle (D.target.pts k) (D.target.pts (k + 2)) (D.target.pts (k + 1)) = β
  hleg1 : dist (D.target.pts k) (D.target.pts (k + 1)) = (f : ℝ) ^ 3
  hleg2 : dist (D.target.pts k) (D.target.pts (k + 2)) = (f : ℝ) ^ 3
  hbase : dist (D.target.pts (k + 1)) (D.target.pts (k + 2))
    = (e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)

theorem frame {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {k : Fin 3}
    (h : M1Data D e f α β γ k) : Nonempty (HFrame D e f α β γ) :=
  ApexLegWord.exists_hframe_m1 D h.hco h.he h.hef h.hM h.hAng k h.hcorner h.hβ1 h.hβ2 h.hleg1
    h.hleg2 h.hbase

/-- **`cor:noTP`'s input, for a real dissection: two `γ`'s at `P′`** (`T₂` and `T₃` both present
`γ` there — each has its `c`-side opposite `P′`).  REDISCOVERY: this is `TileIdent.t2_t3_gamma`
(Draft), restated with the two vertex sets; the new content is only its `_real` form below. -/
theorem two_gamma_at_pprime {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ}
    (F : HFrame D e f α β γ) :
    ∃ i2 i3 : Fin N, i2 ≠ i3 ∧ Set.range (D.tile i2).pts = {F.A, F.V, F.P} ∧
      Set.range (D.tile i3).pts = {F.A, F.P, F.A + ((f : ℝ) ^ 2) • F.uL} ∧
      (D.tile i2).localAngle F.P = γ ∧ (D.tile i3).localAngle F.P = γ := by
  obtain ⟨hab, hac, hbc⟩ := sides_distinct F.hco F.he (by have := F.hef; omega)
  have hloc := fun {i : Fin N} {P Q R : Plane} (hr : Set.range (D.tile i).pts = {P, Q, R}) =>
    localAngle_of_rangeE D hab hac hbc F.hM.hs0 F.hM.hs1 F.hM.hs2 F.hM.hα' F.hM.hβ' F.hM.hγ' hr
  have hf2 : (0 : ℝ) ≤ (f : ℝ) ^ 2 := by positivity
  have hAV : dist F.A F.V = (f : ℝ) ^ 2 := by rw [F.hV]; exact dist_self_add_unit F.huR hf2
  have hAJ : dist F.A (F.A + ((f : ℝ) ^ 2) • F.uL) = (f : ℝ) ^ 2 := dist_self_add_unit F.huL hf2
  obtain ⟨i2, h2⟩ := F.hT2
  obtain ⟨i3, h3⟩ := F.hT3
  have h2' : Set.range (D.tile i2).pts = {F.P, F.A, F.V} := by
    rw [h2]; ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have h3' : Set.range (D.tile i3).pts = {F.P, F.A, F.A + ((f : ℝ) ^ 2) • F.uL} := by
    rw [h3]; ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  refine ⟨i2, i3, ?_, h2, h3, (hloc h2').2.2 hAV, (hloc h3').2.2 hAJ⟩
  intro heq
  subst heq
  have hVmem : F.V ∈ ({F.A, F.P, F.A + ((f : ℝ) ^ 2) • F.uL} : Set Plane) := by
    rw [← h3, h2]; simp
  have hef := F.hef
  have he := F.he
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast he
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast hef
  have hfpos : (0 : ℝ) < f := by linarith
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hVmem
  rcases hVmem with hVA | hVP | hVJ
  · rw [hVA, dist_self] at hAV; nlinarith
  · have := F.hVP; rw [hVP, dist_self] at this; nlinarith
  · have huRL : F.uR = F.uL := by
      have h' : ((f : ℝ) ^ 2) • F.uR = ((f : ℝ) ^ 2) • F.uL := by
        have := hVJ; rw [F.hV] at this; exact add_left_cancel this
      exact smul_right_injective _ (by positivity : ((f : ℝ) ^ 2) ≠ 0) h'
    have hJ3 : F.A + ((f : ℝ) ^ 3) • F.uL ∈ D.target.carrier := by
      apply subset_convexHull ℝ _
      rw [F.htarget]; simp
    apply F.hrbase ((f : ℝ) * (e : ℝ) ^ 2) (by positivity)
    have : F.A + ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + (f : ℝ) * (e : ℝ) ^ 2) • F.uR
        = F.A + ((f : ℝ) ^ 3) • F.uL := by
      rw [huRL]; congr 2; ring
    rw [this]; exact hJ3

/-! ## The frame-conditioned results, for a real dissection -/

/-- `cor:noTP` input at `P′`, unconditional. -/
theorem two_gamma_at_pprime_real {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {k : Fin 3}
    (h : M1Data D e f α β γ k) :
    ∃ F : HFrame D e f α β γ, ∃ i2 i3 : Fin N, i2 ≠ i3 ∧
      Set.range (D.tile i2).pts = {F.A, F.V, F.P} ∧
      Set.range (D.tile i3).pts = {F.A, F.P, F.A + ((f : ℝ) ^ 2) • F.uL} ∧
      (D.tile i2).localAngle F.P = γ ∧ (D.tile i3).localAngle F.P = γ := by
  obtain ⟨F⟩ := frame h
  exact ⟨F, two_gamma_at_pprime F⟩

/-- **Lemma G steps 1–4 (the (H)/(M) split), for a real dissection.** -/
theorem lemmaG_real {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {k : Fin 3}
    (h : M1Data D e f α β γ k) :
    ∃ F : HFrame D e f α β γ,
      Present D F.K ∨ ∃ M : Plane, IsMirror F.A F.V F.P M ∧ Present D {F.V, F.P, M} := by
  obtain ⟨F⟩ := frame h
  exact ⟨F, TileIdent.lemmaG_frame F⟩

/-- **`V` is pierced (straddled on the mismatch ray `r`), for a real dissection.** -/
theorem V_pierced_real {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {k : Fin 3}
    (h : M1Data D e f α β γ k) :
    ∃ F : HFrame D e f α β γ,
      TraceCovering.Straddled D.toDissection (-F.h) (-(F.h F.A)) F.V := by
  obtain ⟨F⟩ := frame h
  exact ⟨F, HFrame.V_pierced F⟩

/-- **The chain points `A + j·c·u_r` are pierced once a pure `c`-chain reaches them, for a real
dissection.** -/
theorem chain_point_pierced_real {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {k : Fin 3}
    (h : M1Data D e f α β γ k) :
    ∃ F : HFrame D e f α β γ, ∀ j : ℕ, 1 ≤ j →
      (j : ℝ) * (f : ℝ) ^ 2 < (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) →
      (∀ i < j, ∃ ε ∈ F.near,
        EdgeIs D ε (F.rpt ((i : ℝ) * (f : ℝ) ^ 2)) (F.rpt (((i : ℝ) + 1) * (f : ℝ) ^ 2))) →
      TraceCovering.Straddled D.toDissection (-F.h) (-(F.h F.A))
        (F.A + ((j : ℝ) * (f : ℝ) ^ 2) • F.uR) := by
  obtain ⟨F⟩ := frame h
  exact ⟨F, fun j hj hjL hpure => HFrame.chain_point_pierced F j hj hjL hpure⟩

/-- **The figure at `P′` in branch (H), for a real dissection.** -/
theorem corners_at_pprime_real {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {k : Fin 3}
    (h : M1Data D e f α β γ k) :
    ∃ F : HFrame D e f α β γ, Present D F.K →
      ∃ i2 i3 k' : Fin N, i2 ≠ i3 ∧ (D.tile i2).localAngle F.P = γ ∧
        (D.tile i3).localAngle F.P = γ ∧ (D.tile k').localAngle F.P = β := by
  obtain ⟨F⟩ := frame h
  exact ⟨F, fun hK => HFrame.corners_at_pprime F hK⟩

/-- **Half of R4(a) at `P′` (`pprime_band_alpha_T2P`), for a real dissection.** -/
theorem pprime_band_alpha_T2P_real {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ}
    {k : Fin 3} (h : M1Data D e f α β γ k) :
    ∃ F : HFrame D e f α β γ, Present D F.K →
      ∃ (j : Fin N) (Lε : ℝ), 0 < Lε ∧ (∃ ε ∈ F.band, EdgeIs D ε F.P (F.P + Lε • F.uR)) ∧
        (∃ m' : Fin 3, (D.tile j).pts m' = F.P) ∧
        (Lε = (f : ℝ) ^ 2 → (D.tile j).localAngle F.P = α → Present D F.T2P) := by
  obtain ⟨F⟩ := frame h
  exact ⟨F, fun hK => TileIdent.pprime_band_alpha_T2P F hK⟩

end Erdos634.Draft.ApexFrameReal

#print axioms Erdos634.Draft.ApexFrameReal.frame
#print axioms Erdos634.Draft.ApexFrameReal.two_gamma_at_pprime
#print axioms Erdos634.Draft.ApexFrameReal.two_gamma_at_pprime_real
#print axioms Erdos634.Draft.ApexFrameReal.lemmaG_real
#print axioms Erdos634.Draft.ApexFrameReal.V_pierced_real
#print axioms Erdos634.Draft.ApexFrameReal.chain_point_pierced_real
#print axioms Erdos634.Draft.ApexFrameReal.corners_at_pprime_real
#print axioms Erdos634.Draft.ApexFrameReal.pprime_band_alpha_T2P_real

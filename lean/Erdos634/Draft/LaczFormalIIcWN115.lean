-- Draft/LaczFormalIIcWN115.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3, Fig. 8), R4: the turns at a convex vertex `q t` of the corner polygon, for the chord arriving from `U` and the neighbour `q (t-1)` / `q (t+1)`.
-- `vertex_turn_pred`: (`sigma = 1`, `RotPos (Y-U) (N-Y) a`, `RotPos (Y-N) (U-Y) (-a)`) or (`sigma = -1`, ..., `-a`, `a`);  `vertex_turn_succ`: (`sigma = 1`, `-b`, `b`) or (`sigma = -1`, `b`, `-b`).
-- Route: `arrive_rot` (WN113) + `w_turn_*` (WN112) + the edge directions of the corner polygon (`IsCornerOfD`, WN109).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3, Fig. 5, 8), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN114
import Erdos634.Draft.LaczFormalIIcWN109

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG
open Erdos634.Draft.LaczFormal.WN (edgeSet wind extAng OrientOK RotPos IsCornerOfD)

local notation "tc" => Erdos634.Draft.LaczFormal.WN.toC

variable {N M : ℕ}

set_option maxHeartbeats 6400000 in
theorem vertex_turn [NeZero N] [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3)
    (G : AngGen (fun l => D.model.angleAt l))
    {m : ℕ} [NeZero m] (C : Fin m → Plane) (hCy : ∀ k : Fin m, GKite D idx (C k) (C (k + 1))) (hinj : Function.Injective C)
    (q : Fin M → ℂ) (hq : IsCornerOfD (cyc C) q) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (t : Fin M) (hturn : σ * extAng q t = D.model.angleAt 2) {U : Plane} (hU : GExc D idx U (Erdos634.Draft.LaczFormal.WN.toC.symm (q t))) :
    ∃ k : Fin m, q t = tc (C k) ∧
      ((σ = 1 ∧ RotPos (tc (C (k + 1)) - tc (C k)) (tc (C (k - 1)) - tc (C k)) (D.model.angleAt 0 + D.model.angleAt 1) ∧
          RotPos (tc (C (k + 1)) - tc (C k)) (tc U - tc (C k)) (Real.pi + D.model.angleAt 1)) ∨
       (σ = -1 ∧ RotPos (tc (C (k - 1)) - tc (C k)) (tc (C (k + 1)) - tc (C k)) (D.model.angleAt 0 + D.model.angleAt 1) ∧
          RotPos (tc (C (k - 1)) - tc (C k)) (tc U - tc (C k)) (Real.pi + D.model.angleAt 0))) ∧
      (∃ c : ℝ, 0 < c ∧ q (t + 1) - q t = (c : ℂ) * (tc (C (k + 1)) - tc (C k))) ∧
      (∃ c : ℝ, 0 < c ∧ q (t - 1) - q t = (c : ℂ) * (tc (C (k - 1)) - tc (C k))) := by
  obtain ⟨⟨⟨h3q, hqs, hqi, hqne, hqe, hqv⟩, hsurj⟩, hD⟩ := hq
  obtain ⟨k, hk, hf, hb⟩ := hD t
  obtain ⟨k', hk', hext⟩ := hqv t
  have hinjC : Function.Injective (cyc C) := fun a b h => hinj (Erdos634.Draft.LaczFormal.WN.toC.injective h)
  have hkk : k' = k := hinjC (hk'.symm.trans hk)
  subst hkk
  have hconv : σ * extAng (cyc C) k' = D.model.angleAt 2 := by rw [← hext]; exact hturn
  have hU' : GExc D idx U (C k') := by
    have : Erdos634.Draft.LaczFormal.WN.toC.symm (q t) = C k' := by
      rw [hk]; exact Erdos634.Draft.LaczFormal.WN.toC.symm_apply_apply _
    rw [this] at hU; exact hU
  refine ⟨k', hk, arrive_rot D P hreg idx hC h1 h3 G C hCy hσ k' hconv hU', ?_, ?_⟩
  · obtain ⟨c, hc, e⟩ := hf; exact ⟨c, hc, by rw [e]⟩
  · obtain ⟨c, hc, e⟩ := hb; exact ⟨c, hc, by rw [e]⟩

theorem vertex_turn_pred [NeZero N] [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3)
    (G : AngGen (fun l => D.model.angleAt l))
    {m : ℕ} [NeZero m] (C : Fin m → Plane) (hCy : ∀ k : Fin m, GKite D idx (C k) (C (k + 1))) (hinj : Function.Injective C)
    (q : Fin M → ℂ) (hq : IsCornerOfD (cyc C) q) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (t : Fin M) (hturn : σ * extAng q t = D.model.angleAt 2) {U : Plane} (hU : GExc D idx U (Erdos634.Draft.LaczFormal.WN.toC.symm (q t))) :
    (σ = 1 ∧ RotPos (q t - tc U) (q (t - 1) - q t) (D.model.angleAt 0) ∧ RotPos (q t - q (t - 1)) (tc U - q t) (-D.model.angleAt 0)) ∨
    (σ = -1 ∧ RotPos (q t - tc U) (q (t - 1) - q t) (-D.model.angleAt 0) ∧ RotPos (q t - q (t - 1)) (tc U - q t) (D.model.angleAt 0)) := by
  obtain ⟨k, hk, hcase, -, ⟨c, hc, hb⟩⟩ := vertex_turn D P hreg idx hC h1 h3 G C hCy hinj q hq hσ t hturn hU
  have hb' := hb
  rw [hk] at hb'
  have hN : RotPos (tc (C (k - 1)) - tc (C k)) (q (t - 1) - tc (C k)) 0 := ⟨c, hc, by rw [hb']; simp⟩
  rcases hcase with ⟨hs, ha, hb2⟩ | ⟨hs, ha, hb2⟩
  · left
    obtain ⟨r1, r2⟩ := Erdos634.Draft.LaczFormal.WN.w_turn_B_pred (a := D.model.angleAt 0) (b := D.model.angleAt 1) (N := q (t - 1)) ha hb2 hN
    rw [hk]
    exact ⟨hs, r1, r2⟩
  · right
    obtain ⟨r1, r2⟩ := Erdos634.Draft.LaczFormal.WN.w_turn_A_pred (a := D.model.angleAt 0) (b := D.model.angleAt 1) (Z := tc (C (k + 1))) (N := q (t - 1)) hb2 hN
    rw [hk]
    exact ⟨hs, r1, r2⟩

theorem vertex_turn_succ [NeZero N] [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3)
    (G : AngGen (fun l => D.model.angleAt l))
    {m : ℕ} [NeZero m] (C : Fin m → Plane) (hCy : ∀ k : Fin m, GKite D idx (C k) (C (k + 1))) (hinj : Function.Injective C)
    (q : Fin M → ℂ) (hq : IsCornerOfD (cyc C) q) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (t : Fin M) (hturn : σ * extAng q t = D.model.angleAt 2) {U : Plane} (hU : GExc D idx U (Erdos634.Draft.LaczFormal.WN.toC.symm (q t))) :
    (σ = 1 ∧ RotPos (q t - tc U) (q (t + 1) - q t) (-D.model.angleAt 1) ∧ RotPos (q t - q (t + 1)) (tc U - q t) (D.model.angleAt 1)) ∨
    (σ = -1 ∧ RotPos (q t - tc U) (q (t + 1) - q t) (D.model.angleAt 1) ∧ RotPos (q t - q (t + 1)) (tc U - q t) (-D.model.angleAt 1)) := by
  obtain ⟨k, hk, hcase, ⟨c, hc, hf⟩, -⟩ := vertex_turn D P hreg idx hC h1 h3 G C hCy hinj q hq hσ t hturn hU
  have hf' := hf
  rw [hk] at hf'
  have hN : RotPos (tc (C (k + 1)) - tc (C k)) (q (t + 1) - tc (C k)) 0 := ⟨c, hc, by rw [hf']; simp⟩
  rcases hcase with ⟨hs, ha, hb2⟩ | ⟨hs, ha, hb2⟩
  · left
    obtain ⟨r1, r2⟩ := Erdos634.Draft.LaczFormal.WN.w_turn_B_succ (a := D.model.angleAt 0) (b := D.model.angleAt 1) (X := tc (C (k - 1))) (N := q (t + 1)) hb2 hN
    rw [hk]
    exact ⟨hs, r1, r2⟩
  · right
    obtain ⟨r1, r2⟩ := Erdos634.Draft.LaczFormal.WN.w_turn_A_succ (a := D.model.angleAt 0) (b := D.model.angleAt 1) (N := q (t + 1)) ha hb2 hN
    rw [hk]
    exact ⟨hs, r1, r2⟩

#print axioms vertex_turn_pred
#print axioms vertex_turn_succ

end Erdos634.Draft.LaczFormal.RG

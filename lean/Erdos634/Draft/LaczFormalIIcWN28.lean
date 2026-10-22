-- Draft/LaczFormalIIcWN28.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2 ("Fig. 5"), second half of step (a): TURNING ANGLE at a vertex of a Gamma_kite chain.
-- If `XY` and `YZ` are consecutive edges of Gamma_kite then `Z - Y` is `X - Y` rotated by `beta + alpha + t*gamma`, `t in {0,1,2}`, i.e. the edge direction turns by `(t-1) gamma in {-gamma, 0, gamma}`.
-- Proof: the six tiles at the interior (2,2,2) vertex `Y` form a `Fan6` (fan222_tile); the two tiles of `XY` are adjacent sectors separated by the ray `YX` with two beta corners, the two tiles of `YZ`
-- adjacent sectors separated by the ray `YZ` with two alpha corners (step_start / step_end), and `fan_turn` (WN26) gives the rotation.  The straight case `t = 1` is NOT excluded here (the paper's Fig. 5
-- is not in the extracted text); it turns by 0 and does not affect the count `u - v = N`.
-- NOTE, UNAUDITED.  Hypotheses: the Case IIc block of `gkite_vertex_type` plus `AngGen`; NOT witnessed (no tiling with two consecutive Gamma_kite edges is exhibited).  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12Fan222Tile
import Erdos634.Draft.LaczFormalRG12GKiteEx
import Erdos634.Draft.LaczFormalIIcWN27

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

theorem rg_step_start {D : RegionDissection N} {V : Plane} {κ : Type} [Fintype κ] (F : ExtFan D V κ) {d : V2} {i : Fin N} {U' : Plane}
    (hS : TriStep (D.tile i) d V U') (hi : V ∈ (D.tile i).carrier) : Par (F.p ⟨i, hi⟩) d := by
  obtain ⟨kk, f, g, hk, -⟩ := id hS
  obtain ⟨kk', fl, hk', hp, hq⟩ := spec_corner_data (F.hspec ⟨i, hi⟩) ⟨kk, hk⟩
  exact triStep_start hS kk' fl hk' hp hq (F.hok _)

theorem rg_step_end {D : RegionDissection N} {V : Plane} {κ : Type} [Fintype κ] (F : ExtFan D V κ) {d : V2} {i : Fin N} {U : Plane}
    (hS : TriStep (D.tile i) d U V) (hi : V ∈ (D.tile i).carrier) : Par (F.q ⟨i, hi⟩) (-d.1, -d.2) := by
  obtain ⟨kk, f, g, hk, hf, -⟩ := id hS
  obtain ⟨kk', fl, hk', hp, hq⟩ := spec_corner_data (F.hspec ⟨i, hi⟩) ⟨f, hf⟩
  exact triStep_end hS kk' fl hk' hp hq (F.hok _)

theorem nsq_toV2 (A B : Plane) : nsq (toV2 (A - B)) = dist A B ^ 2 := by
  rw [dist_sq_plane]; simp [nsq, toV2]

set_option maxHeartbeats 3200000 in
/-- **Turning angle at a vertex of a Gamma_kite chain** (second half of step (a)). -/
theorem gkite_turn [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx)
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l)) {X Y Z : Plane}
    (hXY : GKite D idx X Y) (hYZ : GKite D idx Y Z) :
    ∃ t : ℕ, t ≤ 2 ∧ toV2 (Z - Y) =
      Graph.rot (D.model.angleAt 1 + D.model.angleAt 0 + (t : ℝ) * D.model.angleAt 2) (toV2 (X - Y)) := by
  classical
  obtain ⟨⟨hYi, c0, c1, c2⟩, -⟩ := gkite_vertex_type D P hreg idx hC.hidxA hC.hregc h1 h3 hXY
  obtain ⟨F, s, ℓ, hF, hlab, hsurj, hper⟩ := fan222_tile D idx hC.hidxA hYi c0 c1 c2 G
  obtain ⟨i, j, d, kk, f, kk', f', hij, hSi, hSj, hk, hf, hik, hif, hk', hf', hjk, hjf⟩ := hXY
  obtain ⟨i', j', d', kk2, f2, kk2', f2', hij2, hSi2, hSj2, hk2, hf2, hik2, hif2, hk2', hf2', hjk2, hjf2⟩ := hYZ
  have hmem : ∀ (t : Fin N) (k : Fin 3), (D.tile t).pts k = Y → Y ∈ (D.tile t).carrier := fun t k h => h ▸ tile_pt_mem _ k
  have hmi : Y ∈ (D.tile i).carrier := hmem i f hf
  have hmj : Y ∈ (D.tile j).carrier := hmem j kk' hk'
  have hmi2 : Y ∈ (D.tile i').carrier := hmem i' kk2 hk2
  have hmj2 : Y ∈ (D.tile j').carrier := hmem j' f2' hf2'
  obtain ⟨a, -, hsa⟩ := hsurj ⟨i, hmi⟩
  obtain ⟨b, -, hsb⟩ := hsurj ⟨j, hmj⟩
  obtain ⟨a', -, hsa'⟩ := hsurj ⟨i', hmi2⟩
  obtain ⟨b', -, hsb'⟩ := hsurj ⟨j', hmj2⟩
  have hlabel : ∀ n (t : Fin N) (k : Fin 3), (s n).1 = t → (D.tile t).pts k = Y → idx t k = ℓ n := by
    intro n t k hn hk0
    obtain ⟨k0, hk0', hl0⟩ := hlab n
    rw [hn] at hk0' hl0
    have : k0 = k := (D.tile t).indep.injective (hk0'.trans hk0.symm)
    rw [← hl0, this]
  have hℓa : ℓ a = 1 := by rw [← hlabel a i f (by rw [hsa]) hf, hif]
  have hℓb : ℓ b = 1 := by rw [← hlabel b j kk' (by rw [hsb]) hk', hjk]
  have hℓa' : ℓ a' = 0 := by rw [← hlabel a' i' kk2 (by rw [hsa']) hk2, hik2]
  have hℓb' : ℓ b' = 0 := by rw [← hlabel b' j' f2' (by rw [hsb']) hf2', hjf2]
  have hl6 : ∀ n, ℓ (n + 6) = ℓ n := by
    intro n
    obtain ⟨k0, hk0, hl0⟩ := hlab (n + 6)
    obtain ⟨k1, hk1, hl1⟩ := hlab n
    rw [hper n] at hk0 hl0
    have : k0 = k1 := (D.tile (s n).1).indep.injective (hk0.trans hk1.symm)
    rw [← hl0, ← hl1, this]
  have hu6 : ∀ n, F.p (s (n + 6)) = F.p (s n) := fun n => by rw [hper n]
  have eℓ : ∀ n, ℓ n = ℓ (n % 6) := per_reduce ℓ hl6
  have eu : ∀ n, F.p (s n) = F.p (s (n % 6)) := per_reduce (fun n => F.p (s n)) hu6
  -- rays at Y
  have hqa : Par (F.q (s a)) (neg2 d) := by rw [hsa]; exact rg_step_end F hSi hmi
  have hpb : Par (F.p (s b)) (neg2 d) := by rw [hsb]; exact rg_step_start F hSj hmj
  have hpa' : Par (F.p (s a')) d' := by rw [hsa']; exact rg_step_start F hSi2 hmi2
  have hqb' : Par (F.q (s b')) d' := by
    have := rg_step_end F hSj2 hmj2
    rw [hsb'] at *
    have e : ((-(neg2 d').1, -(neg2 d').2) : V2) = d' := neg2_neg2 d'
    rw [e] at this
    exact this
  have hua : Par (F.p (s (a + 1))) (neg2 d) := (hF.hpar a).trans hqa
  have hmod1 : (a + 1) % 6 = b % 6 := fan_par_mod G hF hu6 (hua.trans hpb.symm)
  have hub : Par (F.p (s (b' + 1))) d' := (hF.hpar b').trans hqb'
  have hmod2 : (b' + 1) % 6 = a' % 6 := fan_par_mod G hF hu6 (hub.trans hpa'.symm)
  have hℓa1 : ℓ (a + 1) = 1 := by rw [eℓ (a + 1), hmod1, ← eℓ]; exact hℓb
  have hℓb1 : ℓ (b' + 1) = 0 := by rw [eℓ (b' + 1), hmod2, ← eℓ]; exact hℓa'
  obtain ⟨t, ht, hrot⟩ := fan_turn hF hu6 hl6 hℓa hℓa1 hℓb' hℓb1
  refine ⟨t, ht, ?_⟩
  -- vectors
  have hW1 : Par (toV2 (Z - Y)) d' := by
    obtain ⟨-, -, -, -, -, -, -, -, hp, -⟩ := hSi2; exact hp
  have hW2 : Par (toV2 (Y - X)) d := by
    obtain ⟨-, -, -, -, -, -, -, -, hp, -⟩ := hSi; exact hp
  have hW2' : Par (toV2 (X - Y)) (neg2 d) := by
    have := par_neg hW2
    have e : toV2 (X - Y) = (-(toV2 (Y - X)).1, -(toV2 (Y - X)).2) := by unfold toV2; ext <;> simp
    rw [e]; exact this
  have hchain : Par (toV2 (Z - Y)) (Graph.rot (D.model.angleAt 1 + D.model.angleAt 0 + (t : ℝ) * D.model.angleAt 2) (toV2 (X - Y))) := by
    exact ((hW1.trans hub.symm).trans hrot).trans ((par_rot _ hua).trans (par_rot _ hW2'.symm))
  have hd1 : dist X Y = dist Y Z := by
    have e1 := hC.hidx i kk f
    have e2 := hC.hidx i' kk2 f2
    rw [hk, hf, hik, hif] at e1
    rw [hk2, hf2, hik2, hif2] at e2
    rw [e1, e2]
  have hnorm : nsq (toV2 (Z - Y)) = nsq (Graph.rot (D.model.angleAt 1 + D.model.angleAt 0 + (t : ℝ) * D.model.angleAt 2) (toV2 (X - Y))) := by
    rw [nsq_rot, nsq_toV2, nsq_toV2, dist_comm Z Y, hd1]
  exact eq_of_par_nsq hchain hnorm

end Erdos634.Draft.LaczFormal.RG

-- Draft/LaczFormalRG12CornerSeg.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2, the graph Gamma_except (S0c, piece (i)): a MAXIMAL SEGMENT STARTS AT A POLYGON CORNER.
-- At a vertex `V = v_{k+1}` of the convex polygon `A` where at least TWO tiles meet, the tiles at `V` form a chain (`corner_chain`); the ray between the first two tiles is the start of a maximal segment
-- (`noBack_corner`): both divisions `L1` (left, tiles starting along `d`) and `L2` (right, tiles ending along `d`) are nonempty and end together at `Y` (`exists_maxseg`).  Tiles lie on BOTH sides of the segment,
-- so it is inside `A` (apart from `V`) -- this is the segment `XZ` of the definition of Gamma_except with `X` a vertex of `A`.  No run clause (that is Gamma_a / Gamma_exc, a further step).
-- Hypotheses: `HasFansC`, `D.region = P.carrier`, two distinct tiles contain `V`.  NOTE, UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Sect. 4, 6.2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG5GammaC

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- `d` is the direction of a maximal segment `X..Y` of the tiling starting at `X`: nothing covers `X` from behind, both divisions are nonempty, and both end maximally at `Y`. -/
def MaxSegAlong (D : RegionDissection N) (d : V2) (X : Plane) : Prop :=
  ∃ (Y : Plane) (L1 L2 : List (Fin N × Plane × Plane)),
    d ≠ 0 ∧ NoBack D d X ∧ WalkT D d X Y L1 ∧ WalkR D d X Y L2 ∧ L1 ≠ [] ∧ L2 ≠ [] ∧
    (∀ i U', ¬ TriStep (D.tile i) d Y U') ∧ (∀ i U', ¬ TriStep (D.tile i) (neg2 d) U' Y)

set_option maxHeartbeats 3200000 in
/-- **A maximal segment starts at a polygon corner with at least two tiles.**  `d` lies in the corner cone `inCone pT qT` (`pT`, `qT` parallel to the outgoing edge and the reversed incoming edge). -/
theorem corner_segment_exists (D : RegionDissection N) [HasFansC D] (P : ConvPoly M) (hreg : D.region = P.carrier) (k : Fin M)
    (hvert : ∃ j k', (D.tile j).pts k' = P.v (k + 1))
    (h2 : ∃ x y : AtV D (P.v (k + 1)), x ≠ y) :
    ∃ (pT qT d : V2), Par pT (toV2 (P.e (k + 1))) ∧ Par qT (toV2 (P.v k - P.v (k + 1))) ∧ 0 < crs pT qT ∧
      inCone pT qT d ∧ MaxSegAlong D d (P.v (k + 1)) := by
  classical
  obtain ⟨pT, qT, F, hpd, hqd, hcr, h1, h2', h3, h4, h5⟩ := fan_vertex_poly D P hreg k hvert
  obtain ⟨i0, k0, hk0⟩ := hvert
  have hmem0 : (P.v (k + 1)) ∈ (D.tile i0).carrier := hk0 ▸ subset_convexHull ℝ _ ⟨k0, rfl⟩
  have hAt : 0 < Fintype.card (AtV D (P.v (k + 1))) := Fintype.card_pos_iff.mpr ⟨⟨i0, hmem0⟩⟩
  have hn2 : 2 ≤ Fintype.card (AtV D (P.v (k + 1))) := by
    obtain ⟨x, y, hxy⟩ := h2
    exact Fintype.one_lt_card_iff.mpr ⟨x, y, hxy⟩
  obtain ⟨c, hc1, hcn, hadj, hsurjc, hinjc⟩ := corner_chain F hcr h1 h2' h3 h4 h5 hAt
  set n := Fintype.card (AtV D (P.v (k + 1))) with hn
  have hsumT := corner_tile_sum D F hcr h1 h2' h3 h4
  have hwlt := wd_lt_pi_of_crs_pos hcr
  have hwpos := wd_pos (Or.inl hcr : SecOK pT qT)
  have hnostr : ∀ x : AtV D (P.v (k + 1)), ∃ kb, (D.tile x.1).pts kb = (P.v (k + 1)) := by
    intro x
    rcases F.hspec x with ⟨kb, hk, -⟩ | ⟨hnv, m', -, -, hq, -⟩
    · exact ⟨kb, hk⟩
    · exfalso
      have hw : wd (F.p x) (F.q x) = Real.pi := by rw [hq]; exact wd_straight (F.hok x).ne_p
      have hle : wd (F.p x) (F.q x) ≤ ∑ y : AtV D (P.v (k + 1)), wd (F.p y) (F.q y) :=
        Finset.single_le_sum (f := fun y => wd (F.p y) (F.q y)) (fun y _ => (wd_pos (F.hok y)).le) (Finset.mem_univ x)
      linarith
  have hcrall : ∀ x : AtV D (P.v (k + 1)), 0 < crs (F.p x) (F.q x) :=
    fun x => crs_pos_of_corner (F.hok x) (F.hspec x) (hnostr x)
  set x := c 1 with hx
  set y := c 2 with hy
  have hxy : Par (F.p y) (F.q x) := hadj 1 le_rfl (by omega)
  have hd : F.q x ≠ 0 := (F.hok x).ne_q
  have hnb : NoBack D (F.q x) (P.v (k + 1)) := noBack_corner F hcr h5 (tile_ray_mem F x).2 hd
  have hcx := hcrall x
  have hcy := hcrall y
  obtain ⟨kx, flx, hkx, hpx, hqx⟩ := spec_corner_data (F.hspec x) (hnostr x)
  obtain ⟨ky, fly, hky, hpy, hqy⟩ := spec_corner_data (F.hspec y) (hnostr y)
  have hstepR := triStep_of_end (T := D.tile x.1) (d := F.q x) kx flx hkx hpx hqx hcx (par_refl hd)
  have hstepL := triStep_of_start (T := D.tile y.1) (d := F.q x) ky fly hky hpy hqy hcy hxy
  have hX : ∃ j kb, (D.tile j).pts kb = (P.v (k + 1)) := ⟨y.1, ky, hky⟩
  obtain ⟨Y, L1, L2, W1, W2, hL1, hL2, hno1, hno2⟩ :=
    exists_maxseg D hd hX ⟨y.1, _, hstepL⟩ ⟨x.1, _, hstepR⟩
  have hcone : inCone pT qT (F.q x) := by
    have h := (tile_ray_mem F x).2
    rw [h5] at h
    exact h
  exact ⟨pT, qT, F.q x, hpd, hqd, hcr, hcone,
    Y, L1, L2, hd, hnb, W1, W2, hL1, hL2, hno1, hno2⟩

end Erdos634.Draft.LaczFormal.RG

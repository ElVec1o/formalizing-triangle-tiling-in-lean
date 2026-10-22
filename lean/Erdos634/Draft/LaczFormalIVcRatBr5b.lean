-- Draft/LaczFormalIVcRatBr5b.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, rational branch): BRIDGE item (1), stage Br5b.
--   `walk_cover` (every point of [X, Y) lies in the half-open segment of a walk entry) and
--   `hint_of_no_c_walk`: if NO tile edge of the side walks (a `WalkT` along every side of the polygon, as given by `edge_data`/`sides_edge_dichotomy`) has length c,
--   then every tile left step `U -> V` of length c has an open-segment point interior to the region.  This is exactly the hypothesis `hint` of `BrHyp`
--   in the first branch of the dichotomy `sides_edge_dichotomy` (B1).  Proof: a boundary c-edge lies on a side line (`edge_param`), is positively parallel to it
--   (the tile is on the left, the polygon on the left), lies in the half-open range of a walk entry (`walk_cover`), and the two tiles coincide (`overlap_eq`,
--   `tri_edges_par_eq`), so the edge is a walk entry of length c.  No fans (only `interiors_disjoint`).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 4, 8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcRatBr5a
import Erdos634.Draft.LaczFormalRG12GKiteEx

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

theorem toV2_eq_iff (A B : Plane) (s t : ℝ) : toV2 (A - B) = (s, t) ↔ A 0 - B 0 = s ∧ A 1 - B 1 = t := by
  rw [toV2_sub]; simp [Prod.ext_iff]

theorem walk_cover {D : RegionDissection N} {d : V2} (hd : d ≠ 0) {X Y : Plane} {L : List (Fin N × Plane × Plane)} (W : WalkT D d X Y L)
    {Z : Plane} {T u : ℝ} (hT : toV2 (Y - X) = (T * d.1, T * d.2)) (hu : toV2 (Z - X) = (u * d.1, u * d.2)) (hu0 : 0 ≤ u) (huT : u < T) :
    ∃ e ∈ L, ∃ c1 r : ℝ, 0 < c1 ∧ 0 ≤ r ∧ r < c1 ∧ toV2 (e.2.2 - e.2.1) = (c1 * d.1, c1 * d.2) ∧ toV2 (Z - e.2.1) = (r * d.1, r * d.2) := by
  induction W generalizing Z T u with
  | nil X =>
    exfalso
    rw [toV2_eq_iff] at hT
    obtain ⟨h1, h2⟩ := hT
    have hT0 : T = 0 := by
      by_contra hne
      apply hd
      have e1 : d.1 = 0 := by
        have : T * d.1 = 0 := by linarith
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h hne
        · exact h
      have e2 : d.2 = 0 := by
        have : T * d.2 = 0 := by linarith
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h hne
        · exact h
      exact Prod.ext e1 e2
    linarith
  | @cons i X X' Y L hS W' ih =>
    obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := id hS
    obtain ⟨c, hc, hcw⟩ := hpar.smul
    by_cases huc : u < c
    · refine ⟨(i, X, X'), List.mem_cons_self, c, u, hc, hu0, huc, hcw, hu⟩
    · push_neg at huc
      rw [toV2_eq_iff] at hT hu hcw
      have hT' : toV2 (Y - X') = ((T - c) * d.1, (T - c) * d.2) := by
        rw [toV2_eq_iff]; simp only [PiLp.sub_apply] at *; constructor <;> linarith [hT.1, hT.2, hcw.1, hcw.2]
      have hu' : toV2 (Z - X') = ((u - c) * d.1, (u - c) * d.2) := by
        rw [toV2_eq_iff]; simp only [PiLp.sub_apply] at *; constructor <;> linarith [hu.1, hu.2, hcw.1, hcw.2]
      obtain ⟨e, he, hrest⟩ := ih hT' hu' (by linarith) (by linarith)
      exact ⟨e, List.mem_cons_of_mem _ he, hrest⟩

theorem hint_of_no_c_walk [NeZero M] (D : CongruentRegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier)
    (L : Fin M → List (Fin N × Plane × Plane))
    (hW : ∀ k, WalkT D.toRegionDissection (toV2 (P.e k)) (P.v k) (P.v (k + 1)) (L k))
    (hno : ∀ k, ∀ e ∈ L k, dist e.2.1 e.2.2 ≠ slen D 2) :
    ∀ (i : Fin N) (d : V2) (U V : Plane), TriStep (D.tile i) d U V → dist U V = slen D 2 →
      ∃ m ∈ openSegment ℝ U V, m ∈ interior D.region := by
  intro i d U V hS hc
  by_contra hnone
  push_neg at hnone
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, hleft⟩ := id hS
  have hsub : ∀ x ∈ (D.tile i).carrier, x ∈ P.carrier := fun x hx => hreg ▸ tile_sub_region D.toRegionDissection i hx
  have hUc : U ∈ P.carrier := hsub U (hk ▸ tile_pt_mem _ kk)
  have hVc : V ∈ P.carrier := hsub V (hf ▸ tile_pt_mem _ f)
  have hgc : (D.tile i).pts g ∈ P.carrier := hsub _ (tile_pt_mem _ g)
  set m : Plane := (1 - 1 / 2 : ℝ) • U + (1 / 2 : ℝ) • V with hmdef
  have hm : m ∈ openSegment ℝ U V := ⟨1 - 1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  have hmc : ∀ j, P.c j m = (1 - 1 / 2) * P.c j U + (1 / 2) * P.c j V := fun j => P.c_comb j U V (1 / 2)
  by_cases hpos : ∀ j, 0 < P.c j m
  · exact hnone m hm (by rw [hreg]; exact P.interior_of_pos hpos)
  push_neg at hpos
  obtain ⟨k, hk0⟩ := hpos
  have hU0 : 0 ≤ P.c k U := (P.mem_carrier_iff U).1 hUc k
  have hV0 : 0 ≤ P.c k V := (P.mem_carrier_iff V).1 hVc k
  have hm0 := hmc k
  have cU : P.c k U = 0 := by linarith
  have cV : P.c k V = 0 := by linarith
  obtain ⟨t, ht, hUt⟩ := P.edge_param P.three_le hUc cU
  obtain ⟨t', ht', hVt⟩ := P.edge_param P.three_le hVc cV
  -- coordinates
  have hE0 : P.e k 0 = P.v (k + 1) 0 - P.v k 0 := by simp [ConvPoly.e]
  have hE1 : P.e k 1 = P.v (k + 1) 1 - P.v k 1 := by simp [ConvPoly.e]
  have hu0 : U 0 = P.v k 0 + t * P.e k 0 := by rw [hUt, hE0]; simp; ring
  have hu1 : U 1 = P.v k 1 + t * P.e k 1 := by rw [hUt, hE1]; simp; ring
  have hv0 : V 0 = P.v k 0 + t' * P.e k 0 := by rw [hVt, hE0]; simp; ring
  have hv1 : V 1 = P.v k 1 + t' * P.e k 1 := by rw [hVt, hE1]; simp; ring
  obtain ⟨c0, hc0, hcv⟩ := hpar.smul
  rw [toV2_eq_iff] at hcv
  obtain ⟨L1, L2⟩ := hcv
  -- (t'-t) e = c0 d
  have M1 : (t' - t) * P.e k 0 = c0 * d.1 := by rw [← L1, hu0, hv0]; ring
  have M2 : (t' - t) * P.e k 1 = c0 * d.2 := by rw [← L2, hu1, hv1]; ring
  -- orientation
  unfold crs at hleft
  rw [toV2_sub] at hleft
  simp only at hleft
  have hX : 0 ≤ P.c k ((D.tile i).pts g) := (P.mem_carrier_iff _).1 hgc k
  have hXe : P.c k ((D.tile i).pts g) = P.e k 0 * ((D.tile i).pts g 1 - U 1) - P.e k 1 * ((D.tile i).pts g 0 - U 0) := by
    unfold ConvPoly.c cross2
    simp only [PiLp.sub_apply]
    rw [hu0, hu1]; ring
  have hlam : 0 < t' - t := by
    by_contra hle
    push_neg at hle
    have h1 : (t' - t) * (P.e k 0 * ((D.tile i).pts g 1 - U 1) - P.e k 1 * ((D.tile i).pts g 0 - U 0)) =
        c0 * (d.1 * ((D.tile i).pts g 1 - U 1) - d.2 * ((D.tile i).pts g 0 - U 0)) := by
      linear_combination ((D.tile i).pts g 1 - U 1) * M1 - ((D.tile i).pts g 0 - U 0) * M2
    have h2 : 0 < c0 * (d.1 * ((D.tile i).pts g 1 - U 1) - d.2 * ((D.tile i).pts g 0 - U 0)) := mul_pos hc0 hleft
    rw [← h1] at h2
    rw [hXe] at hX
    nlinarith [mul_nonneg (neg_nonneg.2 hle) hX]
  have hdk0 : toV2 (P.e k) ≠ 0 := toV2_ne_zero (P.e_ne_zero P.three_le k)
  have hn : 0 < (P.e k 0) ^ 2 + (P.e k 1) ^ 2 := nsq_pos hdk0
  -- Par dk d
  have hPar : Par (toV2 (P.e k)) d := by
    refine ⟨?_, ?_⟩
    · show P.e k 0 * d.2 - P.e k 1 * d.1 = 0
      have : c0 * (P.e k 0 * d.2 - P.e k 1 * d.1) = 0 := by
        linear_combination (P.e k 0) * (-M2) + (P.e k 1) * M1
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hc0.ne'
      · exact h
    · show 0 < P.e k 0 * d.1 + P.e k 1 * d.2
      have h1 : c0 * (P.e k 0 * d.1 + P.e k 1 * d.2) = (t' - t) * ((P.e k 0) ^ 2 + (P.e k 1) ^ 2) := by
        linear_combination (-(P.e k 0)) * M1 - (P.e k 1) * M2
      have h2 : 0 < (t' - t) * ((P.e k 0) ^ 2 + (P.e k 1) ^ 2) := mul_pos hlam hn
      rw [← h1] at h2
      exact pos_of_mul_pos_right h2 hc0.le
  have hSk : TriStep (D.tile i) (toV2 (P.e k)) U V := TriStep.of_par hPar hS
  have ht1 : t < 1 := by linarith [ht'.2]
  have hT : toV2 (P.v (k + 1) - P.v k) = (1 * (toV2 (P.e k)).1, 1 * (toV2 (P.e k)).2) := by
    rw [toV2_eq_iff]
    constructor <;> simp [ConvPoly.e, toV2]
  have hu : toV2 (U - P.v k) = (t * (toV2 (P.e k)).1, t * (toV2 (P.e k)).2) := by
    rw [toV2_eq_iff]
    exact ⟨by rw [hu0]; show P.v k 0 + t * P.e k 0 - P.v k 0 = t * P.e k 0; ring, by rw [hu1]; show P.v k 1 + t * P.e k 1 - P.v k 1 = t * P.e k 1; ring⟩
  obtain ⟨⟨j, A, B⟩, he, c1, r, hc1, hr0, hr1, hAB, hAU⟩ := walk_cover hdk0 (hW k) hT hu ht.1 ht1
  have hUV : toV2 (V - U) = ((t' - t) * (toV2 (P.e k)).1, (t' - t) * (toV2 (P.e k)).2) := by
    rw [toV2_eq_iff]
    exact ⟨by rw [hu0, hv0]; show _ = (t' - t) * P.e k 0; ring, by rw [hu1, hv1]; show _ = (t' - t) * P.e k 1; ring⟩
  have hj : TriStep (D.tile j) (toV2 (P.e k)) A B := walkT_mem_step (hW k) _ he
  simp only at hAB hAU
  have hij : i = j := overlap_eq D.toRegionDissection hSk hj hc1 hlam hr0 hr1 hAB hUV hAU
  subst hij
  obtain ⟨hUA, hVB⟩ := tri_edges_par_eq _ hSk hj
  have := hno k _ he
  simp only at this
  rw [← hUA, ← hVB] at this
  exact this hc

end Erdos634.Draft.LaczFormal.RG

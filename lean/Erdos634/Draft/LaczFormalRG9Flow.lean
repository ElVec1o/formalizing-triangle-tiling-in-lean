-- Draft/LaczFormalRG9Flow.lean -- the flow of `Gamma_a` with deficits (Laczkovich DCG 48 (2012), Sect. 5.1, the cases `R = N-1`, `R = N`): a head of an edge starts an edge unless the parity condition fails at it
-- (`ga_head_out_loc`, the local form of `ga_head_out_half`); the heads without outgoing edge (`gaDf`) are interior exceptional vertices; the boundary vertices with an outgoing edge (`gaZ`) are at most as many
-- as the heads without outgoing edge (`ga_Z_le_Df`: `sum (out - in) = 0`, `in <= 1`, `in = 0` on the boundary).  UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Sect. 4, 5.1), Beeson, Beeson-Zhang (the weight/flow technique of `bz_count_poly`).
import Erdos634.Draft.LaczFormalRG9Sides
import Erdos634.Draft.LaczFormalRG9SideA

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- **Local form of `ga_head_out_half`**: the parity condition is needed only at the head `H`. -/
theorem ga_head_out_loc (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2)
    {X H : Plane} (hE : GaEdge D.toRegionDissection (slen D 0) X H)
    (hpar : ∑ l, (cnt D idx H l : ℝ) * D.model.angleAt l = Real.pi → (cnt D idx H 1 + cnt D idx H 2) % 2 = 0) :
    ∃ H', GaEdge D.toRegionDissection (slen D 0) H H' := by
  classical
  obtain ⟨κ, _, ⟨F⟩⟩ := HasFansC.fans (D := D.toRegionDissection) H (ga_edge_vertex _ _ hE)
  obtain ⟨d, hd, nb, hc⟩ := ga_edge_data D idx hidx hnc hE F
  have key : ∀ {e : V2} {u v s : AtV D.toRegionDissection H}, HeadCfg D F e u v s → ∃ H', GaEdge D.toRegionDissection (slen D 0) H H' := by
    intro e u v s hc
    have hc' := hc
    obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩ := hc'
    have hcyc := F.head_cyc u v s hc1 hc2 hc3 hc4 hc5 hc6
    obtain ⟨hS1, hsum, hcard⟩ := head_counts D idx hidxA F hcyc.1 hc6 hc1
    exact head_cfg_edge D idx hidx hnc hab hac F hc (hpar hsum)
  rcases hc with ⟨P, W, hP, a, b, s, h1, h2, h3, h4, h5, h6, h7, h8⟩ | ⟨P, W, hP, a, b, s, h1, h2, h3, h4, h5, h6, h7, h8⟩
  · exact key (HeadCfg.of_left D F a b s h1 h2 h3 h4 h5 h6 h7 h8)
  · exact key (HeadCfg.of_right D F a b s h1 h2 h3 h4 h5 h6 h7 h8)

/-- Boundary vertices of the tiling with an outgoing `Γ_a` edge. -/
noncomputable def gaZ (D : CongruentRegionDissection N) : Finset Plane :=
  (vtxSet D.toRegionDissection).filter (fun v => v ∉ interior D.region ∧ ∃ H, GaEdge D.toRegionDissection (slen D 0) v H)

/-- Heads of `Γ_a` edges without outgoing edge (deficit vertices). -/
noncomputable def gaDf (D : CongruentRegionDissection N) : Finset Plane :=
  (vtxSet D.toRegionDissection).filter (fun v => (∃ X, GaEdge D.toRegionDissection (slen D 0) X v) ∧ ¬ ∃ H, GaEdge D.toRegionDissection (slen D 0) v H)

/-- **The flow inequality**: at most as many boundary vertices start an edge of `Γ_a` as there are heads without outgoing edge. -/
theorem ga_Z_le_Df (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseA D idx) :
    (gaZ D).card ≤ (gaDf D).card := by
  classical
  set V := vtxSet D.toRegionDissection with hVdef
  set E : Finset (Plane × Plane) := (V ×ˢ V).filter (fun e => GaEdge D.toRegionDissection (slen D 0) e.1 e.2) with hE
  let out : Plane → ℕ := fun v => (E.filter (fun e => e.1 = v)).card
  let inn : Plane → ℕ := fun v => (E.filter (fun e => e.2 = v)).card
  have hEmem : ∀ e : Plane × Plane, e ∈ E ↔ GaEdge D.toRegionDissection (slen D 0) e.1 e.2 := by
    intro e
    simp only [hE, Finset.mem_filter, Finset.mem_product]
    constructor
    · exact fun h => h.2
    · intro h'
      have := ga_edge_endpoints D.toRegionDissection (slen D 0) h'
      exact ⟨⟨mem_vtxSet.mpr this.1, mem_vtxSet.mpr this.2⟩, h'⟩
  have hin1 : ∀ v, inn v ≤ 1 := by
    intro v
    simp only [inn]
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    have h1 := (hEmem a).mp ha.1
    have h2 := (hEmem b).mp hb.1
    rw [ha.2] at h1
    rw [hb.2] at h2
    have := ga_indegree D idx h.hidx h.hnc h1 h2
    exact Prod.ext this (ha.2.trans hb.2.symm)
  have hbal : ∑ v ∈ V, (out v : ℤ) = ∑ v ∈ V, (inn v : ℤ) := by
    have h1 := Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (s := E) (t := V)
      (fun e he => ((Finset.mem_product.mp (Finset.mem_filter.mp he).1).1))
    have h2 := Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (s := E) (t := V)
      (fun e he => ((Finset.mem_product.mp (Finset.mem_filter.mp he).1).2))
    have : ∑ v ∈ V, out v = ∑ v ∈ V, inn v := by
      simp only [out, inn]; rw [← h1, ← h2]
    exact_mod_cast this
  have hout_iff : ∀ v, 1 ≤ out v ↔ ∃ H, GaEdge D.toRegionDissection (slen D 0) v H := by
    intro v
    constructor
    · intro h1
      obtain ⟨e, he⟩ := Finset.card_pos.mp (by simpa [out] using h1 : 0 < (E.filter (fun e => e.1 = v)).card)
      simp only [Finset.mem_filter] at he
      have := (hEmem e).mp he.1
      rw [he.2] at this
      exact ⟨e.2, this⟩
    · rintro ⟨H', hH'⟩
      have hv := ga_edge_endpoints D.toRegionDissection (slen D 0) hH'
      apply Finset.card_pos.mpr
      refine ⟨(v, H'), ?_⟩
      simp only [Finset.mem_filter]
      exact ⟨(hEmem (v, H')).mpr hH', trivial⟩
  have hin_iff : ∀ v, 1 ≤ inn v ↔ ∃ X, GaEdge D.toRegionDissection (slen D 0) X v := by
    intro v
    constructor
    · intro h1
      obtain ⟨e, he⟩ := Finset.card_pos.mp (by simpa [inn] using h1 : 0 < (E.filter (fun e => e.2 = v)).card)
      simp only [Finset.mem_filter] at he
      have := (hEmem e).mp he.1
      rw [he.2] at this
      exact ⟨e.1, this⟩
    · rintro ⟨X, hX⟩
      apply Finset.card_pos.mpr
      refine ⟨(X, v), ?_⟩
      simp only [Finset.mem_filter]
      exact ⟨(hEmem (X, v)).mpr hX, trivial⟩
  -- no edge arrives at a boundary point
  have hbdy : ∀ v, v ∉ interior D.region → inn v = 0 := by
    intro v hv
    by_contra hne
    have : 1 ≤ inn v := by omega
    obtain ⟨X, hX⟩ := (hin_iff v).mp this
    exact hv (ga_head_interior D idx h.hidx h.hnc hX)
  -- the signed degree
  have hf_nonneg : ∀ v ∈ V, v ∉ gaDf D → 0 ≤ (out v : ℤ) - inn v := by
    intro v hv hnDf
    have hi := hin1 v
    by_cases hi0 : inn v = 0
    · omega
    · have hi1 : 1 ≤ inn v := by omega
      have hex := (hin_iff v).mp hi1
      have : ∃ H, GaEdge D.toRegionDissection (slen D 0) v H := by
        by_contra hno
        apply hnDf
        simp only [gaDf, Finset.mem_filter]
        exact ⟨hv, hex, hno⟩
      have := (hout_iff v).mpr this
      omega
  have hZ_ge : ∀ v ∈ gaZ D, 1 ≤ (out v : ℤ) - inn v := by
    intro v hv
    simp only [gaZ, Finset.mem_filter] at hv
    have := (hout_iff v).mpr hv.2.2
    have := hbdy v hv.2.1
    omega
  have hDf_eq : ∀ v ∈ gaDf D, (out v : ℤ) - inn v = -1 := by
    intro v hv
    simp only [gaDf, Finset.mem_filter] at hv
    have h1 := (hin_iff v).mpr hv.2.1
    have h0 : out v = 0 := by
      by_contra hne
      have : 1 ≤ out v := by omega
      exact hv.2.2 ((hout_iff v).mp this)
    have := hin1 v
    omega
  have hDfV : gaDf D ⊆ V := Finset.filter_subset _ _
  have hZV : gaZ D ⊆ V := Finset.filter_subset _ _
  have hZdisj : Disjoint (gaZ D) (gaDf D) := by
    rw [Finset.disjoint_left]
    intro v hvZ hvD
    have := hDf_eq v hvD
    have := hZ_ge v hvZ
    omega
  have hsum0 : ∑ v ∈ V, ((out v : ℤ) - inn v) = 0 := by
    rw [Finset.sum_sub_distrib, hbal]; ring
  -- split `V` into `Df` and the rest
  have hsplit := Finset.sum_sdiff (f := fun v => ((out v : ℤ) - inn v)) hDfV
  have hDsum : ∑ v ∈ gaDf D, ((out v : ℤ) - inn v) = -((gaDf D).card : ℤ) := by
    rw [Finset.sum_congr rfl hDf_eq]; simp
  have hrest : ∑ v ∈ gaZ D, ((out v : ℤ) - inn v) ≤ ∑ v ∈ V \ gaDf D, ((out v : ℤ) - inn v) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro v hv
      rw [Finset.mem_sdiff]
      exact ⟨hZV hv, fun hD => Finset.disjoint_left.mp hZdisj hv hD⟩
    · intro v hv hvZ
      rw [Finset.mem_sdiff] at hv
      exact hf_nonneg v hv.1 hv.2
  have hZsum : ((gaZ D).card : ℤ) ≤ ∑ v ∈ gaZ D, ((out v : ℤ) - inn v) := by
    calc ((gaZ D).card : ℤ) = ∑ _v ∈ gaZ D, (1 : ℤ) := by simp
      _ ≤ _ := Finset.sum_le_sum hZ_ge
  have hs2 : ∑ v ∈ V \ gaDf D, ((out v : ℤ) - inn v) + ∑ v ∈ gaDf D, ((out v : ℤ) - inn v) = 0 := by
    rw [← hsum0]; exact hsplit
  omega

end Erdos634.Draft.LaczFormal.RG

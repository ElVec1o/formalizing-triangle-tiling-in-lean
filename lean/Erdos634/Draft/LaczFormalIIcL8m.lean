-- Draft/LaczFormalIIcL8m.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, L8 `gexc_disjoint`, step 6: a vertex with TWO lines of tile sides through it, each flanked on the back ray by two `gamma` corner sectors, is exceptional.
--  `exc_of_two_lines`: four `gamma` sectors at `V`, `aL1, aR1` flanking the ray `-d1` and `aL2, aR2` flanking `-d2` (`d1, d2` not parallel): then `cnt alpha < cnt gamma` at `V`.
--  Either at least three of the four sectors are distinct (`cnt gamma >= 3`, hence `cnt alpha < cnt gamma` by the angle sum, `v <= 2`, `gamma < pi/2`), or `aL1 = aR2` and `aR1 = aL2`: then `{aL1, aR1}` is closed under predecessor
--  (`fan_closed`), every sector is `gamma`, `cnt alpha = 0 < cnt gamma`.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12GExcCapMain
import Erdos634.Draft.LaczFormalIIcSharp3

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

/-- the number of `gamma` sectors is at most `cnt gamma`. -/
theorem gamma_card_le_cnt (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {E : Plane} (Γ : Finset (AtV D.toRegionDissection E))
    (hΓ : ∀ a ∈ Γ, IsGam D idx a) : Γ.card ≤ cnt D idx E 2 := by
  classical
  unfold cnt
  apply Finset.card_le_card_of_injOn (fun a : AtV D.toRegionDissection E => (a.1, if h : ∃ k, (D.tile a.1).pts k = E ∧ idx a.1 k = 2 then h.choose else 0))
  · intro a ha
    have hg : ∃ k, (D.tile a.1).pts k = E ∧ idx a.1 k = 2 := hΓ a (Finset.mem_coe.mp ha)
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, dif_pos hg]
    exact hg.choose_spec
  · intro a _ a' _ h
    exact Subtype.ext (congrArg Prod.fst h)

/-- angle relation at a vertex of the tiling that is not a vertex of the polygon: `(r - p) gamma = (v - p) pi` with `v <= 2`. -/
theorem vertex_angle_rel [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1)
    {X : Plane} (hvert : ∃ j k, (D.tile j).pts k = X) (hnc : ∀ k : Fin M, X ≠ P.v (k + 1)) :
    ∃ v : ℕ, v ≤ 2 ∧ ((cnt D idx X 2 : ℝ) - cnt D idx X 0) * D.model.angleAt 2 = ((v : ℝ) - cnt D idx X 0) * Real.pi := by
  have hv : ∃ v : ℕ, (v = 1 ∨ (v = 2 ∧ X ∈ interior D.region)) ∧ Asum D idx X = v * Real.pi := by
    rcases vertex_A D P hreg idx hidxA hvert with ⟨hi, h2 | h1'⟩ | ⟨hni, h1' | ⟨k, hXk, -⟩⟩
    · exact ⟨2, Or.inr ⟨rfl, hi⟩, by rw [h2]; push_cast; ring⟩
    · exact ⟨1, Or.inl rfl, by rw [h1']; push_cast; ring⟩
    · exact ⟨1, Or.inl rfl, by rw [h1']; push_cast; ring⟩
    · exact absurd hXk (hnc k)
  obtain ⟨v, hv12, hAv⟩ := hv
  rw [Asum_eq D idx hregc] at hAv
  refine ⟨v, by rcases hv12 with h | ⟨h, -⟩ <;> omega, by linarith⟩

/-- Two lines of tile sides through `V` with `gamma` flanks on their back rays: `V` is exceptional. -/
theorem exc_of_two_lines [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (h1 : D.model.angleAt 2 < Real.pi / 2)
    {V : Plane} (hvert : ∃ j k, (D.tile j).pts k = V) (hnc : ∀ k : Fin M, V ≠ P.v (k + 1)) {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection V κ)
    {d1 d2 : V2} (hnp : crs d1 d2 ≠ 0) {aL1 aR1 aL2 aR2 : AtV D.toRegionDissection V}
    (q1 : Par (F.q aL1) (neg2 d1)) (p1 : Par (F.p aR1) (neg2 d1)) (g1L : IsGam D idx aL1) (g1R : IsGam D idx aR1)
    (q2 : Par (F.q aL2) (neg2 d2)) (p2 : Par (F.p aR2) (neg2 d2)) (g2L : IsGam D idx aL2) (g2R : IsGam D idx aR2) :
    cnt D idx V 0 < cnt D idx V 2 := by
  classical
  have hpi := Real.pi_pos
  have hγ0 := model_angle_pos' D 2
  -- the rays -d1, -d2 are not parallel
  have hn12 : ¬ Par (neg2 d1) (neg2 d2) := by
    intro h; apply hnp; have := h.1; unfold crs neg2 at this; unfold crs; simp only at this; linarith
  have hn21 : ¬ Par (neg2 d2) (neg2 d1) := fun h => hn12 h.symm
  have e13 : aL1 ≠ aL2 := fun h => hn12 (by subst h; exact q1.symm.trans q2)
  have e24 : aR1 ≠ aR2 := fun h => hn12 (by subst h; exact p1.symm.trans p2)
  have e12 : aL1 ≠ aR1 := by
    intro h; subst h
    have hp : Par (F.p aL1) (F.q aL1) := p1.trans q1.symm
    have := F.hok aL1
    rcases this with h | ⟨h, h'⟩
    · exact absurd hp.1 h.ne'
    · exact absurd hp.2 (by linarith)
  have e34 : aL2 ≠ aR2 := by
    intro h; subst h
    have hp : Par (F.p aL2) (F.q aL2) := p2.trans q2.symm
    have := F.hok aL2
    rcases this with h | ⟨h, h'⟩
    · exact absurd hp.1 h.ne'
    · exact absurd hp.2 (by linarith)
  by_cases hA : aL1 = aR2 ∧ aR1 = aL2
  · -- closure case
    obtain ⟨hA1, hA2⟩ := hA
    set Γ0 : Set (AtV D.toRegionDissection V) := {aL1, aR1} with hΓ0
    have hg0 : aL1 ∈ Γ0 := by simp [hΓ0]
    have hcl : ∀ g ∈ Γ0, ∃ a ∈ Γ0, Par (F.q a) (F.p g) := by
      intro g hg
      rcases hg with rfl | hg
      · refine ⟨aR1, by simp [hΓ0], ?_⟩
        rw [hA2]; rw [hA1] at *; exact q2.trans p2.symm
      · rw [Set.mem_singleton_iff] at hg
        subst hg
        refine ⟨aL1, by simp [hΓ0], q1.trans p1.symm⟩
    have hall := fan_closed F Γ0 hg0 hcl
    have hγall : ∀ a : AtV D.toRegionDissection V, IsGam D idx a := by
      intro a
      obtain ⟨b, hb, hba⟩ := hall (Sum.inl a)
      have : b = a := (Sum.inl_injective hba).symm
      subst this
      rcases hb with rfl | hb
      · exact g1L
      · rw [Set.mem_singleton_iff] at hb; subst hb; exact g1R
    have h0 : cnt D idx V 0 = 0 := by
      by_contra hne
      have hpos : 0 < cnt D idx V 0 := Nat.pos_of_ne_zero hne
      unfold cnt at hpos
      obtain ⟨⟨i, k⟩, hik⟩ := Finset.card_pos.mp hpos
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hik
      obtain ⟨hik1, hik2⟩ := hik
      have hmem : V ∈ (D.tile i).carrier := hik1 ▸ tile_pt_mem _ k
      obtain ⟨k', hk'1, hk'2⟩ := hγall ⟨i, hmem⟩
      have : k' = k := (D.tile i).indep.injective (hk'1.trans hik1.symm)
      rw [this, hik2] at hk'2
      exact absurd hk'2 (by decide)
    have hc2 : 1 ≤ cnt D idx V 2 := by
      have := gamma_card_le_cnt D idx ({aL1} : Finset (AtV D.toRegionDissection V)) (by intro a ha; rw [Finset.mem_singleton.mp ha]; exact g1L)
      simpa using this
    omega
  · -- three distinct gamma sectors
    have h3 : ∃ x y z : AtV D.toRegionDissection V, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ IsGam D idx x ∧ IsGam D idx y ∧ IsGam D idx z := by
      by_cases hc : aL1 = aR2
      · have hc' : aR1 ≠ aL2 := fun h => hA ⟨hc, h⟩
        refine ⟨aL1, aR1, aL2, e12, e13, hc', g1L, g1R, g2L⟩
      · refine ⟨aL1, aR1, aR2, e12, hc, e24, g1L, g1R, g2R⟩
    obtain ⟨x, y, z, hxy, hxz, hyz, gx, gy, gz⟩ := h3
    have hcard : 3 ≤ cnt D idx V 2 := by
      have := gamma_card_le_cnt D idx ({x, y, z} : Finset (AtV D.toRegionDissection V)) (by
        intro a ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl | rfl <;> assumption)
      rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]), Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton] at this
      omega
    obtain ⟨v, hv2, hrel⟩ := vertex_angle_rel D P hreg idx hC.hidxA hC.hregc hvert hnc
    by_contra hge
    push Not at hge
    have hge' : (cnt D idx V 2 : ℝ) ≤ cnt D idx V 0 := by exact_mod_cast hge
    have h3' : (3 : ℝ) ≤ cnt D idx V 2 := by exact_mod_cast hcard
    have hv2' : (v : ℝ) ≤ 2 := by exact_mod_cast hv2
    nlinarith [mul_nonneg (sub_nonneg.mpr hge') hγ0.le, mul_pos hpi hγ0]

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.exc_of_two_lines

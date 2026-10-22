-- Draft/LaczFormalIVcRatBr3d.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, rational branch): BRIDGE stage Br3d (B-b): `vw_transfer`.
--   At a point X the corners of tiles with label /= 2 (labels c, d in {rho, pi}) are equinumerous (`CaseC.hregc`); the partner map (tile i -> its c-partner, corner -> the corner of the partner at X)
--   is an involution on them; same-label pairs of colour c and of colour d are therefore equinumerous (`involution_count`).  So a same-label c-pair at X gives a same-label d-pair at X.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3, Lemma 4.8, blueprint P2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcRatBr3c

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M] {D : CongruentRegionDissection N} {P : ConvPoly M} {idx : Fin N → Equiv.Perm (Fin 3)} {s : ℝ} {ρ π : Fin 3}

/-- Existence of the partner corner at the same point. -/
theorem partner_corner [HasFansC D.toRegionDissection] (h : BrHyp D P idx s ρ π) (i : Fin N) (a : Fin 3) (ha : idx i a ≠ 2) :
    ∃ j a', Pr D i j ∧ (D.tile j).pts a' = (D.tile i).pts a ∧ idx j a' ≠ 2 := by
  obtain ⟨j, -, hPr⟩ := Pr_exists h i
  obtain ⟨d, U, V, hS, hc, hS'⟩ := hPr
  rcases pair_tile_shape D idx h.hC.hidx h.hs h.hρπ h.hρ h.hπ h.hlρ h.hlπ h.hl2 hS hS' hc with ⟨K, -, -, -, -, -, hcl⟩ | ⟨-, hcl⟩
  · obtain ⟨a', ha', hl⟩ := hcl a ha
    exact ⟨j, a', ⟨d, U, V, hS, hc, hS'⟩, ha', by rw [hl]; exact ha⟩
  · obtain ⟨a', ha', -, hne⟩ := hcl a ha
    exact ⟨j, a', ⟨d, U, V, hS, hc, hS'⟩, ha', hne⟩

set_option maxHeartbeats 1600000 in
theorem vw_transfer [HasFansC D.toRegionDissection] (h : BrHyp D P idx s ρ π) {c d : Fin 3} (hcd : c ≠ d) (hc2 : c ≠ 2) (hd2 : d ≠ 2)
    {i j : Fin N} {a a' : Fin 3} {X : Plane} (hPr : Pr D i j) (ha : (D.tile i).pts a = X) (ha' : (D.tile j).pts a' = X)
    (hla : idx i a = c) (hla' : idx j a' = c) :
    ∃ i' j' b b', Pr D i' j' ∧ (D.tile i').pts b = X ∧ idx i' b = d ∧ (D.tile j').pts b' = X ∧ idx j' b' = d := by
  classical
  set S : Finset (Fin N × Fin 3) := Finset.univ.filter (fun q => (D.tile q.1).pts q.2 = X ∧ idx q.1 q.2 ≠ 2) with hS
  have memS : ∀ q, q ∈ S ↔ (D.tile q.1).pts q.2 = X ∧ idx q.1 q.2 ≠ 2 := by intro q; simp [hS]
  let Gr : Fin N × Fin 3 → Fin N × Fin 3 → Prop := fun q q' => Pr D q.1 q'.1 ∧ (D.tile q'.1).pts q'.2 = (D.tile q.1).pts q.2
  have hex : ∀ q ∈ S, ∃ q', q' ∈ S ∧ Gr q q' := by
    intro q hq
    obtain ⟨hqX, hq2⟩ := (memS q).1 hq
    obtain ⟨j0, a0, hPr0, hpt, h2⟩ := partner_corner h q.1 q.2 hq2
    exact ⟨(j0, a0), (memS _).2 ⟨hpt.trans hqX, h2⟩, hPr0, hpt⟩
  have huniq : ∀ q q' q'', Gr q q' → Gr q q'' → q' = q'' := by
    rintro q ⟨j1, a1⟩ ⟨j2, a2⟩ ⟨p1, e1⟩ ⟨p2, e2⟩
    have hj : j1 = j2 := Pr.unique D idx h.hC.hidx h.h0 h.h1 p1 p2
    subst hj
    have : a1 = a2 := (D.tile j1).indep.injective (e1.trans e2.symm)
    subst this; rfl
  have hsymm : ∀ q q', Gr q q' → Gr q' q := fun q q' ⟨p, e⟩ => ⟨p.symm, e.symm⟩
  let σ : Fin N × Fin 3 → Fin N × Fin 3 := fun q => if hq : ∃ q', q' ∈ S ∧ Gr q q' then Classical.choose hq else q
  have hσ : ∀ q ∈ S, σ q ∈ S ∧ Gr q (σ q) := by
    intro q hq
    have hq' := hex q hq
    simp only [σ, dif_pos hq']
    exact Classical.choose_spec hq'
  have hσS : ∀ q ∈ S, σ q ∈ S := fun q hq => (hσ q hq).1
  have hinv : ∀ q ∈ S, σ (σ q) = q := by
    intro q hq
    obtain ⟨h1, h2⟩ := hσ q hq
    obtain ⟨h3, h4⟩ := hσ (σ q) h1
    exact huniq (σ q) _ _ h4 (hsymm _ _ h2)
  have hσeq : ∀ q ∈ S, ∀ q', Gr q q' → σ q = q' := fun q hq q' hg => huniq q _ _ (hσ q hq).2 hg
  -- counting
  have cntc : (S.filter (fun q => idx q.1 q.2 = c)).card = cnt D idx X c := by
    unfold cnt; congr 1; ext q; simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by rw [h3]; exact hc2⟩, h3⟩
  have cntd : (S.filter (fun q => ¬ idx q.1 q.2 = c)).card = cnt D idx X d := by
    unfold cnt; congr 1; ext q; simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, fin3_other c d _ hcd hc2 hd2 h2 h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by rw [h3]; exact hd2⟩, by rw [h3]; exact hcd.symm⟩
  have hreg : cnt D idx X c = cnt D idx X d := by
    rcases fin3_cd c d hcd hc2 hd2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2]; exact h.hC.hregc X
    · rw [e1, e2]; exact (h.hC.hregc X).symm
  have hcard : (S.filter (fun q => idx q.1 q.2 = c)).card = (S.filter (fun q => ¬ idx q.1 q.2 = c)).card := by
    rw [cntc, cntd]; exact hreg
  have hmain : (S.filter (fun q => idx q.1 q.2 = c ∧ idx (σ q).1 (σ q).2 = c)).card =
      (S.filter (fun q => ¬ idx q.1 q.2 = c ∧ ¬ idx (σ q).1 (σ q).2 = c)).card := by
    convert involution_count S σ (fun q => idx q.1 q.2 = c) hσS hinv (by convert hcard)
  -- the given pair
  have hq0 : ((i, a) : Fin N × Fin 3) ∈ S := (memS _).2 ⟨ha, by simp only; rw [hla]; exact hc2⟩
  have hq1 : ((j, a') : Fin N × Fin 3) ∈ S := (memS _).2 ⟨ha', by simp only; rw [hla']; exact hc2⟩
  have hσ0 : σ (i, a) = (j, a') := hσeq _ hq0 _ ⟨hPr, ha'.trans ha.symm⟩
  have hA : 0 < (S.filter (fun q => idx q.1 q.2 = c ∧ idx (σ q).1 (σ q).2 = c)).card := by
    apply Finset.card_pos.2
    refine ⟨(i, a), ?_⟩
    rw [Finset.mem_filter]
    refine ⟨hq0, hla, ?_⟩
    rw [hσ0]; exact hla'
  rw [hmain] at hA
  obtain ⟨q, hq⟩ := Finset.card_pos.1 hA
  rw [Finset.mem_filter] at hq
  obtain ⟨hqS, hq1', hq2'⟩ := hq
  obtain ⟨hσS', hGr⟩ := hσ q hqS
  obtain ⟨-, hqne⟩ := (memS q).1 hqS
  obtain ⟨-, hσne⟩ := (memS (σ q)).1 hσS'
  exact ⟨q.1, (σ q).1, q.2, (σ q).2, hGr.1, ((memS q).1 hqS).1, fin3_other c d _ hcd hc2 hd2 hqne hq1',
    ((memS (σ q)).1 hσS').1, fin3_other c d _ hcd hc2 hd2 hσne hq2'⟩

#print axioms Erdos634.Draft.LaczFormal.RG.vw_transfer

end Erdos634.Draft.LaczFormal.RG

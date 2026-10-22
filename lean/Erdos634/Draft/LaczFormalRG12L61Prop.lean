-- Draft/LaczFormalRG12L61Prop.lean -- Laczkovich DCG 48 (2012), Lemma 6.1 (Subcase IIc), propagation of `gamma` around a polygon vertex.  Case C (`Gamma_c` empty / no edge of `Gamma_c` on the boundary), polygon
-- vertices `X, Y, Z` consecutive, the open sides `XY`, `YZ` with normal tiling vertices, `X` a corner carrying no `alpha, beta` (only `gamma`'s), `Y` a corner without `gamma`: then `Z` carries a `gamma`
-- (`gamma_prop_fwd`; `gamma_prop_bwd` is the same in the opposite direction).  Route: `walk_gamma_n` (tail `gamma` along `XY`), the c-status at the corner `Y` (`corner_c_status`, Lemma 4.7), head `gamma` along `YZ`
-- (`walk_head_fwd`).  NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), proof of Lemma 6.1, Fig. 4), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12L61Loc
import Erdos634.Draft.LaczFormalRG11Block

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

theorem c_ne_ab (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx) : slen D 2 ≠ slen D 1 ∧ slen D 2 ≠ slen D 0 := by
  have hG := h.caseG
  have h1 := hG.hab
  have h2 := hG.hac
  unfold relabelC at h1 h2
  rw [relabel_slen, relabel_slen, swap02_0, swap02_1] at h1
  rw [relabel_slen, relabel_slen, swap02_0, swap02_2] at h2
  exact ⟨h1, h2⟩

/-- A step between two corners of a tile, neither of type `γ`, has length `c`. -/
theorem step_dist_c (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    {j : Fin N} {p q : Fin 3} (hpq : p ≠ q) (hp : idx j p ≠ 2) (hq : idx j q ≠ 2) : dist ((D.tile j).pts p) ((D.tile j).pts q) = slen D 2 := by
  have hne : idx j p ≠ idx j q := fun e => hpq ((idx j).injective e)
  rw [hidx]
  unfold slen
  have : ∀ x y : Fin 3, x ≠ 2 → y ≠ 2 → x ≠ y → (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) := by decide
  rcases this _ _ hp hq hne with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1, e2]; rfl
  · rw [e1, e2, dist_comm]; rfl

/-- A step with a corner of type `γ` does not have length `c`. -/
theorem step_dist_ne_c (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx)
    {j : Fin N} {p q : Fin 3} (hpq : p ≠ q) (hg : idx j p = 2 ∨ idx j q = 2) : dist ((D.tile j).pts p) ((D.tile j).pts q) ≠ slen D 2 := by
  obtain ⟨hcb, hca⟩ := c_ne_ab D idx h
  have hne : idx j p ≠ idx j q := fun e => hpq ((idx j).injective e)
  rw [h.hidx]
  have key : ∀ x y : Fin 3, x ≠ y → (x = 2 ∨ y = 2) → (x = 2 ∧ y = 0) ∨ (x = 2 ∧ y = 1) ∨ (x = 0 ∧ y = 2) ∨ (x = 1 ∧ y = 2) := by decide
  rcases key _ _ hne hg with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1, e2]; intro hh; apply hcb.symm; rw [← hh]; unfold slen; rfl
  · rw [e1, e2]; intro hh; apply hca.symm; rw [← hh]; unfold slen; rw [dist_comm]; rfl
  · rw [e1, e2]; intro hh; apply hcb.symm; rw [← hh]; unfold slen; rw [dist_comm]; rfl
  · rw [e1, e2]; intro hh; apply hca.symm; rw [← hh]; unfold slen; rfl


/-- Whole-side rules (Case C, normal interior vertices): head `γ` forward, head `γ` backward, tail `γ` backward (tail `γ` forward is `walk_gamma_n`). -/
theorem walk_head_fwd (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx) (i : Fin M) (hnorm : NormSide D idx P i) {L : List (Fin N × Plane × Plane)}
    (W : WalkT D.toRegionDissection (toV2 (P.e i)) (P.v i) (P.v (i + 1)) L) {e0 el : Fin N × Plane × Plane}
    (hf : L.head? = some e0) (hl : L.getLast? = some el) :
    TyAt D idx e0.1 e0.2.2 2 → TyAt D idx el.1 el.2.2 2 := by
  classical
  have hU : ∃ s : ℝ, 0 ≤ s ∧ toV2 (P.v i - P.v i) = (s * (toV2 (P.e i)).1, s * (toV2 (P.e i)).2) :=
    ⟨0, le_rfl, by unfold toV2; ext <;> simp⟩
  obtain ⟨L0, hL0⟩ : ∃ L0, L = e0 :: L0 := by
    cases L with
    | nil => simp at hf
    | cons x L0 => simp at hf; exact ⟨L0, by rw [hf]⟩
  have hel_mem : el ∈ L := List.mem_of_getLast? hl
  intro hR
  refine walk_prop_forward D.toRegionDissection P hreg i (fun e => TyAt D idx e.1 e.2.2 2) ?_ rfl W hU e0 L0 hL0 hR el hel_mem
  intro e e2 t ht0 ht1 hVt hX2 hS1 hS2 hRe
  obtain ⟨kk1, f1, hk1, hf1⟩ := step_idx hS1
  obtain ⟨kk2, f2, hk2, hf2⟩ := step_idx hS2
  have := edge_step_head_f D P hreg idx h i hnorm ht0 ht1 hVt (U := e.2.1) (U'' := e2.2.2) (j1 := e.1) (j2 := e2.1) hS1 (by rw [← hX2]; exact hS2)
    kk2 f2 f1 kk1 (by rw [← hX2]; exact hk2) hf2 hf1 hk1 ((tyAt_iff hf1 2).mp hRe)
  exact (tyAt_iff hf2 2).mpr this

theorem walk_head_bwd (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx) (i : Fin M) (hnorm : NormSide D idx P i) {L : List (Fin N × Plane × Plane)}
    (W : WalkT D.toRegionDissection (toV2 (P.e i)) (P.v i) (P.v (i + 1)) L) {e0 el : Fin N × Plane × Plane}
    (hf : L.head? = some e0) (hl : L.getLast? = some el) :
    TyAt D idx el.1 el.2.2 2 → TyAt D idx e0.1 e0.2.2 2 := by
  classical
  have hU : ∃ s : ℝ, 0 ≤ s ∧ toV2 (P.v i - P.v i) = (s * (toV2 (P.e i)).1, s * (toV2 (P.e i)).2) :=
    ⟨0, le_rfl, by unfold toV2; ext <;> simp⟩
  have he0_mem : e0 ∈ L := List.mem_of_mem_head? hf
  intro hR
  refine walk_prop_backward D.toRegionDissection P hreg i (fun e => TyAt D idx e.1 e.2.2 2) ?_ rfl W hU el hl hR e0 he0_mem
  intro e e2 t ht0 ht1 hVt hX2 hS1 hS2 hRe
  obtain ⟨kk1, f1, hk1, hf1⟩ := step_idx hS1
  obtain ⟨kk2, f2, hk2, hf2⟩ := step_idx hS2
  have := edge_step_head_b D P hreg idx h i hnorm ht0 ht1 hVt (U := e.2.1) (U'' := e2.2.2) (j1 := e.1) (j2 := e2.1) hS1 (by rw [← hX2]; exact hS2)
    kk2 f2 f1 kk1 (by rw [← hX2]; exact hk2) hf2 hf1 hk1 ((tyAt_iff hf2 2).mp hRe)
  exact (tyAt_iff hf1 2).mpr this

theorem walk_tail_bwd (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx) (i : Fin M) (hnorm : NormSide D idx P i) {L : List (Fin N × Plane × Plane)}
    (W : WalkT D.toRegionDissection (toV2 (P.e i)) (P.v i) (P.v (i + 1)) L) {e0 el : Fin N × Plane × Plane}
    (hf : L.head? = some e0) (hl : L.getLast? = some el) :
    TyAt D idx el.1 el.2.1 2 → TyAt D idx e0.1 e0.2.1 2 := by
  classical
  have hU : ∃ s : ℝ, 0 ≤ s ∧ toV2 (P.v i - P.v i) = (s * (toV2 (P.e i)).1, s * (toV2 (P.e i)).2) :=
    ⟨0, le_rfl, by unfold toV2; ext <;> simp⟩
  have he0_mem : e0 ∈ L := List.mem_of_mem_head? hf
  intro hR
  refine walk_prop_backward D.toRegionDissection P hreg i (fun e => TyAt D idx e.1 e.2.1 2) ?_ rfl W hU el hl hR e0 he0_mem
  intro e e2 t ht0 ht1 hVt hX2 hS1 hS2 hRe
  obtain ⟨kk1, f1, hk1, hf1⟩ := step_idx hS1
  obtain ⟨kk2, f2, hk2, hf2⟩ := step_idx hS2
  have := edge_step_tail_b D P hreg idx h i hnorm ht0 ht1 hVt (U := e.2.1) (U'' := e2.2.2) (j1 := e.1) (j2 := e2.1) hS1 (by rw [← hX2]; exact hS2)
    kk2 f2 f1 kk1 (by rw [← hX2]; exact hk2) hf2 hf1 hk1 ((tyAt_iff hk2 2).mp hRe)
  exact (tyAt_iff hk1 2).mpr this

/-- **`γ` propagation around a vertex, forward** (Laczkovich Lemma 6.1, proof): `X = v_i`, `Y = v_{i+1}`, `Z = v_{i+2}`; the sides `XY`, `YZ` have normal interior vertices, `X` carries no `α, β` corner, `Y`
carries no `γ`.  Then `Z` carries a `γ` corner. -/
theorem gamma_prop_fwd (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx) (i : Fin M) (hn1 : NormSide D idx P i) (hn2 : NormSide D idx P (i + 1))
    (hX0 : cnt D idx (P.v i) 0 = 0) (hX1 : cnt D idx (P.v i) 1 = 0) (hY2 : cnt D idx (P.v (i + 1)) 2 = 0) :
    1 ≤ cnt D idx (P.v (i + 1 + 1)) 2 := by
  classical
  obtain ⟨L, e0, el, hW, hh, hl, hs1, hs2, hT0, hT1⟩ := edge_data D P hreg i
  obtain ⟨L'', e0'', el'', hW'', hh'', hl'', hs1'', hs2'', hT0'', hT1''⟩ := edge_data D P hreg (i + 1)
  have t0 : TyAt D idx e0.1 e0.2.1 2 := by
    intro kk hkk
    exact idx_two_of_cnt D idx hX0 hX1 (hkk.trans hs1)
  have t1 := walk_gamma_n D P hreg idx h i hn1 hW hh hl t0
  have hSi : TriStep (D.tile el.1) (toV2 (P.e i)) el.2.1 (P.v (i + 1)) := by rw [← hs2]; exact hT1
  have hSo : TriStep (D.tile e0''.1) (toV2 (P.e (i + 1))) (P.v (i + 1)) e0''.2.2 := by rw [← hs1'']; exact hT0''
  have hcs := corner_c_status D idx h P hreg i e0''.1 e0''.2.2 el.1 el.2.1 hSo hSi
  -- the last tile of `XY` has tail `γ`, so its step is not of length `c`
  obtain ⟨kki, fi, gi, hki, hfi, hfki, -⟩ := id hSi
  have tyi : idx el.1 kki = 2 := (tyAt_iff hki 2).mp t1
  have hne1 : dist el.2.1 (P.v (i + 1)) ≠ slen D 2 := by
    rw [← hki, ← hfi]
    exact step_dist_ne_c D idx h (Ne.symm hfki) (Or.inl tyi)
  have hne2 : ¬ dist (P.v (i + 1)) e0''.2.2 = slen D 2 := fun hh2 => hne1 (hcs.mp hh2)
  -- the first tile of `YZ`: tail at `Y` is not `γ`, so the head is `γ`
  obtain ⟨kko, fo, go, hko, hfo, hfko, -⟩ := id hSo
  have tyo : idx e0''.1 kko ≠ 2 := by
    intro e
    have := cnt_one D idx 2 hko e
    omega
  have tyo2 : idx e0''.1 fo = 2 := by
    by_contra hne
    apply hne2
    rw [← hko, ← hfo]
    exact step_dist_c D idx h.hidx (Ne.symm hfko) tyo hne
  have t2 : TyAt D idx e0''.1 e0''.2.2 2 := (tyAt_iff hfo 2).mpr tyo2
  have t3 := walk_head_fwd D P hreg idx h (i + 1) hn2 hW'' hh'' hl'' t2
  obtain ⟨kk, f, g, hk, hf, -⟩ := id hT1''
  have e2 := (tyAt_iff hf 2).mp t3
  have : (D.tile el''.1).pts f = P.v (i + 1 + 1) := by rw [hf, hs2'']
  exact cnt_one D idx 2 this e2

/-- **`γ` propagation around a vertex, backward**: `X = v_{i+2}`, `Y = v_{i+1}`, `Z = v_i`; same hypotheses with the roles of the sides exchanged.  Then `Z` carries a `γ` corner. -/
theorem gamma_prop_bwd (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx) (i : Fin M) (hn1 : NormSide D idx P i) (hn2 : NormSide D idx P (i + 1))
    (hX0 : cnt D idx (P.v (i + 1 + 1)) 0 = 0) (hX1 : cnt D idx (P.v (i + 1 + 1)) 1 = 0) (hY2 : cnt D idx (P.v (i + 1)) 2 = 0) :
    1 ≤ cnt D idx (P.v i) 2 := by
  classical
  obtain ⟨L, e0, el, hW, hh, hl, hs1, hs2, hT0, hT1⟩ := edge_data D P hreg i
  obtain ⟨L'', e0'', el'', hW'', hh'', hl'', hs1'', hs2'', hT0'', hT1''⟩ := edge_data D P hreg (i + 1)
  have t0 : TyAt D idx el''.1 el''.2.2 2 := by
    intro kk hkk
    exact idx_two_of_cnt D idx hX0 hX1 (hkk.trans hs2'')
  have t1 := walk_head_bwd D P hreg idx h (i + 1) hn2 hW'' hh'' hl'' t0
  have hSi : TriStep (D.tile el.1) (toV2 (P.e i)) el.2.1 (P.v (i + 1)) := by rw [← hs2]; exact hT1
  have hSo : TriStep (D.tile e0''.1) (toV2 (P.e (i + 1))) (P.v (i + 1)) e0''.2.2 := by rw [← hs1'']; exact hT0''
  have hcs := corner_c_status D idx h P hreg i e0''.1 e0''.2.2 el.1 el.2.1 hSo hSi
  obtain ⟨kko, fo, go, hko, hfo, hfko, -⟩ := id hSo
  have tyo : idx e0''.1 fo = 2 := (tyAt_iff hfo 2).mp t1
  have hne1 : dist (P.v (i + 1)) e0''.2.2 ≠ slen D 2 := by
    rw [← hko, ← hfo]
    exact step_dist_ne_c D idx h (Ne.symm hfko) (Or.inr tyo)
  have hne2 : ¬ dist el.2.1 (P.v (i + 1)) = slen D 2 := fun hh2 => hne1 (hcs.mpr hh2)
  obtain ⟨kki, fi, gi, hki, hfi, hfki, -⟩ := id hSi
  have tyi : idx el.1 fi ≠ 2 := by
    intro e
    have := cnt_one D idx 2 hfi e
    omega
  have tyi2 : idx el.1 kki = 2 := by
    by_contra hne
    apply hne2
    rw [← hki, ← hfi]
    exact step_dist_c D idx h.hidx hfki.symm hne tyi
  have t2 : TyAt D idx el.1 el.2.1 2 := (tyAt_iff hki 2).mpr tyi2
  have t3 := walk_tail_bwd D P hreg idx h i hn1 hW hh hl t2
  obtain ⟨kk, f, g, hk, hf, -⟩ := id hT0
  have e2 := (tyAt_iff hk 2).mp t3
  have : (D.tile e0.1).pts kk = P.v i := by rw [hk, hs1]
  exact cnt_one D idx 2 this e2

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.gamma_prop_fwd
#print axioms Erdos634.Draft.LaczFormal.RG.gamma_prop_bwd

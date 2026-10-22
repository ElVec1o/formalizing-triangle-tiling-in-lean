-- Draft/LaczFormalRG9SideC2.lean -- Laczkovich DCG 48 (2012), Lemma 4.4 (ii) for a polygon side, `Gamma_c`, general gamma (normal interior side vertices): a `{alpha, beta}` type pair (tail, head) of a tile of the walk is copied
-- by the next tile (`edge_step_pair_c`, from `side_step_all` of the relabeled model), hence if the first tile of the walk along the side carries the pair, every tile does and the side is an integer multiple of `c`
-- (`edge_multiple_c`).  UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Lemma 4.4 (ii)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG9Side
import Erdos634.Draft.LaczFormalRG4Walk

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

set_option maxHeartbeats 3200000 in
/-- **The `γ` rule along a side** (Laczkovich Lemma 4.4, local content): two consecutive tiles `j1` (ending at `V`) and `j2` (starting at `V`) of the walk along the edge `i`, `V` in the relative
interior of the edge.  If `j1` has `γ` at its tail then `j2` has `γ` at its tail `V`. -/
theorem edge_step_pair_c (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx) (i : Fin M) (hnorm : ∀ V : Plane, (∃ j k, (D.tile j).pts k = V) → (∃ t : ℝ, 0 < t ∧ t < 1 ∧ V = (1 - t) • P.v i + t • P.v (i + 1)) → cnt D idx V 0 = 1 ∧ cnt D idx V 1 = 1 ∧ cnt D idx V 2 = 1) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {V : Plane} (hV : V = (1 - t) • P.v i + t • P.v (i + 1)) {U U'' : Plane} {j1 j2 : Fin N}
    (h1 : TriStep (D.tile j1) (toV2 (P.e i)) U V) (h2 : TriStep (D.tile j2) (toV2 (P.e i)) V U'')
    (kR fR kL fL : Fin 3) (hR1 : (D.tile j2).pts kR = V) (hR2 : (D.tile j2).pts fR = U'')
    (hL1 : (D.tile j1).pts kL = V) (hL2 : (D.tile j1).pts fL = U) :
    ((idx j1 fL = 0 ∧ idx j1 kL = 1) ∨ (idx j1 fL = 1 ∧ idx j1 kL = 0)) → idx j2 kR = idx j1 fL ∧ idx j2 fR = idx j1 kL := by
  classical
  intro hg
  have hG := h.caseG
  haveI : HasFansC (relabelC D).toRegionDissection := (inferInstance : HasFansC D.toRegionDissection)
  have hvert : ∃ j k, (D.tile j).pts k = V := ⟨j2, kR, hR1⟩
  obtain ⟨pT, F, s1, s2, s3, hpd, hF, hc2, hcls, hno1, hno2⟩ := edge_vertex_data_n D P hreg idx h i hnorm ht0 ht1 hV hvert
  have hi : V ∈ (D.tile j1).carrier := hL1 ▸ subset_convexHull ℝ _ ⟨kL, rfl⟩
  have hi2 : V ∈ (D.tile j2).carrier := hR1 ▸ subset_convexHull ℝ _ ⟨kR, rfl⟩
  have e1 := fan_start_unique hF hpd h2 hi2
  have e3 := fan_end_unique hF hpd h1 hi
  have hj2 : s1.1 = j2 := by rw [← e1]
  have hj1 : s3.1 = j1 := by rw [← e3]
  have hR2' : Par (toV2 ((D.tile s1.1).pts fR - V)) pT := by
    rw [hj2, hR2]
    obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := h2
    exact hpar.trans hpd.symm
  have hL2' : Par (toV2 ((D.tile s3.1).pts fL - V)) (-pT.1, -pT.2) := by
    rw [hj1, hL2]
    obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := h1
    have hneg : toV2 (U - V) = (-(toV2 (V - U)).1, -(toV2 (V - U)).2) := by
      unfold toV2; ext <;> simp
    rw [hneg]
    exact (par_neg hpar).trans (par_neg hpd).symm
  rcases hcls with hnorm | hall
  · have hnorm' : ∀ k1 k2 k3, (D.tile s1.1).pts k1 = V → (D.tile s2.1).pts k2 = V → (D.tile s3.1).pts k3 = V →
        relabelCIdx idx s1.1 k1 ≠ relabelCIdx idx s2.1 k2 ∧ relabelCIdx idx s1.1 k1 ≠ relabelCIdx idx s3.1 k3 ∧
        relabelCIdx idx s2.1 k2 ≠ relabelCIdx idx s3.1 k3 := by
      intro k1 k2 k3 a1 a2 a3
      obtain ⟨n1, n2, n3⟩ := hnorm k1 k2 k3 a1 a2 a3
      have inj : ∀ (a b : Fin N) (k k' : Fin 3), relabelCIdx idx a k = relabelCIdx idx b k' → idx a k = idx b k' := by
        intro a b k k' e
        unfold relabelCIdx at e
        rw [relabelIdx_apply, relabelIdx_apply] at e
        exact Equiv.injective _ e
      exact ⟨fun e => n1 (inj _ _ _ _ e), fun e => n2 (inj _ _ _ _ e), fun e => n3 (inj _ _ _ _ e)⟩
    have hs0 : slen (relabelC D) 0 = slen D 2 := relabelC_slen0 D
    have := side_step_all (relabelC D) (relabelCIdx idx) hG.hidx V hF hc2 hG.hab hG.hac hnorm' (by rw [hs0]; exact hno1) (by rw [hs0]; exact hno2)
      kR fR kL fL (by rw [hj2]; exact hR1) hR2' (by rw [hj1]; exact hL1) hL2'
    rw [hj2, hj1] at this
    have h3 := this.1
    unfold relabelCIdx at h3
    rw [relabelIdx_apply, relabelIdx_apply, relabelIdx_apply, relabelIdx_apply] at h3
    have s1 : ∀ x : Fin 3, (Equiv.swap (0 : Fin 3) 2).symm x = 1 ↔ x = 1 := by decide
    have s2 : ∀ x : Fin 3, (Equiv.swap (0 : Fin 3) 2).symm x = 2 ↔ x = 0 := by decide
    have hh := h3 (by
      rcases hg with ⟨a, b⟩ | ⟨a, b⟩
      · right; exact ⟨(s2 _).mpr a, (s1 _).mpr b⟩
      · left; exact ⟨(s1 _).mpr a, (s2 _).mpr b⟩)
    exact ⟨Equiv.injective _ hh.1, Equiv.injective _ hh.2⟩
  · exfalso
    have hk := hall kL (by rw [hj1]; exact hL1)
    rw [hj1] at hk
    rcases hg with ⟨a, b⟩ | ⟨a, b⟩ <;> omega


/-- A tile with a step whose type pair (tail, head) is `(β,γ)` or `(γ,β)` has that step of length `a`. -/
theorem step_len_pair_c (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    {j : Fin N} {d : V2} {U U' : Plane} (hS : TriStep (D.tile j) d U U') {a b : Fin 3} (hab : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0))
    (ha : TyAt D idx j U a) (hb : TyAt D idx j U' b) : dist U U' = slen D 2 := by
  obtain ⟨kk, f, hk, hf⟩ := step_idx hS
  have e1 := (tyAt_iff hk a).mp ha
  have e2 := (tyAt_iff hf b).mp hb
  rw [← hk, ← hf, hidx, e1, e2]
  unfold slen
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · rw [dist_comm]; rfl

/-- **The edge is an integer multiple of `a`** (Laczkovich Lemma 4.3 (ii)): if the first tile of the walk along the edge `i` has the type pair `(β,γ)` or `(γ,β)` (tail, head),
every tile of the walk has that pair and side `a`, so the edge has length `m a`, `m ≥ 1`. -/
theorem edge_multiple_c (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx) (i : Fin M) (hnorm : ∀ V : Plane, (∃ j k, (D.tile j).pts k = V) → (∃ t : ℝ, 0 < t ∧ t < 1 ∧ V = (1 - t) • P.v i + t • P.v (i + 1)) → cnt D idx V 0 = 1 ∧ cnt D idx V 1 = 1 ∧ cnt D idx V 2 = 1) {L : List (Fin N × Plane × Plane)}
    (W : WalkT D.toRegionDissection (toV2 (P.e i)) (P.v i) (P.v (i + 1)) L) {e0 : Fin N × Plane × Plane} (hf : L.head? = some e0)
    {a b : Fin 3} (hab : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)) (h0 : TyAt D idx e0.1 e0.2.1 a ∧ TyAt D idx e0.1 e0.2.2 b) :
    ∃ m : ℕ, 0 < m ∧ P.side i = m * slen D 2 := by
  classical
  have hU : ∃ s : ℝ, 0 ≤ s ∧ toV2 (P.v i - P.v i) = (s * (toV2 (P.e i)).1, s * (toV2 (P.e i)).2) :=
    ⟨0, le_rfl, by unfold toV2; ext <;> simp⟩
  obtain ⟨L0, hL0⟩ : ∃ L0, L = e0 :: L0 := by
    cases L with
    | nil => simp at hf
    | cons x L0 => simp at hf; exact ⟨L0, by rw [hf]⟩
  have local_step : ∀ (e e2 : Fin N × Plane × Plane) (t : ℝ), 0 < t → t < 1 → e.2.2 = (1 - t) • P.v i + t • P.v (i + 1) → e2.2.1 = e.2.2 →
      TriStep (D.tile e.1) (toV2 (P.e i)) e.2.1 e.2.2 → TriStep (D.tile e2.1) (toV2 (P.e i)) e2.2.1 e2.2.2 →
      ∀ kk1 f1 kk2 f2 : Fin 3, (D.tile e.1).pts kk1 = e.2.1 → (D.tile e.1).pts f1 = e.2.2 → (D.tile e2.1).pts kk2 = e2.2.1 → (D.tile e2.1).pts f2 = e2.2.2 →
      (((idx e.1 kk1 = 0 ∧ idx e.1 f1 = 1) ∨ (idx e.1 kk1 = 1 ∧ idx e.1 f1 = 0)) → idx e2.1 kk2 = idx e.1 kk1 ∧ idx e2.1 f2 = idx e.1 f1) := by
    intro e e2 t ht0 ht1 hVt hX2 hS1 hS2 kk1 f1 kk2 f2 hk1 hf1 hk2 hf2
    exact (edge_step_pair_c D P hreg idx h i hnorm ht0 ht1 hVt (U := e.2.1) (U'' := e2.2.2) (j1 := e.1) (j2 := e2.1) hS1 (by rw [← hX2]; exact hS2)
      kk2 f2 f1 kk1 (by rw [← hX2, ← hk2]) (by rw [hf2]) hf1 hk1)
  have hall := walk_prop_forward D.toRegionDissection P hreg i (fun e => TyAt D idx e.1 e.2.1 a ∧ TyAt D idx e.1 e.2.2 b) (by
      intro e e2 t ht0 ht1 hVt hX2 hS1 hS2 hRe
      obtain ⟨kk1, f1, hk1, hf1⟩ := step_idx hS1
      obtain ⟨kk2, f2, hk2, hf2⟩ := step_idx hS2
      have ls := local_step e e2 t ht0 ht1 hVt hX2 hS1 hS2 kk1 f1 kk2 f2 hk1 hf1 hk2 hf2
      have ha : idx e.1 kk1 = a := (tyAt_iff hk1 a).mp hRe.1
      have hb : idx e.1 f1 = b := (tyAt_iff hf1 b).mp hRe.2
      have := ls (by rw [ha, hb]; exact hab)
      exact ⟨(tyAt_iff hk2 a).mpr (by rw [this.1, ha]), (tyAt_iff hf2 b).mpr (by rw [this.2, hb])⟩) rfl W hU e0 L0 hL0 h0
  have hlen : ∀ e ∈ L, dist e.2.1 e.2.2 = slen D 2 := fun e he =>
    step_len_pair_c D idx h.hidx (walkT_mem_step W e he) hab (hall e he).1 (hall e he).2
  have hsum := walkT_dist_sum W
  have hsumA : (L.map fun e => dist e.2.1 e.2.2).sum = (L.map fun e => dist e.2.1 e.2.2).length • slen D 2 :=
    List.sum_eq_card_nsmul _ _ (fun x hx => by
      obtain ⟨e', he', rfl⟩ := List.mem_map.mp hx
      exact hlen e' he')
  rw [List.length_map, nsmul_eq_mul] at hsumA
  refine ⟨L.length, by rw [hL0]; simp, ?_⟩
  rw [ConvPoly.side, ← hsum, hsumA]


end Erdos634.Draft.LaczFormal.RG

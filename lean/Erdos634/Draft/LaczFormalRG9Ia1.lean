-- Draft/LaczFormalRG9Ia1.lean -- Laczkovich DCG 48 (2012), Lemma 4.3 (i) for a polygon side (general gamma, `Gamma_a`): if the first tile of the side has `gamma` at its tail and the last tile has `gamma` at its head
-- (both ends single `gamma` corners), contradiction.  Proof by the invariant `(tail gamma, head beta) or head alpha` along the walk (rules R1 and R4 of the local step, and the distinctness of the types at the
-- normal junction).  Also the `gamma`-vertex step: one of the two sides at a single-`gamma` vertex is an integer multiple of `a` (Lemma 4.3 (ii)).  UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Lemma 4.3 and its proof, Fig. 3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG9WalkA

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- **The local step along a polygon edge** (Laczkovich Lemma 4.3, local content, with Lemma 8.1 (ii),(iii)): two consecutive tiles `j1` (ending at `V`) and `j2` (starting at `V`) of the walk along the
edge `i`, `V` in the relative interior of the edge. (βγ) a `{β,γ}` pair of the tile `j1` is copied by `j2`; (α) `α` at the tail of `j1` gives `α` at the tail of `j2`; (α') `α` at the head of `j2`
gives `α` at the head of `j1`. -/
theorem edge_consec_a2 (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseA D idx) (i : Fin M) (hnormv : ∀ V : Plane, (∃ j k, (D.tile j).pts k = V) → (∃ t : ℝ, 0 < t ∧ t < 1 ∧ V = (1 - t) • P.v i + t • P.v (i + 1)) → cnt D idx V 0 = 1 ∧ cnt D idx V 1 = 1 ∧ cnt D idx V 2 = 1)
    (hno : ∀ V : Plane, (∃ j k, (D.tile j).pts k = V) → (∃ t : ℝ, 0 < t ∧ t < 1 ∧ V = (1 - t) • P.v i + t • P.v (i + 1)) → ∀ H', ¬ GaEdge D.toRegionDissection (slen D 0) V H') {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {V : Plane}
    (hV : V = (1 - t) • P.v i + t • P.v (i + 1)) {U U'' : Plane} {j1 j2 : Fin N}
    (h1 : TriStep (D.tile j1) (toV2 (P.e i)) U V) (h2 : TriStep (D.tile j2) (toV2 (P.e i)) V U'')
    (kR fR kL fL : Fin 3) (hR1 : (D.tile j2).pts kR = V) (hR2 : (D.tile j2).pts fR = U'')
    (hL1 : (D.tile j1).pts kL = V) (hL2 : (D.tile j1).pts fL = U) :
    (((idx j1 fL = 1 ∧ idx j1 kL = 2) ∨ (idx j1 fL = 2 ∧ idx j1 kL = 1)) → idx j2 kR = idx j1 fL ∧ idx j2 fR = idx j1 kL) ∧
    (idx j1 fL = 0 → idx j2 kR = 0) ∧ (idx j2 fR = 0 → idx j1 kL = 0) ∧
    (((idx j2 kR = 1 ∧ idx j2 fR = 2) ∨ (idx j2 kR = 2 ∧ idx j2 fR = 1)) → idx j2 kR = idx j1 fL ∧ idx j2 fR = idx j1 kL) ∧
    idx j2 kR ≠ idx j1 kL := by
  classical
  have hvert : ∃ j k, (D.tile j).pts k = V := ⟨j2, kR, hR1⟩
  obtain ⟨pT, F, s1, s2, s3, hpd, hF, hc2, hnorm, hno1, hno2⟩ := edge_vertex_data_a D P hreg idx h i hnormv ht0 ht1 hV hvert (hno V hvert ⟨t, ht0, ht1, hV⟩)
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
  have := side_step_all D idx h.hidx V hF hc2 h.hab h.hac hnorm hno1 hno2 kR fR kL fL (by rw [hj2]; exact hR1) hR2'
    (by rw [hj1]; exact hL1) hL2'
  rw [hj2, hj1] at this
  obtain ⟨k2, hk2⟩ := hc2
  have hd := (hnorm kR k2 kL (by rw [hj2]; exact hR1) hk2 (by rw [hj1]; exact hL1)).2.1
  rw [hj2, hj1] at hd
  exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2, hd⟩


/-- Finite check of the invariant step. -/
theorem inv_step : ∀ t1 h1 t2 h2 : Fin 3, t1 ≠ h1 → t2 ≠ h2 → h1 ≠ t2 → ((t1 = 2 ∧ h1 = 1) ∨ h1 = 0) →
    (((t1 = 1 ∧ h1 = 2) ∨ (t1 = 2 ∧ h1 = 1)) → t2 = t1 ∧ h2 = h1) →
    (((t2 = 1 ∧ h2 = 2) ∨ (t2 = 2 ∧ h2 = 1)) → t2 = t1 ∧ h2 = h1) → ((t2 = 2 ∧ h2 = 1) ∨ h2 = 0) := by decide

set_option maxHeartbeats 3200000 in
/-- **Lemma 4.3 (i), polygon side, `Γ_a`** (general `γ`): the first tile of the walk along the side has `γ` at its tail and the last tile has `γ` at its head: impossible. -/
theorem side_no_gg_a (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseA D idx) (i : Fin M)
    (hnormv : ∀ V : Plane, (∃ j k, (D.tile j).pts k = V) → (∃ t : ℝ, 0 < t ∧ t < 1 ∧ V = (1 - t) • P.v i + t • P.v (i + 1)) →
      cnt D idx V 0 = 1 ∧ cnt D idx V 1 = 1 ∧ cnt D idx V 2 = 1)
    (hno : ∀ V : Plane, (∃ j k, (D.tile j).pts k = V) → (∃ t : ℝ, 0 < t ∧ t < 1 ∧ V = (1 - t) • P.v i + t • P.v (i + 1)) →
      ∀ H', ¬ GaEdge D.toRegionDissection (slen D 0) V H')
    {L : List (Fin N × Plane × Plane)} (W : WalkT D.toRegionDissection (toV2 (P.e i)) (P.v i) (P.v (i + 1)) L) {e0 el : Fin N × Plane × Plane}
    (hf : L.head? = some e0) (hl : L.getLast? = some el) :
    TyAt D idx e0.1 e0.2.1 2 → TyAt D idx el.1 el.2.2 2 → False := by
  classical
  intro t0 t1
  have hU : ∃ s : ℝ, 0 ≤ s ∧ toV2 (P.v i - P.v i) = (s * (toV2 (P.e i)).1, s * (toV2 (P.e i)).2) :=
    ⟨0, le_rfl, by unfold toV2; ext <;> simp⟩
  obtain ⟨L0, hL0⟩ : ∃ L0, L = e0 :: L0 := by
    cases L with
    | nil => simp at hf
    | cons x L0 => simp at hf; exact ⟨L0, by rw [hf]⟩
  have hel_mem : el ∈ L := List.mem_of_getLast? hl
  have he0_mem : e0 ∈ L := by rw [hL0]; simp
  have base : (TyAt D idx e0.1 e0.2.1 2 ∧ TyAt D idx e0.1 e0.2.2 1) ∨ TyAt D idx e0.1 e0.2.2 0 := by
    obtain ⟨kk, f, g, hk, hf', hfk, -⟩ := walkT_mem_step W e0 he0_mem
    have hne : idx e0.1 f ≠ idx e0.1 kk := fun e => hfk ((idx e0.1).injective e)
    have e2 : idx e0.1 kk = 2 := (tyAt_iff hk 2).mp t0
    have : idx e0.1 f = 0 ∨ idx e0.1 f = 1 := by
      generalize idx e0.1 f = z at hne
      rw [e2] at hne
      fin_cases z <;> simp_all
    rcases this with h0 | h1
    · exact Or.inr ((tyAt_iff hf' 0).mpr h0)
    · exact Or.inl ⟨t0, (tyAt_iff hf' 1).mpr h1⟩
  have hall := walk_prop_forward D.toRegionDissection P hreg i (fun e => (TyAt D idx e.1 e.2.1 2 ∧ TyAt D idx e.1 e.2.2 1) ∨ TyAt D idx e.1 e.2.2 0) (by
      intro e e2 t ht0 ht1 hVt hX2 hS1 hS2 hRe
      obtain ⟨kk1, f1, g1, hk1, hf1, hfk1, -⟩ := id hS1
      obtain ⟨kk2, f2, g2, hk2, hf2, hfk2, -⟩ := id hS2
      have ec := edge_consec_a2 D P hreg idx h i hnormv hno ht0 ht1 hVt (U := e.2.1) (U'' := e2.2.2) (j1 := e.1) (j2 := e2.1) hS1 (by rw [← hX2]; exact hS2)
        kk2 f2 f1 kk1 (by rw [← hX2, ← hk2]) (by rw [hf2]) hf1 hk1
      have d1 : idx e.1 kk1 ≠ idx e.1 f1 := fun e' => hfk1 ((idx e.1).injective e').symm
      have d2 : idx e2.1 kk2 ≠ idx e2.1 f2 := fun e' => hfk2 ((idx e2.1).injective e').symm
      have hR : ((idx e.1 kk1 = 2 ∧ idx e.1 f1 = 1) ∨ idx e.1 f1 = 0) := by
        rcases hRe with ⟨a, b⟩ | b
        · exact Or.inl ⟨(tyAt_iff hk1 2).mp a, (tyAt_iff hf1 1).mp b⟩
        · exact Or.inr ((tyAt_iff hf1 0).mp b)
      have := inv_step (idx e.1 kk1) (idx e.1 f1) (idx e2.1 kk2) (idx e2.1 f2) d1 d2 (Ne.symm ec.2.2.2.2) hR ec.1 ec.2.2.2.1
      rcases this with ⟨a, b⟩ | b
      · exact Or.inl ⟨(tyAt_iff hk2 2).mpr a, (tyAt_iff hf2 1).mpr b⟩
      · exact Or.inr ((tyAt_iff hf2 0).mpr b)) rfl W hU e0 L0 hL0 base
  have hlast := hall el hel_mem
  obtain ⟨kk, f, g, hk, hf', hfk, -⟩ := walkT_mem_step W el hel_mem
  have e2 : idx el.1 f = 2 := (tyAt_iff hf' 2).mp t1
  rcases hlast with ⟨-, b⟩ | b
  · have := (tyAt_iff hf' 1).mp b
    rw [e2] at this
    exact absurd this (by decide)
  · have := (tyAt_iff hf' 0).mp b
    rw [e2] at this
    exact absurd this (by decide)

/-- Consecutive edges of a strictly convex polygon turn left. -/
theorem cross_pos' (P : ConvPoly M) (i : Fin M) : 0 < cross2 (P.e (i - 1)) (P.e i) := by
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := ConvPoly.fin_facts P.three_le i
  have := P.left (i - 1) (i + 1) (by intro h; exact f4 h) (by rw [f5]; exact f1)
  have e1 : P.v (i - 1 + 1) - P.v (i - 1) = P.e (i - 1) := rfl
  have e2 : P.v (i + 1) - P.v (i - 1) = P.e (i - 1) + P.e i := by
    unfold ConvPoly.e; rw [f5]; abel
  rw [e1, e2, cross2_add_right, cross2_self] at this
  simpa using this

/-- **One of the two sides at a single-`γ` vertex is an integer multiple of `a`** (Laczkovich Lemma 4.3 (ii), for the polygon vertex `v_{j+1}` with a single `γ` corner): the side `j` (incoming) or the
side `j + 1` (outgoing).  Hypotheses: normal tiling vertices in the relative interior of both sides, no edge of `Γ_a` starting there. -/
theorem gamma_vertex_multiple (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseA D idx) (j : Fin M)
    (hS0 : cnt D idx (P.v (j + 1)) 0 = 0) (hS1 : cnt D idx (P.v (j + 1)) 1 = 0) (hS2 : cnt D idx (P.v (j + 1)) 2 = 1)
    (hnormI : ∀ V : Plane, (∃ jj k, (D.tile jj).pts k = V) → (∃ t : ℝ, 0 < t ∧ t < 1 ∧ V = (1 - t) • P.v j + t • P.v (j + 1)) →
      cnt D idx V 0 = 1 ∧ cnt D idx V 1 = 1 ∧ cnt D idx V 2 = 1)
    (hnoI : ∀ V : Plane, (∃ jj k, (D.tile jj).pts k = V) → (∃ t : ℝ, 0 < t ∧ t < 1 ∧ V = (1 - t) • P.v j + t • P.v (j + 1)) →
      ∀ H', ¬ GaEdge D.toRegionDissection (slen D 0) V H')
    (hnormO : ∀ V : Plane, (∃ jj k, (D.tile jj).pts k = V) → (∃ t : ℝ, 0 < t ∧ t < 1 ∧ V = (1 - t) • P.v (j + 1) + t • P.v (j + 1 + 1)) →
      cnt D idx V 0 = 1 ∧ cnt D idx V 1 = 1 ∧ cnt D idx V 2 = 1)
    (hnoO : ∀ V : Plane, (∃ jj k, (D.tile jj).pts k = V) → (∃ t : ℝ, 0 < t ∧ t < 1 ∧ V = (1 - t) • P.v (j + 1) + t • P.v (j + 1 + 1)) →
      ∀ H', ¬ GaEdge D.toRegionDissection (slen D 0) V H') :
    (∃ m : ℕ, 0 < m ∧ P.side j = m * slen D 0) ∨ (∃ m : ℕ, 0 < m ∧ P.side (j + 1) = m * slen D 0) := by
  classical
  obtain ⟨L, e0, el, hW, hh, hl, hs1, hs2, hT0, hT1⟩ := edge_data D P hreg (j + 1)
  obtain ⟨L', e0', el', hW', hh', hl', hs1', hs2', hT0', hT1'⟩ := edge_data D P hreg j
  have t_e0 : TyAt D idx e0.1 e0.2.1 2 := fun kk hkk => idx_two_of_cnt D idx hS0 hS1 (hkk.trans hs1)
  have t_el' : TyAt D idx el'.1 el'.2.2 2 := fun kk hkk => idx_two_of_cnt D idx hS0 hS1 (hkk.trans hs2')
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar0, -⟩ := id hT0
  have hne0 : idx e0.1 f ≠ idx e0.1 kk := fun e => hfk ((idx e0.1).injective e)
  have e2 : idx e0.1 kk = 2 := (tyAt_iff hk 2).mp t_e0
  have hcases : idx e0.1 f = 0 ∨ idx e0.1 f = 1 := by
    have key : ∀ z : Fin 3, z ≠ 2 → z = 0 ∨ z = 1 := by decide
    exact key _ (by rw [← e2]; exact hne0)
  rcases hcases with hhead | hhead
  · -- head of the first outgoing tile is `α`: the incoming side carries the `β` end
    left
    obtain ⟨kk', f', g', hk', hf', hfk', hgk', hgf', hpar1, -⟩ := id hT1'
    -- same tile
    have hj : e0.1 = el'.1 := by
      by_contra hne
      have := cnt_two D idx 2 hne (hk.trans hs1) (hf'.trans hs2') e2 ((tyAt_iff hf' 2).mp t_el')
      omega
    have hf'' : (D.tile e0.1).pts f' = P.v (j + 1) := by rw [hj]; exact hf'.trans hs2'
    have hf'kk : f' = kk := (D.tile e0.1).indep.injective (hf''.trans (hk.trans hs1).symm)
    have hkk'0 : (D.tile e0.1).pts kk' = el'.2.1 := by rw [hj]; exact hk'
    have hfkk' : f ≠ kk' := by
      intro hfe
      have hY : e0.2.2 = el'.2.1 := by rw [← hf, hfe, hkk'0]
      obtain ⟨c, hc, hcw⟩ := hpar0.smul
      obtain ⟨c', hc', hcw'⟩ := hpar1.smul
      rw [hs1] at hcw
      rw [hs2', ← hY] at hcw'
      have a1 := congrArg Prod.fst hcw
      have a2 := congrArg Prod.snd hcw
      have b1 := congrArg Prod.fst hcw'
      have b2 := congrArg Prod.snd hcw'
      simp only [toV2_sub, toV2, PiLp.sub_apply] at a1 a2 b1 b2
      have hcr := cross_pos' P (j + 1)
      have e1 : j + 1 - 1 = j := add_sub_cancel_right j 1
      rw [e1] at hcr
      have key : c * cross2 (P.e j) (P.e (j + 1)) = 0 := by
        unfold cross2
        linear_combination (-((P.e j).ofLp 0)) * (a2 + b2) + ((P.e j).ofLp 1) * (a1 + b1)
      have := mul_pos hc hcr
      linarith
    have hkk'ne : kk' ≠ kk := fun e => hfk' (hf'kk.trans e.symm)
    have hty1 : idx e0.1 kk' = 1 := by
      have key : ∀ x : Fin 3, x ≠ 0 → x ≠ 2 → x = 1 := by decide
      apply key
      · intro e; exact hfkk' ((idx e0.1).injective (e.trans hhead.symm)).symm
      · intro e; exact hkk'ne ((idx e0.1).injective (e.trans e2.symm))
    have hel1 : TyAt D idx el'.1 el'.2.1 1 ∧ TyAt D idx el'.1 el'.2.2 2 := by
      refine ⟨(tyAt_iff hk' 1).mpr ?_, t_el'⟩
      rw [← hj]; exact hty1
    have hR1 := (walk_rules_a D P hreg idx h j hnormI hnoI hW' hh' hl').1 1 2 (Or.inl ⟨rfl, rfl⟩)
    obtain ⟨m, hm, hs⟩ := edge_multiple_a D P hreg idx h j hnormI hnoI hW' hh' (a := 1) (b := 2) (Or.inl ⟨rfl, rfl⟩) (hR1.mpr hel1)
    exact ⟨m, hm, hs⟩
  · right
    obtain ⟨m, hm, hs⟩ := edge_multiple_a D P hreg idx h (j + 1) hnormO hnoO hW hh (a := 2) (b := 1) (Or.inr ⟨rfl, rfl⟩) ⟨t_e0, (tyAt_iff hf 1).mpr hhead⟩
    exact ⟨m, hm, hs⟩

end Erdos634.Draft.LaczFormal.RG

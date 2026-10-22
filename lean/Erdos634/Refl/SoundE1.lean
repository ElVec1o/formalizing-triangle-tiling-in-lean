import Erdos634.Refl.CheckE
import Erdos634.Refl.SoundStage13

/-! Refl/SoundE1.lean -- `LocalFactsE`, `hlex_soundE`, `hfree_soundE`: verbatim copies of SoundStage5/7 for `nodeLocalOkE`
    (only the `blk` field differs; the proofs use no `blk`).  UNAUDITED. -/

set_option linter.unusedSimpArgs false
open Erdos634.CertNode Erdos634.PlacementCompleteness
open Erdos634.Geometry (Plane)

namespace Refl

/-- the unpacked content of `nodeLocalOkE` -/
structure LocalFactsE (I : Inst) (cfg : List _root_.Tri) (n : Node) : Prop where
  vw : 0 < n.v.w
  dw : 0 < n.d.w
  unit : n.d.x * n.d.x + I.Dn * n.d.y * n.d.y = n.d.w * n.d.w
  tauN : 0 < n.tauN
  tauD : 0 < n.tauD
  flen : n.fedges.length = cfg.length
  r1 : Bsp.check cfg [] [] false
      (List.map (fun l => (l, false)) (tgtLins I) ++ [(yltL n.v, true)]) [] n.t1 = true
  r2 : Bsp.check cfg (tgtLins I ++ [ygeL n.v]) [(yltL n.v, false), (xltL n.v, true)] true
      (List.map (fun l => (l, false)) (tgtLins I) ++ [(ygeL n.v, false), (xltL n.v, true)]) [] n.t2 = true
  tgtQ : ((tgtLins I).all fun l => okPos (quad I n.v n.d l) n.tauN n.tauD) = true
  tileQ : ((cfg.zip n.fedges).all fun x => okNeg (quad I n.v n.d (x.1.edge x.2)) n.tauN n.tauD) = true
  blk : blockedOkE I cfg n.v n.d n.hb = true

theorem nodeLocalOkE_facts (I : Inst) (cfg : List _root_.Tri) (n : Node)
    (h : nodeLocalOkE I cfg n = true) : LocalFactsE I cfg n := by
  unfold nodeLocalOkE at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩



/-- **`hlex`**: the two checked BSPs give a closed superset of the unfilled region on which `v` is
lexicographically least. -/
theorem hlex_soundE (Dn : ℝ) (hD : 0 < Dn) (I : Inst) (htok : I.tgt.ok = true)
    (cfg : List _root_.Tri) (hcfg : ∀ t ∈ cfg, t.ok = true) (n : Node) (F : LocalFactsE I cfg n)
    {N : ℕ} (D : Erdos634.Geometry.CongruentDissection N)
    (htarget : D.target.carrier = I.tgt.carr Dn) (S : Finset (Fin N))
    (hS : ∀ t ∈ cfg, ∃ i ∈ S, (D.tile i).carrier = t.carr Dn) :
    ∀ p ∈ closure (unfilled D.toDissection S), LexLE (n.v.re Dn) p := by
  set C : Set Plane := I.tgt.carr Dn ∩ halfL Dn (ygeL n.v) ∩
    (halfL Dn (xgeL n.v) ∪ cellSet Dn cfg (tgtLins I ++ [ygeL n.v]) n.t2 []) with hC
  have hClosed : IsClosed C :=
    ((tri_carr_closed Dn hD _ htok).inter (isClosed_halfR _ _ _ _)).inter
      ((isClosed_halfR _ _ _ _).union (cellSet_closed Dn cfg _ n.t2 []))
  refine hlex_of D.toDissection S (n.v.re Dn) C hClosed ?_ ?_
  · -- U ⊆ C
    intro p hp hnot
    have hnt : ∀ t ∈ cfg, p ∉ t.carr Dn := by
      intro t ht hpt
      obtain ⟨i, hi, hti⟩ := hS t ht
      exact hnot i hi (by rw [hti]; exact hpt)
    obtain ⟨X, Y, rfl⟩ := exists_rp hD p
    have hpt : rp Dn X Y ∈ I.tgt.carr Dn := by rw [← htarget]; exact hp
    have hsatT := tgtLins_sat Dn hD I htok X Y hpt
    have hmapT : ∀ c ∈ List.map (fun l => (l, false)) (tgtLins I), Sat c X Y := by
      intro c hc
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hc
      simpa [Sat] using hsatT l hl
    by_cases hY : Y < n.v.Y
    · exfalso
      rcases bsp_cover Dn hD cfg hcfg [] [] false n.t1 _ [] X Y F.r1 (by
          intro c hc
          rcases List.mem_append.mp hc with h | h
          · exact hmapT c h
          · simp only [List.mem_singleton] at h; subst h
            simpa [Sat] using (evalL_ylt n.v F.vw X Y).mpr hY) (by simp) (by simp) with
        ⟨t, ht, hm⟩ | ⟨h, _⟩
      · exact hnt t ht hm
      · simp at h
    · push_neg at hY
      have hyg : rp Dn X Y ∈ halfL Dn (ygeL n.v) := (mem_halfL_rp Dn hD _ X Y).mpr ((evalL_yge n.v F.vw X Y).mpr hY)
      refine ⟨⟨hpt, hyg⟩, ?_⟩
      by_cases hX : n.v.X ≤ X
      · exact Or.inl ((mem_halfL_rp Dn hD _ X Y).mpr ((evalL_xge n.v F.vw X Y).mpr hX))
      · push_neg at hX
        refine Or.inr ?_
        rcases bsp_cover Dn hD cfg hcfg (tgtLins I ++ [ygeL n.v]) [(yltL n.v, false), (xltL n.v, true)] true n.t2 _ [] X Y F.r2 (by
          intro c hc
          rcases List.mem_append.mp hc with h | h
          · exact hmapT c h
          · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
            rcases h with h | h
            · subst h; simpa [Sat] using (evalL_yge n.v F.vw X Y).mpr hY
            · subst h; simpa [Sat] using (evalL_xlt n.v F.vw X Y).mpr hX) (by simp) (by
              intro l hl
              rcases List.mem_append.mp hl with h | h
              · exact hsatT l h
              · simp only [List.mem_singleton] at h; subst h; exact (evalL_yge n.v F.vw X Y).mpr hY) with
          ⟨t, ht, hm⟩ | ⟨_, h⟩
        · exact absurd hm (hnt t ht)
        · exact h
  · -- v is least on C
    intro p hp
    obtain ⟨X, Y, rfl⟩ := exists_rp hD p
    obtain ⟨⟨hpt, hyg⟩, hx⟩ := hp
    have hY : n.v.Y ≤ Y := (evalL_yge n.v F.vw X Y).mp ((mem_halfL_rp Dn hD _ X Y).mp hyg)
    show LexLE (rp Dn n.v.X n.v.Y) (rp Dn X Y)
    refine lexLE_rp hD hY ?_
    intro hEq
    rcases hx with hx | hx
    · exact (evalL_xge n.v F.vw X Y).mp ((mem_halfL_rp Dn hD _ X Y).mp hx)
    · by_contra hlt
      push_neg at hlt
      refine cellSet_extra Dn hD cfg _ _ true n.t2 _ [] X Y F.r2 hx ?_
      intro e he
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
      rcases he with rfl | rfl
      · simpa [Sat] using (evalL_ylt' n.v F.vw X Y).mpr (by linarith)
      · simpa [Sat] using (evalL_xlt n.v F.vw X Y).mpr hlt


/-- **`hfree`**: the curve `t ↦ v + t(d + t√Dn d⊥)` stays in the unfilled region for `0 < t ≤ τ`. -/
theorem hfree_soundE (Dn : ℝ) (hD : 0 < Dn) (I : Inst) (hDn : (I.Dn : ℝ) = Dn)
    (htok : I.tgt.ok = true) (cfg : List _root_.Tri) (hcfg : ∀ t ∈ cfg, t.ok = true)
    (n : Node) (F : LocalFactsE I cfg n)
    {N : ℕ} (D : Erdos634.Geometry.CongruentDissection N)
    (htarget : D.target.carrier = I.tgt.carr Dn) (S : Finset (Fin N))
    (hSt : ∀ i ∈ S, ∃ t ∈ cfg, (D.tile i).carrier = t.carr Dn) :
    ∀ ε : ℝ, 0 < ε → ∃ t s : ℝ, 0 < t ∧ t < ε ∧ 0 < s ∧ s < ε ∧
      (n.v.re Dn) + t • ((n.d.re Dn) + s • perp (n.d.re Dn))
        ∈ unfilled D.toDissection S := by
  have hτ : (0:ℝ) < (n.tauN : ℝ) / n.tauD := by
    have a : (0:ℝ) < n.tauN := by exact_mod_cast F.tauN
    have b : (0:ℝ) < n.tauD := by exact_mod_cast F.tauD
    positivity
  refine hfree_of (Dn := Dn) (B := max 1 (sr Dn + 1)) hD (le_max_left _ _)
    (lt_of_lt_of_le (by linarith) (le_max_right _ _)) hτ _ _ _ ?_
  intro t ht0 htτ
  have hcurve := pt_ccw_rp Dn hD n.v.X n.v.Y n.d.X n.d.Y t
  show (rp Dn n.v.X n.v.Y) + t • ((rp Dn n.d.X n.d.Y) + (t * sr Dn) • perp (rp Dn n.d.X n.d.Y)) ∈ _
  rw [hcurve]
  set X := n.v.X + n.d.X * t - Dn * n.d.Y * t ^ 2
  set Y := n.v.Y + n.d.Y * t + n.d.X * t ^ 2
  rw [unfilled]
  refine ⟨?_, fun hU => ?_⟩
  · rw [htarget]
    refine Tri.mem_of_edges Dn hD I.tgt htok X Y ?_
    intro i hi
    have hall := List.all_eq_true.mp F.tgtQ (I.tgt.edge i)
      (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    exact okPos_sound I Dn hDn n.v n.d F.vw F.dw _ _ _ F.tauN F.tauD hall t ht0 htτ
  · obtain ⟨i, hi, hm⟩ := Set.mem_iUnion₂.mp hU
    obtain ⟨T, hT, hTc⟩ := hSt i hi
    rw [hTc] at hm
    obtain ⟨e, he⟩ := zip_all_ex _ cfg n.fedges F.flen F.tileQ T hT
    have hneg := okNeg_sound I Dn hDn n.v n.d F.vw F.dw _ _ _ F.tauN F.tauD he t ht0 htτ
    have hnn := Tri.edge_nonneg Dn hD T (hcfg T hT) X Y hm (e % 3) (Nat.mod_lt _ (by norm_num))
    rw [← Tri.edge_mod] at hnn
    linarith


#print axioms Refl.hlex_soundE
#print axioms Refl.hfree_soundE
end Refl

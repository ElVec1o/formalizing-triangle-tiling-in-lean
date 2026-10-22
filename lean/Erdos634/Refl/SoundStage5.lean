import Erdos634.Refl.SoundStage4

/-! Stage 5: `nodeLocalOk` unpacked, and `hlex_sound` (the lexicographic-least hypothesis of
    `placement_completeness`, from the two checked BSPs). -/

set_option linter.unusedSimpArgs false
open Erdos634.CertNode Erdos634.PlacementCompleteness
open Erdos634.Geometry (Plane)

namespace Refl

def tgtLins (I : Inst) : List Lin := (List.range 3).map (fun i => I.tgt.edge i)
def yltL (v : Pt) : Lin := ⟨0, -v.w, v.y⟩
def ygeL (v : Pt) : Lin := ⟨0, v.w, -v.y⟩
def xltL (v : Pt) : Lin := ⟨-v.w, 0, v.x⟩
def xgeL (v : Pt) : Lin := ⟨v.w, 0, -v.x⟩

/-- the unpacked content of `nodeLocalOk` -/
structure LocalFacts (I : Inst) (cfg : List _root_.Tri) (n : Node) : Prop where
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
  blk : blockedOk I cfg n.v n.d n.hb = true

theorem nodeLocalOk_facts (I : Inst) (cfg : List _root_.Tri) (n : Node)
    (h : nodeLocalOk I cfg n = true) : LocalFacts I cfg n := by
  unfold nodeLocalOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩


/-! ### line evaluations at the node vertex -/

theorem evalL_ylt (v : Pt) (hw : 0 < v.w) (X Y : ℝ) :
    0 < evalL (yltL v) X Y ↔ Y < v.Y := by
  have h := Pt.w_pos v hw
  unfold evalL yltL Pt.Y
  rw [lt_div_iff₀ h]; push_cast; constructor <;> intro <;> nlinarith
theorem evalL_ylt' (v : Pt) (hw : 0 < v.w) (X Y : ℝ) :
    0 ≤ evalL (yltL v) X Y ↔ Y ≤ v.Y := by
  have h := Pt.w_pos v hw
  unfold evalL yltL Pt.Y
  rw [le_div_iff₀ h]; push_cast; constructor <;> intro <;> nlinarith
theorem evalL_yge (v : Pt) (hw : 0 < v.w) (X Y : ℝ) :
    0 ≤ evalL (ygeL v) X Y ↔ v.Y ≤ Y := by
  have h := Pt.w_pos v hw
  unfold evalL ygeL Pt.Y
  rw [div_le_iff₀ h]; push_cast; constructor <;> intro <;> nlinarith
theorem evalL_xlt (v : Pt) (hw : 0 < v.w) (X Y : ℝ) :
    0 < evalL (xltL v) X Y ↔ X < v.X := by
  have h := Pt.w_pos v hw
  unfold evalL xltL Pt.X
  rw [lt_div_iff₀ h]; push_cast; constructor <;> intro <;> nlinarith
theorem evalL_xge (v : Pt) (hw : 0 < v.w) (X Y : ℝ) :
    0 ≤ evalL (xgeL v) X Y ↔ v.X ≤ X := by
  have h := Pt.w_pos v hw
  unfold evalL xgeL Pt.X
  rw [div_le_iff₀ h]; push_cast; constructor <;> intro <;> nlinarith

theorem tgtLins_sat (Dn : ℝ) (hD : 0 < Dn) (I : Inst) (htok : I.tgt.ok = true) (X Y : ℝ)
    (h : rp Dn X Y ∈ I.tgt.carr Dn) : ∀ l ∈ tgtLins I, 0 ≤ evalL l X Y := by
  intro l hl
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
  exact Tri.edge_nonneg Dn hD I.tgt htok X Y h i (List.mem_range.mp hi)

theorem tri_carr_closed (Dn : ℝ) (hD : 0 < Dn) (t : _root_.Tri) (ht : t.ok = true) :
    IsClosed (t.carr Dn) := by
  obtain ⟨hp, hc⟩ := Tri.ok_sem Dn hD t ht
  rw [hc]; exact (rtri Dn hD _ _ _ _ _ _ hp).isCompact.isClosed

/-- **`hlex`**: the two checked BSPs give a closed superset of the unfilled region on which `v` is
lexicographically least. -/
theorem hlex_sound (Dn : ℝ) (hD : 0 < Dn) (I : Inst) (htok : I.tgt.ok = true)
    (cfg : List _root_.Tri) (hcfg : ∀ t ∈ cfg, t.ok = true) (n : Node) (F : LocalFacts I cfg n)
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

#print axioms Refl.hlex_sound
end Refl

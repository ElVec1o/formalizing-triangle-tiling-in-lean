import Erdos634.Refl.SoundStage1

/-! Stage 2: `bsp_sound` — a checked binary space partition covers by tiles or cells. -/

set_option linter.unusedSimpArgs false
open Erdos634.CertNode
open Erdos634.Geometry (Plane)

namespace Refl

theorem evalL_neg (l : Lin) (X Y : ℝ) : evalL l.neg X Y = -evalL l X Y := by
  simp only [evalL, Lin.neg]; push_cast; ring

/-- three nonneg edge lines put the point in the triangle -/
theorem Tri.mem_of_edges (Dn : ℝ) (hD : 0 < Dn) (t : _root_.Tri) (ht : t.ok = true) (X Y : ℝ)
    (h : ∀ i, i < 3 → 0 ≤ evalL (t.edge i) X Y) : rp Dn X Y ∈ t.carr Dn := by
  have ht' := ht
  simp only [_root_.Tri.ok, Bool.and_eq_true, decide_eq_true_eq] at ht'
  obtain ⟨⟨⟨ha, hb⟩, hc⟩, -⟩ := ht'
  obtain ⟨hpos, hcar⟩ := Tri.ok_sem Dn hD t ht
  rw [hcar]
  have wa := Pt.w_pos _ ha
  have wb := Pt.w_pos _ hb
  have wc := Pt.w_pos _ hc
  have h0 := h 0 (by norm_num)
  have h1 := h 1 (by norm_num)
  have h2 := h 2 (by norm_num)
  simp only [_root_.Tri.edge, _root_.Tri.vert, Nat.reduceMod, Nat.reduceAdd] at h0 h1 h2
  rw [evalL_linOf _ _ (Pt.w_ne _ ha) (Pt.w_ne _ hb)] at h0
  rw [evalL_linOf _ _ (Pt.w_ne _ hb) (Pt.w_ne _ hc)] at h1
  rw [evalL_linOf _ _ (Pt.w_ne _ hc) (Pt.w_ne _ ha)] at h2
  exact mem_rtri hD hpos ((mul_nonneg_iff_of_pos_left (mul_pos wa wb)).mp h0)
    ((mul_nonneg_iff_of_pos_left (mul_pos wb wc)).mp h1)
    ((mul_nonneg_iff_of_pos_left (mul_pos wc wa)).mp h2)

theorem bsp_sound (Dn : ℝ) (hD : 0 < Dn) (cfg : List _root_.Tri) (hcfg : ∀ t ∈ cfg, t.ok = true)
    (closedBase : List Lin) (extra : List (Lin × Bool)) (allowCell : Bool) :
    ∀ (b : Bsp) (cons : List (Lin × Bool)) (path : List Lin) (X Y : ℝ),
      Bsp.check cfg closedBase extra allowCell cons path b = true →
      (∀ c ∈ cons, Sat c X Y) → (∀ l ∈ path, 0 ≤ evalL l X Y) →
      (∃ t ∈ cfg, rp Dn X Y ∈ t.carr Dn) ∨
      (allowCell = true ∧ ((∀ l ∈ closedBase, 0 ≤ evalL l X Y) → ¬ ∀ e ∈ extra, Sat e X Y)) := by
  intro b
  induction b with
  | inf ms =>
    intro cons path X Y hk hs _
    exact (farkas_sound X Y cons ms hs (by simpa [Bsp.check] using hk)).elim
  | tile m f0 f1 f2 =>
    intro cons path X Y hk hs _
    simp only [Bsp.check] at hk
    cases hm : cfg[m]? with
    | none => rw [hm] at hk; simp at hk
    | some t =>
      rw [hm] at hk
      simp only [Bool.and_eq_true] at hk
      obtain ⟨⟨k0, k1⟩, k2⟩ := hk
      have htm : t ∈ cfg := List.mem_of_getElem? hm
      left
      refine ⟨t, htm, Tri.mem_of_edges Dn hD t (hcfg t htm) X Y ?_⟩
      have key : ∀ (i : Nat) (fs : List Nat),
          farkas (cons ++ [((t.edge i).neg, true)]) fs = true → 0 ≤ evalL (t.edge i) X Y := by
        intro i fs hf
        by_contra hneg
        push_neg at hneg
        refine farkas_sound X Y _ fs ?_ hf
        intro c hc
        rcases List.mem_append.mp hc with hc | hc
        · exact hs c hc
        · simp only [List.mem_singleton] at hc
          subst hc
          simp only [Sat, if_true, evalL_neg]
          linarith
      intro i hi
      interval_cases i
      · exact key 0 f0 k0
      · exact key 1 f1 k1
      · exact key 2 f2 k2
  | cell ms =>
    intro cons path X Y hk hs hp
    simp only [Bsp.check, Bool.and_eq_true] at hk
    obtain ⟨hall, hf⟩ := hk
    right
    refine ⟨hall, fun hcb hextra => ?_⟩
    refine farkas_sound X Y _ ms ?_ hf
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hc
      simp only [Sat, Bool.false_eq_true, if_false]
      rcases List.mem_append.mp hl with hl | hl
      · exact hcb l hl
      · exact hp l hl
    · exact hextra c hc
  | split m i l r ihl ihr =>
    intro cons path X Y hk hs hp
    simp only [Bsp.check] at hk
    cases hm : cfg[m]? with
    | none => rw [hm] at hk; simp at hk
    | some t =>
      rw [hm] at hk
      simp only [Bool.and_eq_true] at hk
      obtain ⟨kl, kr⟩ := hk
      by_cases hc : 0 ≤ evalL (t.edge i) X Y
      · refine ihl _ _ X Y kl ?_ ?_
        · intro c hc'
          rcases List.mem_append.mp hc' with h | h
          · exact hs c h
          · simp only [List.mem_singleton] at h; subst h; simpa [Sat] using hc
        · intro l' hl'
          rcases List.mem_append.mp hl' with h | h
          · exact hp l' h
          · simp only [List.mem_singleton] at h; subst h; exact hc
      · push_neg at hc
        refine ihr _ _ X Y kr ?_ ?_
        · intro c hc'
          rcases List.mem_append.mp hc' with h | h
          · exact hs c h
          · simp only [List.mem_singleton] at h; subst h
            simp only [Sat, if_true, evalL_neg]; linarith
        · intro l' hl'
          rcases List.mem_append.mp hl' with h | h
          · exact hp l' h
          · simp only [List.mem_singleton] at h; subst h
            rw [evalL_neg]; linarith

#print axioms Refl.bsp_sound
end Refl

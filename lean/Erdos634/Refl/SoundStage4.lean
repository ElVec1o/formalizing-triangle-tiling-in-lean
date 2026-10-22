import Erdos634.Refl.SoundStage3

/-! Stage 4a: closed cell sets of a BSP, and the coverage form of `bsp_sound` that names them.
    Stage 4b: `hlex_sound`. -/

set_option linter.unusedSimpArgs false
open Erdos634.CertNode Erdos634.PlacementCompleteness
open Erdos634.Geometry (Plane)

namespace Refl

def halfL (Dn : ℝ) (l : Lin) : Set Plane := halfR Dn l.α l.β l.γ

theorem mem_halfL_rp (Dn : ℝ) (hD : 0 < Dn) (l : Lin) (X Y : ℝ) :
    rp Dn X Y ∈ halfL Dn l ↔ 0 ≤ evalL l X Y := by
  unfold halfL evalL; exact mem_halfR_rp hD _ _ _ _ _

/-- the union of the closed cells of a BSP (path lines nonstrict, plus `cb`) -/
def cellSet (Dn : ℝ) (cfg : List _root_.Tri) (cb : List Lin) : Bsp → List Lin → Set Plane
  | .inf _, _ => ∅
  | .tile _ _ _ _, _ => ∅
  | .cell _, path => ⋂ l ∈ (cb ++ path), halfL Dn l
  | .split m i l r, path =>
    match cfg[m]? with
    | none => ∅
    | some t => cellSet Dn cfg cb l (path ++ [t.edge i]) ∪ cellSet Dn cfg cb r (path ++ [(t.edge i).neg])

theorem cellSet_closed (Dn : ℝ) (cfg : List _root_.Tri) (cb : List Lin) :
    ∀ (b : Bsp) (path : List Lin), IsClosed (cellSet Dn cfg cb b path) := by
  intro b
  induction b with
  | inf ms => intro path; simp [cellSet]
  | tile m f0 f1 f2 => intro path; simp [cellSet]
  | cell ms =>
    intro path
    simp only [cellSet]
    exact isClosed_iInter fun l => isClosed_iInter fun _ => isClosed_halfR _ _ _ _
  | split m i l r ihl ihr =>
    intro path
    simp only [cellSet]
    cases cfg[m]? with
    | none => simp
    | some t => exact (ihl _).union (ihr _)

/-- coverage with named cells: a point in the closed base and on the path lines is in a tile, or in `cellSet` -/
theorem bsp_cover (Dn : ℝ) (hD : 0 < Dn) (cfg : List _root_.Tri) (hcfg : ∀ t ∈ cfg, t.ok = true)
    (cb : List Lin) (extra : List (Lin × Bool)) (allowCell : Bool) :
    ∀ (b : Bsp) (cons : List (Lin × Bool)) (path : List Lin) (X Y : ℝ),
      Bsp.check cfg cb extra allowCell cons path b = true →
      (∀ c ∈ cons, Sat c X Y) → (∀ l ∈ path, 0 ≤ evalL l X Y) → (∀ l ∈ cb, 0 ≤ evalL l X Y) →
      (∃ t ∈ cfg, rp Dn X Y ∈ t.carr Dn) ∨
      (allowCell = true ∧ rp Dn X Y ∈ cellSet Dn cfg cb b path) := by
  intro b
  induction b with
  | inf ms =>
    intro cons path X Y hk hs _ _
    exact (farkas_sound X Y cons ms hs (by simpa [Bsp.check] using hk)).elim
  | tile m f0 f1 f2 =>
    intro cons path X Y hk hs hp hcb
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
    intro cons path X Y hk hs hp hcb
    simp only [Bsp.check, Bool.and_eq_true] at hk
    right
    refine ⟨hk.1, ?_⟩
    simp only [cellSet, Set.mem_iInter]
    intro l hl
    rw [mem_halfL_rp Dn hD]
    rcases List.mem_append.mp hl with h | h
    · exact hcb l h
    · exact hp l h
  | split m i l r ihl ihr =>
    intro cons path X Y hk hs hp hcb
    simp only [Bsp.check] at hk
    cases hm : cfg[m]? with
    | none => rw [hm] at hk; simp at hk
    | some t =>
      rw [hm] at hk
      simp only [Bool.and_eq_true] at hk
      obtain ⟨kl, kr⟩ := hk
      by_cases hc : 0 ≤ evalL (t.edge i) X Y
      · have := ihl _ _ X Y kl (by
          intro c hc'
          rcases List.mem_append.mp hc' with h | h
          · exact hs c h
          · simp only [List.mem_singleton] at h; subst h; simpa [Sat] using hc) (by
          intro l' hl'
          rcases List.mem_append.mp hl' with h | h
          · exact hp l' h
          · simp only [List.mem_singleton] at h; subst h; exact hc) hcb
        rcases this with h | ⟨h1, h2⟩
        · exact Or.inl h
        · right; refine ⟨h1, ?_⟩; simp only [cellSet, hm]; exact Or.inl h2
      · push_neg at hc
        have := ihr _ _ X Y kr (by
          intro c hc'
          rcases List.mem_append.mp hc' with h | h
          · exact hs c h
          · simp only [List.mem_singleton] at h; subst h
            simp only [Sat, if_true, evalL_neg]; linarith) (by
          intro l' hl'
          rcases List.mem_append.mp hl' with h | h
          · exact hp l' h
          · simp only [List.mem_singleton] at h; subst h
            rw [evalL_neg]; linarith) hcb
        rcases this with h | ⟨h1, h2⟩
        · exact Or.inl h
        · right; refine ⟨h1, ?_⟩; simp only [cellSet, hm]; exact Or.inr h2

/-- at a checked cell leaf, the closed cell misses the `extra` region -/
theorem cellSet_extra (Dn : ℝ) (hD : 0 < Dn) (cfg : List _root_.Tri) (cb : List Lin)
    (extra : List (Lin × Bool)) (allowCell : Bool) :
    ∀ (b : Bsp) (cons : List (Lin × Bool)) (path : List Lin) (X Y : ℝ),
      Bsp.check cfg cb extra allowCell cons path b = true →
      rp Dn X Y ∈ cellSet Dn cfg cb b path → ¬ ∀ e ∈ extra, Sat e X Y := by
  intro b
  induction b with
  | inf ms => intro cons path X Y _ h; simp [cellSet] at h
  | tile m f0 f1 f2 => intro cons path X Y _ h; simp [cellSet] at h
  | cell ms =>
    intro cons path X Y hk hm hextra
    simp only [Bsp.check, Bool.and_eq_true] at hk
    simp only [cellSet, Set.mem_iInter] at hm
    refine farkas_sound X Y _ ms ?_ hk.2
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hc
      simp only [Sat, Bool.false_eq_true, if_false]
      exact (mem_halfL_rp Dn hD l X Y).mp (hm l hl)
    · exact hextra c hc
  | split m i l r ihl ihr =>
    intro cons path X Y hk hm
    simp only [Bsp.check] at hk
    simp only [cellSet] at hm
    cases hc : cfg[m]? with
    | none => rw [hc] at hk; simp at hk
    | some t =>
      rw [hc] at hk hm
      simp only [Bool.and_eq_true] at hk
      rcases hm with hm | hm
      · exact ihl _ _ X Y hk.1 hm
      · exact ihr _ _ X Y hk.2 hm

#print axioms Refl.bsp_cover
#print axioms Refl.cellSet_closed
#print axioms Refl.cellSet_extra
end Refl

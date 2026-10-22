-- Draft/LaczFormalIVcRatB8b.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, rational branch), BLUEPRINT Part B, item B8 (P5, the complement of the row), stage b.
--   `piece_above`: a piece Q (closure of its interior) inside the strip {0 <= fa <= k, fb >= 0} whose interior misses the interiors of the row rhombi Par (X + i p) p q (i < k) lies in {fb >= 1}.
--   `VWTiling.complement_row`: T a VWTiling of a convex A inside the quadrant of F, with the row R_0, ..., R_j (rhombi Par (X + i p) p q, i <= j) ending at X + (j+1) p, and a point of A with fb > 1:
--   there is a nonempty Finset S of rhombus indices (the row) such that the union of the remaining pieces (the region of `T.restrict S`) equals A intersected with {fb >= 1}, a CONVEX set.
--   (blueprint P5: "A \ P is convex"; stated with the closed half plane, the region of the restriction.)
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcRatB8a

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

theorem rowPar_fb_le {b : ℝ} (F : Frame b) (hb : 0 < b) (i : ℕ) : ∀ z ∈ VWTiling.rowPar F i, 0 ≤ F.fb z ∧ F.fb z ≤ 1 := by
  rintro z ⟨l, m, hl, hl1, hm, hm1, e0, e1⟩
  have := (F.fa_fb_of hb (y := z) (a := (i : ℝ) + l) (β := m) (by rw [e0]; ring) (by rw [e1]; ring)).2
  rw [this]; exact ⟨hm, hm1⟩

theorem rowPar_fa_range {b : ℝ} (F : Frame b) (hb : 0 < b) (i : ℕ) : ∀ z ∈ VWTiling.rowPar F i, (i : ℝ) ≤ F.fa z ∧ F.fa z ≤ i + 1 := by
  rintro z ⟨l, m, hl, hl1, hm, hm1, e0, e1⟩
  have := (F.fa_fb_of hb (y := z) (a := (i : ℝ) + l) (β := m) (by rw [e0]; ring) (by rw [e1]; ring)).1
  rw [this]; constructor <;> linarith

/-- **B8b (piece above the row).** -/
theorem piece_above {b : ℝ} (F : Frame b) (hb : 0 < b) (k : ℕ) {Q : Set Plane}
    (hQbox : ∀ y ∈ Q, 0 ≤ F.fa y ∧ F.fa y ≤ k ∧ 0 ≤ F.fb y)
    (hcl : Q ⊆ closure (interior Q))
    (hdis : ∀ i : ℕ, i < k → Disjoint (interior Q) (interior (VWTiling.rowPar F i))) :
    ∀ z ∈ Q, 1 ≤ F.fb z := by
  intro z hz
  by_contra hlt
  push Not at hlt
  have hopen : IsOpen {y | F.fb y < 1} := isOpen_lt F.continuous_fb continuous_const
  obtain ⟨w, hwV, hwQ⟩ := mem_closure_iff.mp (hcl hz) _ hopen hlt
  have hwV' : F.fb w < 1 := hwV
  obtain ⟨δ, hδ, hnb⟩ := exists_nhd_shift F hb (S := interior Q) (w := w) (by rw [interior_interior]; exact hwQ)
  have hfbpos : 0 < F.fb w := by
    have := (hQbox _ (interior_subset (hnb (-δ) (by rw [abs_neg, abs_of_pos hδ])).2)).2.2
    rw [F.fb_pt hb] at this; linarith
  set a := F.fa w with ha
  set δ' := min δ 1 with hδ'
  have hδ'p : 0 < δ' := lt_min hδ one_pos
  have hδ'le : δ' ≤ δ := min_le_left _ _
  have hδ'1 : δ' ≤ 1 := min_le_right _ _
  -- a shift s with a + s not an integer
  have hex : ∃ s : ℝ, 0 < s ∧ s ≤ δ ∧ ∀ n : ℤ, (n : ℝ) ≠ a + s := by
    by_cases h1 : ∃ n : ℤ, (n : ℝ) = a + δ' / 2
    · refine ⟨δ' / 3, by positivity, by linarith, fun n' hn' => ?_⟩
      obtain ⟨n, hn⟩ := h1
      have h2 : (n : ℝ) - n' = δ' / 6 := by linarith
      have h3 : (0 : ℝ) < (n : ℝ) - n' := by rw [h2]; positivity
      have h4 : (n : ℝ) - n' < 1 := by rw [h2]; linarith
      have h5 : (0 : ℤ) < n - n' := by exact_mod_cast h3
      have h6 : n - n' < 1 := by exact_mod_cast h4
      omega
    · exact ⟨δ' / 2, by positivity, by linarith, fun n hn => h1 ⟨n, hn⟩⟩
  obtain ⟨s, hs0, hsδ, hsn⟩ := hex
  have hw' : F.pt (a + s) (F.fb w) ∈ interior Q := (hnb s (by rw [abs_of_pos hs0]; exact hsδ)).1
  have hbox := hQbox _ (interior_subset hw')
  rw [F.fa_pt hb, F.fb_pt hb] at hbox
  have hne0 : a + s ≠ 0 := fun h => hsn 0 (by simpa using h.symm)
  have hnek : a + s ≠ k := fun h => hsn k (by simpa using h.symm)
  have hlt0 : 0 < a + s := lt_of_le_of_ne hbox.1 (Ne.symm hne0)
  have hltk : a + s < k := lt_of_le_of_ne hbox.2.1 hnek
  set i := ⌊a + s⌋₊ with hi
  have hik : i < k := (Nat.floor_lt hlt0.le).mpr hltk
  have hfl1 : (i : ℝ) ≤ a + s := Nat.floor_le hlt0.le
  have hfl2 : a + s < (i : ℝ) + 1 := Nat.lt_floor_add_one _
  have hfl3 : (i : ℝ) < a + s := by
    refine lt_of_le_of_ne hfl1 (fun h => ?_)
    exact hsn i (by exact_mod_cast h)
  -- w' is in the interior of the row rhombus i
  have hWopen : IsOpen {y | (i : ℝ) < F.fa y ∧ F.fa y < i + 1 ∧ 0 < F.fb y ∧ F.fb y < 1} := by
    have ha := F.continuous_fa
    have hb' := F.continuous_fb
    have : {y | (i : ℝ) < F.fa y ∧ F.fa y < i + 1 ∧ 0 < F.fb y ∧ F.fb y < 1} =
        {y | (i : ℝ) < F.fa y} ∩ ({y | F.fa y < i + 1} ∩ ({y | 0 < F.fb y} ∩ {y | F.fb y < 1})) := by ext y; simp
    rw [this]
    exact (isOpen_lt continuous_const ha).inter ((isOpen_lt ha continuous_const).inter
      ((isOpen_lt continuous_const hb').inter (isOpen_lt hb' continuous_const)))
  have hWsub : {y | (i : ℝ) < F.fa y ∧ F.fa y < i + 1 ∧ 0 < F.fb y ∧ F.fb y < 1} ⊆ VWTiling.rowPar F i := by
    intro y ⟨h1, h2, h3, h4⟩
    have := F.recon hb y
    refine ⟨F.fa y - i, F.fb y, by linarith, by linarith, by linarith, by linarith, ?_, ?_⟩
    · have h := congrArg (fun y : Plane => y 0) this
      simp only [F.pt_zero] at h; rw [h]; ring
    · have h := congrArg (fun y : Plane => y 1) this
      simp only [F.pt_one] at h; rw [h]; ring
  have hmemW : F.pt (a + s) (F.fb w) ∈ {y | (i : ℝ) < F.fa y ∧ F.fa y < i + 1 ∧ 0 < F.fb y ∧ F.fb y < 1} := by
    show (i : ℝ) < F.fa _ ∧ F.fa _ < i + 1 ∧ 0 < F.fb _ ∧ F.fb _ < 1
    rw [F.fa_pt hb, F.fb_pt hb]
    exact ⟨hfl3, hfl2, hfbpos, hwV'⟩
  exact Set.disjoint_left.mp (hdis i hik) hw' (interior_maximal hWsub hWopen hmemW)

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.piece_above

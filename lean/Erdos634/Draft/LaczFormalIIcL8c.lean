-- Draft/LaczFormalIIcL8c.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, index split (G10), step 3: PURE PLANE GEOMETRY.
-- `path_cross`: for points A, C, E and a path B -> F -> D with B strictly on the E side of the line AC and D strictly on the other side, E on the closed B side, such that the path meets the line AC only
-- in the chord AC and `B` lies in the triangle AEC only if B = E, the path meets the polyline A -> E -> C.   (two-segment version of "a path crossing a chord of a convex polygon meets any bent chord".)
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcL8b

open Erdos634.Geometry Erdos634.Draft.LaczFormal.Thm21

namespace Erdos634.Draft.LaczFormal.RG

/-- signed distance (up to scale) from the line `AC`. -/
def gl (A C X : Plane) : ℝ := cross2 (C - A) (X - A)

theorem gl_comb (A C S R : Plane) (t : ℝ) : gl A C ((1 - t) • S + t • R) = (1 - t) * gl A C S + t * gl A C R := by
  unfold gl cross2; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

theorem tlE_eq (A C X : Plane) : tlE A C X = - gl A C X := by
  unfold tlE gl cross2; simp only [PiLp.sub_apply]; ring

theorem delta_eq (A E C : Plane) : cross2 (E - A) (C - A) = - gl A C E := by
  unfold gl cross2; ring

/-- a point of a chord `AC` lies on one of the two halves cut by a point `E` of the chord. -/
theorem seg_split {A C E Q : Plane} (hE : E ∈ segment ℝ A C) (hQ : Q ∈ segment ℝ A C) : Q ∈ segment ℝ A E ∨ Q ∈ segment ℝ E C := by
  obtain ⟨a1, e, ha1, he, hsum1, rfl⟩ := hE
  obtain ⟨a2, u, ha2, hu, hsum2, rfl⟩ := hQ
  have e1 : a1 = 1 - e := by linarith
  have e2 : a2 = 1 - u := by linarith
  subst e1 e2
  rcases le_total u e with h | h
  · left
    by_cases he0 : e = 0
    · have : u = 0 := by linarith
      subst he0; subst this; simp [left_mem_segment]
    · have hepos : 0 < e := lt_of_le_of_ne he (Ne.symm he0)
      refine ⟨1 - u / e, u / e, by rw [sub_nonneg, div_le_one hepos]; exact h, div_nonneg hu he, by ring, ?_⟩
      apply pl_ext
      · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; field_simp; ring
      · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; field_simp; ring
  · right
    have he1 : e < 1 ∨ e = 1 := lt_or_eq_of_le (by linarith)
    rcases he1 with he1 | he1
    · have hpos : 0 < 1 - e := by linarith
      refine ⟨1 - (u - e) / (1 - e), (u - e) / (1 - e), by rw [sub_nonneg, div_le_one hpos]; linarith, div_nonneg (by linarith) hpos.le, by ring, ?_⟩
      apply pl_ext
      · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; field_simp; ring
      · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; field_simp; ring
    · have : u = 1 := by linarith
      subst he1; subst this; simp [right_mem_segment]

/-- crossing point of a segment `S -> R` with `g S < 0 <= g R` with the line `g = 0`. -/
theorem seg_cross_line {A C S R : Plane} (hS : gl A C S < 0) (hR : 0 ≤ gl A C R) :
    ∃ Q ∈ segment ℝ S R, gl A C Q = 0 := by
  obtain ⟨a0, a1, a2⟩ := aroot_facts hS hR
  refine ⟨(1 - aroot (gl A C S) (gl A C R)) • S + aroot (gl A C S) (gl A C R) • R, ⟨_, _, by linarith, a0, by ring, rfl⟩, ?_⟩
  rw [gl_comb]; exact a2

theorem in_tri_of_chord {A E C Q : Plane} (hΔ : 0 < cross2 (E - A) (C - A)) (hQ : Q ∈ segment ℝ A C) :
    0 ≤ tlA E C Q ∧ 0 ≤ tlE A C Q ∧ 0 ≤ tlC A E Q := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hQ
  have e : a = 1 - b := by linarith
  subst e
  refine ⟨?_, ?_, ?_⟩
  · rw [tlA_comb]
    have h1 : tlA E C A = cross2 (E - A) (C - A) := rfl
    have h2 : tlA E C C = 0 := by unfold tlA cross2; simp
    rw [h1, h2]; nlinarith
  · rw [tlE_comb]
    have h1 : tlE A C A = 0 := by unfold tlE cross2; simp
    have h2 : tlE A C C = 0 := by unfold tlE cross2; simp
    rw [h1, h2]; simp
  · rw [tlC_comb]
    have h1 : tlC A E A = 0 := by unfold tlC cross2; simp
    have h2 : tlC A E C = cross2 (E - A) (C - A) := by unfold tlC cross2; simp only [PiLp.sub_apply]; ring
    rw [h1, h2]; nlinarith

/-- **Two-segment crossing lemma.** -/
theorem path_cross {A C E B F D : Plane}
    (hB : gl A C B < 0) (hD : 0 < gl A C D) (hE : gl A C E ≤ 0)
    (hchord : ∀ X, (X ∈ segment ℝ B F ∨ X ∈ segment ℝ F D) → gl A C X = 0 → X ∈ segment ℝ A C)
    (hchordE : gl A C E = 0 → E ∈ segment ℝ A C)
    (hBT : (0 ≤ tlA E C B ∧ 0 ≤ tlE A C B ∧ 0 ≤ tlC A E B) → B = E) :
    ∃ X, (X ∈ segment ℝ B F ∨ X ∈ segment ℝ F D) ∧ (X ∈ segment ℝ A E ∨ X ∈ segment ℝ E C) := by
  -- a crossing point of the path with the line AC
  have hcross : ∃ Q, ((Q ∈ segment ℝ B F ∧ 0 ≤ gl A C F) ∨ (Q ∈ segment ℝ F D ∧ gl A C F < 0)) ∧ gl A C Q = 0 := by
    by_cases hF : 0 ≤ gl A C F
    · obtain ⟨Q, hQ, hQ0⟩ := seg_cross_line hB hF
      exact ⟨Q, Or.inl ⟨hQ, hF⟩, hQ0⟩
    · push_neg at hF
      obtain ⟨Q, hQ, hQ0⟩ := seg_cross_line hF hD.le
      exact ⟨Q, Or.inr ⟨hQ, hF⟩, hQ0⟩
  by_cases hdeg : gl A C E = 0
  · have hEs := hchordE hdeg
    obtain ⟨Q, hQ, hQ0⟩ := hcross
    have hQp : Q ∈ segment ℝ B F ∨ Q ∈ segment ℝ F D := by rcases hQ with ⟨h, -⟩ | ⟨h, -⟩ <;> tauto
    exact ⟨Q, hQp, seg_split hEs (hchord Q hQp hQ0)⟩
  · have hEneg : gl A C E < 0 := lt_of_le_of_ne hE hdeg
    have hΔ : 0 < cross2 (E - A) (C - A) := by rw [delta_eq]; linarith
    by_cases hBs : tlA E C B < 0 ∨ tlC A E B < 0
    · have hBE : 0 < tlE A C B := by rw [tlE_eq]; linarith
      obtain ⟨Q, hQ, hQ0⟩ := hcross
      have hQp : Q ∈ segment ℝ B F ∨ Q ∈ segment ℝ F D := by rcases hQ with ⟨h, -⟩ | ⟨h, -⟩ <;> tauto
      have hQT := in_tri_of_chord (E := E) hΔ (hchord Q hQp hQ0)
      rcases hQ with ⟨hQ, hF⟩ | ⟨hQ, hF⟩
      · obtain ⟨X, hX, hX'⟩ := seg_enter hΔ hBE hBs hQT.1 hQT.2.1 hQT.2.2
        exact ⟨X, Or.inl ((convex_segment B F).segment_subset (left_mem_segment ℝ B F) hQ hX), hX'⟩
      · by_cases hFT : 0 ≤ tlA E C F ∧ 0 ≤ tlE A C F ∧ 0 ≤ tlC A E F
        · obtain ⟨X, hX, hX'⟩ := seg_enter hΔ hBE hBs hFT.1 hFT.2.1 hFT.2.2
          exact ⟨X, Or.inl hX, hX'⟩
        · have hFE : 0 < tlE A C F := by rw [tlE_eq]; linarith
          have hFs : tlA E C F < 0 ∨ tlC A E F < 0 := by
            by_contra hc; push_neg at hc; exact hFT ⟨hc.1, hFE.le, hc.2⟩
          obtain ⟨X, hX, hX'⟩ := seg_enter hΔ hFE hFs hQT.1 hQT.2.1 hQT.2.2
          exact ⟨X, Or.inr ((convex_segment F D).segment_subset (left_mem_segment ℝ F D) hQ hX), hX'⟩
    · push_neg at hBs
      have hBE : 0 < tlE A C B := by rw [tlE_eq]; linarith
      have := hBT ⟨hBs.1, hBE.le, hBs.2⟩
      exact ⟨B, Or.inl (left_mem_segment ℝ B F), Or.inl (by rw [this]; exact right_mem_segment ℝ A E)⟩

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.path_cross

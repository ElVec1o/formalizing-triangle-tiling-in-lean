-- Draft/LaczFormalIIcL8f.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, index split (G10), step 6: `no_interleave` and `spokes_interval` (see L8e header).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcL8e

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.Draft.LaczFormal.Thm21

namespace Erdos634.Draft.LaczFormal.RG

variable {M : ℕ} [NeZero M]

theorem cast_ne_of_lt {b c : ℕ} (hbc : b < c) (hc : c < M) : ((b : ℕ) : Fin M) ≠ ((c : ℕ) : Fin M) := by
  intro h
  have := congrArg Fin.val h
  rw [Fin.val_natCast, Fin.val_natCast, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hc] at this
  omega

theorem add_cast_ne {s : Fin M} {b c : ℕ} (hbc : b < c) (hc : c < M) : s + (b : Fin M) ≠ s + (c : Fin M) := by
  intro h; exact cast_ne_of_lt hbc hc (add_left_cancel h)

theorem add_cast_ne_self {s : Fin M} {c : ℕ} (h0 : 0 < c) (hc : c < M) : s + (c : Fin M) ≠ s := by
  intro h; apply natCast_ne_zero_fin h0 hc; simpa using h

/-- **Interleaving lemma.** -/
theorem no_interleave (P : ConvPoly M) (s : Fin M) {b c d : ℕ} (hb : 0 < b) (hbc : b < c) (hcd : c < d) (hd : d < M) {E F : Plane}
    (hE : E ∈ P.carrier) (hF : F ∈ P.carrier)
    (hdis : ∀ i l : Fin M, (i = s ∨ i = s + (c : Fin M)) → (l = s + (b : Fin M) ∨ l = s + (d : Fin M)) →
      ∀ X, X ∈ segment ℝ (P.v i) E → X ∈ segment ℝ (P.v l) F → False) : False := by
  set A := P.v s with hA
  set B := P.v (s + (b : Fin M)) with hBd
  set C := P.v (s + (c : Fin M)) with hCd
  set D := P.v (s + (d : Fin M)) with hDd
  have oB := poly_orient P s b c hb hbc (by omega)
  have oD := poly_orient P s c d (by omega) hcd hd
  have hgB : gl A C B < 0 := by
    unfold gl; rw [cross2_neg_swap]; linarith
  have hgD : 0 < gl A C D := oD
  have hsc : s ≠ s + (c : Fin M) := (add_cast_ne_self (s := s) (by omega) (by omega)).symm
  have hBF : segment ℝ B F ⊆ P.carrier := carrier_segment P (vtx_mem' P _) hF
  have hFD : segment ℝ F D ⊆ P.carrier := carrier_segment P hF (vtx_mem' P _)
  have hchord : ∀ X, (X ∈ segment ℝ B F ∨ X ∈ segment ℝ F D) → gl A C X = 0 → X ∈ segment ℝ A C := by
    intro X hX h0
    have : X ∈ P.carrier := by rcases hX with h | h; exact hBF h; exact hFD h
    exact chord_in_segment P hsc this h0
  have hchordE : gl A C E = 0 → E ∈ segment ℝ A C := fun h0 => chord_in_segment P hsc hE h0
  rcases le_total (gl A C E) 0 with hEg | hEg
  · have hBT := vertex_tri_eq P (a := s) (j := s + (b : Fin M)) (c := s + (c : Fin M)) (add_cast_ne_self hb (by omega)) (add_cast_ne hbc (by omega)) hE hgB hEg
    obtain ⟨X, hX1, hX2⟩ := path_cross hgB hgD hEg hchord hchordE (by simpa [hBd, hA, hCd] using hBT)
    rcases hX1 with h1 | h1 <;> rcases hX2 with h2 | h2
    · exact hdis s (s + (b : Fin M)) (Or.inl rfl) (Or.inl rfl) X h2 h1
    · exact hdis (s + (c : Fin M)) (s + (b : Fin M)) (Or.inr rfl) (Or.inl rfl) X (segment_symm ℝ E C ▸ h2) h1
    · exact hdis s (s + (d : Fin M)) (Or.inl rfl) (Or.inr rfl) X h2 (segment_symm ℝ F D ▸ h1)
    · exact hdis (s + (c : Fin M)) (s + (d : Fin M)) (Or.inr rfl) (Or.inr rfl) X (segment_symm ℝ E C ▸ h2) (segment_symm ℝ F D ▸ h1)
  · -- mirror: swap the roles of A and C, B and D
    have hgB' : gl C A D < 0 := by rw [gl_swap]; linarith
    have hgD' : 0 < gl C A B := by rw [gl_swap]; linarith
    have hEg' : gl C A E ≤ 0 := by rw [gl_swap]; linarith
    have hchord' : ∀ X, (X ∈ segment ℝ D F ∨ X ∈ segment ℝ F B) → gl C A X = 0 → X ∈ segment ℝ C A := by
      intro X hX h0
      rw [gl_swap] at h0
      rw [segment_symm]
      apply hchord X
      · rcases hX with h | h
        · right; rwa [segment_symm]
        · left; rwa [segment_symm]
      · linarith
    have hchordE' : gl C A E = 0 → E ∈ segment ℝ C A := by
      intro h0; rw [segment_symm]; apply hchordE; rw [gl_swap] at h0; linarith
    have hBT := vertex_tri_eq P (a := s + (c : Fin M)) (j := s + (d : Fin M)) (c := s) (add_cast_ne (by omega) hd).symm
      (add_cast_ne_self (by omega) hd) hE hgB' hEg'
    obtain ⟨X, hX1, hX2⟩ := path_cross hgB' hgD' hEg' hchord' hchordE' (by simpa [hDd, hA, hCd] using hBT)
    rcases hX1 with h1 | h1 <;> rcases hX2 with h2 | h2
    · exact hdis (s + (c : Fin M)) (s + (d : Fin M)) (Or.inr rfl) (Or.inr rfl) X (segment_symm ℝ E C ▸ h2) h1
    · exact hdis s (s + (d : Fin M)) (Or.inl rfl) (Or.inr rfl) X (segment_symm ℝ A E ▸ h2) h1
    · exact hdis (s + (c : Fin M)) (s + (b : Fin M)) (Or.inr rfl) (Or.inl rfl) X (segment_symm ℝ E C ▸ h2) (segment_symm ℝ F B ▸ h1)
    · exact hdis s (s + (b : Fin M)) (Or.inl rfl) (Or.inl rfl) X (segment_symm ℝ A E ▸ h2) (segment_symm ℝ F B ▸ h1)

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.no_interleave

import Erdos634.Draft.LaczFormalL3

/-!
# Rule W2: the positions of the two far-side `b`-edges (interface lemma I2)

Erdős #634, base-`β` band.  Credit: AI assistant (item 3, band program), Beeson–Roșu, Beeson, Laczkovich, Paliy.
UNAUDITED.  Axiom-clean; no `sorry`.

`L3_two_b_pos`: strengthens `L3_two_b`: the two far-side edges of a `2B` chord `[P,G]` are exactly
`[P, M]` and `[M, G]`, `M` the midpoint (they abut at the midpoint).
-/

namespace Erdos634.LaczJunction

open Erdos634.Geometry Erdos634.Draft.TraceCovering Set

variable {N : ℕ}

open Classical in
theorem L3_two_b_pos (D : Dissection N) (A B C : ℕ)
    (hcover : ∀ x y z : ℕ, x * A + y * B + z * C = 2 * B → x = 0 ∧ y = 2 ∧ z = 0)
    (habc : ∀ (i : Fin N) (k : Fin 3),
      dist ((D.tile i).pts k) ((D.tile i).pts (k+1)) = (A : ℝ) ∨
      dist ((D.tile i).pts k) ((D.tile i).pts (k+1)) = (B : ℝ) ∨
      dist ((D.tile i).pts k) ((D.tile i).pts (k+1)) = (C : ℝ))
    {P G : Plane} (hne : P ≠ G) (hPG : dist P G = 2 * (B : ℝ))
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf0 : f ≠ 0) (hfP : f P = c) (hfG : f G = c)
    (hint : ∀ t : ℝ, 0 < t → t < 1 → AffineMap.lineMap P G t ∈ interior D.target.carrier)
    (hbef : ∀ t : ℝ, t < 0 → AffineMap.lineMap P G t ∉ D.target.carrier)
    (hwall : ∀ t : ℝ, 0 < t → t < 1 → ∀ i, AffineMap.lineMap P G t ∉ interior (D.tile i).carrier)
    (hGend : ¬ Straddled D (-f) (-c) G) :
    ∃ e₁ e₂ : Fin N × Fin 3, e₁ ≠ e₂ ∧ e₁ ∈ D.lineChain (-f) (-c) ∧ e₂ ∈ D.lineChain (-f) (-c) ∧
      dist ((D.tile e₁.1).pts e₁.2) ((D.tile e₁.1).pts (e₁.2 + 1)) = (B : ℝ) ∧
      dist ((D.tile e₂.1).pts e₂.2) ((D.tile e₂.1).pts (e₂.2 + 1)) = (B : ℝ) ∧
      (((D.tile e₁.1).edge e₁.2 = segment ℝ P (midpoint ℝ P G) ∧
          (D.tile e₂.1).edge e₂.2 = segment ℝ (midpoint ℝ P G) G) ∨
        ((D.tile e₂.1).edge e₂.2 = segment ℝ P (midpoint ℝ P G) ∧
          (D.tile e₁.1).edge e₁.2 = segment ℝ (midpoint ℝ P G) G)) := by
  obtain ⟨e₁, e₂, hne12, h1, h2, hs1, hs2, hl1, hl2⟩ :=
    L3_two_b D A B C hcover habc hne hPG f c hf0 hfP hfG hint hbef hwall hGend
  refine ⟨e₁, e₂, hne12, h1, h2, hl1, hl2, ?_⟩
  have hBr : 0 < dist P G := dist_pos.mpr hne
  have hu0 : (dist P G)⁻¹ • (G - P) ≠ 0 :=
    smul_ne_zero (inv_ne_zero hBr.ne') (sub_ne_zero.mpr (Ne.symm hne))
  set u : Plane := (dist P G)⁻¹ • (G - P) with hu
  have hfu : f u = 0 := by rw [hu, map_smul, map_sub, hfG, hfP]; simp
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, Real.norm_of_nonneg hBr.le, ← dist_eq_norm, dist_comm G P]
    exact inv_mul_cancel₀ hBr.ne'
  have hend : P + (dist P G) • u = G := by
    rw [hu, smul_smul, mul_inv_cancel₀ hBr.ne', one_smul]; abel
  have hgd : ∀ y, (-f) y = -c ↔ f y = c := neg_iff
  have hnf : (-f : Plane →ₗ[ℝ] ℝ) ≠ 0 := fun h => hf0 (neg_eq_zero.mp h)
  have hu0' : u ≠ 0 := hu0
  have hmid : P + (dist P G / 2) • u = midpoint ℝ P G := by
    have : dist P G / 2 * (dist P G)⁻¹ = 1 / 2 := by field_simp
    rw [hu, smul_smul, this, midpoint_eq_smul_add]
    simp only [invOf_eq_inv]
    module
  have dat : ∀ e ∈ D.lineChain (-f) (-c), lo D P u e < hi D P u e ∧
      (D.tile e.1).edge e.2 = (fun x : ℝ => P + x • u) '' Icc (lo D P u e) (hi D P u e) ∧
      (‖u‖ = 1 → dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = hi D P u e - lo D P u e) := by
    intro e he
    obtain ⟨a, b, c', d⟩ := edge_data (D := D) (X := P) (u := u) hf0 hfP hfu hu0' (onLine hgd he).1 (onLine hgd he).2
    exact ⟨a, b, d⟩
  have ins : ∀ e ∈ D.lineChain (-f) (-c), (D.tile e.1).edge e.2 ⊆ segment ℝ P G →
      0 ≤ lo D P u e ∧ hi D P u e ≤ dist P G := by
    intro e he hsub
    have := (inside_iff (D := D) (X := P) (u := u) hgd hf0 hfP hfu hu0' he (s := 0) (t := dist P G) hBr.le).mp
      (by
        have e0 : P + (0:ℝ) • u = P := by simp
        rw [e0, hend]; exact hsub)
    exact this
  obtain ⟨a1, ed1, d1⟩ := dat e₁ h1
  obtain ⟨a2, ed2, d2⟩ := dat e₂ h2
  obtain ⟨i10, i11⟩ := ins e₁ h1 hs1
  obtain ⟨i20, i21⟩ := ins e₂ h2 hs2
  have len1 : hi D P u e₁ - lo D P u e₁ = B := by rw [← d1 hu1]; exact hl1
  have len2 : hi D P u e₂ - lo D P u e₂ = B := by rw [← d2 hu1]; exact hl2
  have hB2 : dist P G = 2 * B := hPG
  have hBpos : (0:ℝ) < B := by have := hBr; rw [hB2] at this; linarith
  -- two intervals of length `B` in `[0, 2B]` with at most a common point abut
  have key : ∀ ea eb : Fin N × Fin 3, ea ∈ D.lineChain (-f) (-c) → eb ∈ D.lineChain (-f) (-c) → ea ≠ eb →
      hi D P u ea - lo D P u ea = B → hi D P u eb - lo D P u eb = B →
      0 ≤ lo D P u ea → hi D P u ea ≤ dist P G → 0 ≤ lo D P u eb → hi D P u eb ≤ dist P G →
      lo D P u ea ≤ lo D P u eb → lo D P u ea = 0 ∧ lo D P u eb = B := by
    intro ea eb ha hb hab lena lenb ia0 ia1 ib0 ib1 hle
    have hmeet := meet (D := D) (X := P) (u := u) hnf hgd hf0 hfP hfu hu0' ea ha eb hb hab
    obtain ⟨la, -, -⟩ := dat ea ha
    obtain ⟨lb, -, -⟩ := dat eb hb
    by_cases hov : lo D P u eb < hi D P u ea
    · exfalso
      have hp : lo D P u eb ∈ Icc (lo D P u ea) (hi D P u ea) ∩ Icc (lo D P u eb) (hi D P u eb) :=
        ⟨⟨hle, hov.le⟩, ⟨le_rfl, lb.le⟩⟩
      have hq : hi D P u ea ∈ Icc (lo D P u ea) (hi D P u ea) ∩ Icc (lo D P u eb) (hi D P u eb) :=
        ⟨⟨la.le, le_rfl⟩, ⟨hov.le, by linarith⟩⟩
      have := hmeet hp hq
      linarith
    · push_neg at hov
      constructor <;> linarith
  have hBpos : (0:ℝ) < B := by have := hBr; rw [hB2] at this; linarith
  have edge_eq : ∀ e ∈ D.lineChain (-f) (-c), ∀ s t : ℝ, lo D P u e = s → hi D P u e = t →
      (D.tile e.1).edge e.2 = segment ℝ (P + s • u) (P + t • u) := by
    intro e he s t hs ht
    obtain ⟨hlt, hed, -⟩ := dat e he
    rw [hed, ← hs, ← ht, segment_param, min_eq_left hlt.le, max_eq_right hlt.le]
  have hmidB : P + (B:ℝ) • u = midpoint ℝ P G := by
    have : (B:ℝ) = dist P G / 2 := by linarith
    rw [this]; exact hmid
  have hGB : P + (2 * (B:ℝ)) • u = G := by rw [← hB2]; exact hend
  have first : ∀ e ∈ D.lineChain (-f) (-c), lo D P u e = 0 → hi D P u e - lo D P u e = B →
      (D.tile e.1).edge e.2 = segment ℝ P (midpoint ℝ P G) := by
    intro e he h0 hl
    rw [edge_eq e he 0 B h0 (by linarith), zero_smul, add_zero, hmidB]
  have second : ∀ e ∈ D.lineChain (-f) (-c), lo D P u e = B → hi D P u e - lo D P u e = B →
      (D.tile e.1).edge e.2 = segment ℝ (midpoint ℝ P G) G := by
    intro e he h0 hl
    rw [edge_eq e he B (2 * B) h0 (by linarith), hmidB, hGB]
  rcases le_total (lo D P u e₁) (lo D P u e₂) with hle | hle
  · obtain ⟨x0, y0⟩ := key e₁ e₂ h1 h2 hne12 len1 len2 i10 i11 i20 i21 hle
    exact Or.inl ⟨first e₁ h1 x0 len1, second e₂ h2 y0 len2⟩
  · obtain ⟨x0, y0⟩ := key e₂ e₁ h2 h1 hne12.symm len2 len1 i20 i21 i10 i11 hle
    exact Or.inr ⟨first e₂ h2 x0 len2, second e₁ h1 y0 len1⟩

#print axioms L3_two_b_pos

end Erdos634.LaczJunction

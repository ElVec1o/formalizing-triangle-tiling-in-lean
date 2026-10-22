import Erdos634.Refl.SoundStage6

/-! Stage 7: `hfree_sound`. -/

set_option linter.unusedSimpArgs false
open Erdos634.CertNode Erdos634.PlacementCompleteness
open Erdos634.Geometry (Plane)

namespace Refl

theorem Tri.edge_mod (t : _root_.Tri) (e : Nat) : t.edge e = t.edge (e % 3) := by
  have h3 : (e % 3 + 1) % 3 = (e + 1) % 3 := by omega
  simp only [_root_.Tri.edge, Nat.mod_mod, h3]

theorem zip_all_ex {α β : Type} (P : α × β → Bool) :
    ∀ (xs : List α) (ys : List β), ys.length = xs.length → (xs.zip ys).all P = true →
      ∀ x ∈ xs, ∃ y, P (x, y) = true := by
  intro xs
  induction xs with
  | nil => intro ys _ _ x hx; simp at hx
  | cons a as ih =>
    intro ys hl h x hx
    cases ys with
    | nil => simp at hl
    | cons b bs =>
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨b, h.1⟩
      · exact ih bs (by simpa using hl) h.2 x hx'

/-- **`hfree`**: the curve `t ↦ v + t(d + t√Dn d⊥)` stays in the unfilled region for `0 < t ≤ τ`. -/
theorem hfree_sound (Dn : ℝ) (hD : 0 < Dn) (I : Inst) (hDn : (I.Dn : ℝ) = Dn)
    (htok : I.tgt.ok = true) (cfg : List _root_.Tri) (hcfg : ∀ t ∈ cfg, t.ok = true)
    (n : Node) (F : LocalFacts I cfg n)
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

#print axioms Refl.hfree_sound
end Refl

import Erdos634.Refl.SoundStage8b

/-! Stage 9: `hblocked_sound`. -/

set_option linter.unusedSimpArgs false
open Erdos634.CertNode Erdos634.PlacementCompleteness
open Erdos634.Geometry (Plane)

namespace Refl

theorem hblocked_sound (Dn : ℝ) (hD : 0 < Dn) (I : Inst) (hDn : (I.Dn : ℝ) = Dn)
    (cfg : List _root_.Tri) (hcfg : ∀ t ∈ cfg, t.ok = true) (n : Node) (F : LocalFacts I cfg n)
    {N : ℕ} (D : Erdos634.Geometry.CongruentDissection N) (S : Finset (Fin N))
    (hS : ∀ t ∈ cfg, ∃ i ∈ S, (D.tile i).carrier = t.carr Dn)
    (hbase : n.hb.base = true → ∀ p ∈ D.target.carrier, 0 ≤ p 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t s : ℝ, 0 < t → t < δ → 0 < s → s < δ →
      (n.v.re Dn) + t • ((n.d.re Dn) - s • perp (n.d.re Dn)) ∉ unfilled D.toDissection S := by
  have h := F.blk
  unfold blockedOk at h
  by_cases hb : n.hb.base = true
  · simp only [hb, if_true] at h
    exact hblocked_base_sound Dn hD n F.vw F.dw h D S (hbase hb)
  · simp only [Bool.not_eq_true] at hb
    simp only [hb, Bool.false_eq_true, if_false] at h
    cases hm : cfg[n.hb.m]? with
    | none => rw [hm] at h; simp at h
    | some T =>
      rw [hm] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at h
      have hTm : T ∈ cfg := List.mem_of_getElem? hm
      obtain ⟨T', hsub, h0, hw⟩ := wedge_data_sound Dn hD I hDn T (hcfg T hTm) n.v n.d F.vw F.dw n.hb.W h
      obtain ⟨i, hi, hti⟩ := hS T hTm
      exact hblocked_of_wedge' hD D.toDissection S hi _ _ T' (by rw [hti]; exact hsub) h0 hw

#print axioms Refl.hblocked_sound
end Refl

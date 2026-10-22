-- Draft/LaczFormalL2b.lean -- atom L2b: Beeson-Rosu (arXiv 2607.23453) Lemma 1, second claim:
-- "if T is not equilateral and has commensurable angles, so does R" (B-R cite the first paragraph of the proof of
-- Thm 5.3 of Laczkovich, DM 140 (1995)).  We do NOT reconstruct Laczkovich's paragraph.  Instead the statement is
-- DERIVED from our own shape classification: `LemmaCFinal.lemmaC_general` (tile with an irrational angle and
-- target not similar to it: one of five tile types with listed target shapes) plus `LemmaPProof.lemmaP_general`
-- (pi/3 tile) -- in every outcome the target has an irrational angle or is equilateral.  Any N.
-- UNAUDITED beyond TABLE.md.  Credit: Laczkovich (1995), Beeson-Rosu.
import Erdos634.Draft.LaczFormalL2a
import Erdos634.Draft.LemmaPProof

open scoped Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
  Erdos634.Draft.LemmaCFinal

namespace Erdos634.Draft.LaczFormal

theorem tgt_mem {N : ℕ} {D : CongruentDissection N} {x y z : ℝ} (h : TgtAngles D x y z) :
    (∃ k, D.target.angleAt k = x) ∧ (∃ k, D.target.angleAt k = y) ∧ ∃ k, D.target.angleAt k = z := by
  obtain ⟨σ, h0, h1, h2⟩ := h
  exact ⟨⟨_, h0⟩, ⟨_, h1⟩, ⟨_, h2⟩⟩

/-- **L2b (Beeson-Rosu Lemma 1, second claim).**  A non-equilateral triangle with commensurable angles,
dissected into congruent copies of a tile, forces the tile to have commensurable angles. -/
theorem lemma1b {N : ℕ} (D : CongruentDissection N) (hne : ¬ Equilateral D)
    (h : CommAngles D.target) : CommAngles D.model := by
  by_contra hm
  rw [commAngles_iff] at h hm
  have hirr : ∃ k, IrrPi (D.model.angleAt k) := by
    by_contra hc; push Not at hc
    exact hm (fun k => by by_contra hk; exact hc k hk)
  -- every target angle lies in Q pi
  have hT : ∀ x : ℝ, (∃ k, D.target.angleAt k = x) → ∃ q : ℚ, x = (q : ℝ) * Real.pi := by
    rintro x ⟨k, rfl⟩; exact h k
  by_cases hs : SimilarTM D
  · obtain ⟨μ, τ, hh⟩ := hs
    obtain ⟨k, hk⟩ := hirr
    obtain ⟨q, hq⟩ := h (τ.symm k)
    have := (hh (τ.symm k)).1
    rw [Equiv.apply_symm_apply] at this
    exact hk ⟨q, by rw [← this]; exact hq⟩
  rcases lemmaC_general D hirr hs with hc | hc | hc | hc | hc
  · -- right tile
    obtain ⟨α, -, -, hα0, -, γ, hγ, i, j, -, hi, -⟩ := hc
    have hα := irrPi_of_irrational hα0
    obtain ⟨q, hq⟩ := hT γ ⟨i, hi⟩
    rcases hγ with e | e
    · exact irrPi_ne hα q (by rw [← e]; exact hq)
    · exact irrPi_ne hα (1 / 2 - q) (by push_cast; linarith)
  · obtain ⟨α, a, b, c, hα, -, i, j, -, hi, -⟩ := hc
    obtain ⟨q, hq⟩ := hT α ⟨i, hi⟩
    exact irrPi_ne hα q hq
  · obtain ⟨α, a, b, c, hα, hd⟩ := hc
    exact hne (Erdos634.Draft.LemmaPProof.lemmaP_general D α a b c hα hd hs)
  · obtain ⟨α, a, b, c, hα, hd, hsh⟩ := hc
    rcases hsh with hE | hI | hF1 | hF2
    · exact hne hE
    · rcases hI with e | e
      · obtain ⟨q, hq⟩ := hT α (tgt_mem e).1
        exact irrPi_ne hα q hq
      · obtain ⟨q, hq⟩ := hT _ (tgt_mem e).1
        exact irrPi_ne hα (1 / 3 - q) (by push_cast; linarith)
    · rcases hF1 with e | e
      · obtain ⟨q, hq⟩ := hT α (tgt_mem e).1
        exact irrPi_ne hα q hq
      · obtain ⟨q, hq⟩ := hT _ (tgt_mem e).1
        exact irrPi_ne hα (1 / 3 - q) (by push_cast; linarith)
    · rcases hF2 with e | e | e | e | e
      · obtain ⟨q, hq⟩ := hT _ (tgt_mem e).1
        exact irrPi_ne hα (q / 2) (by push_cast; linarith)
      · obtain ⟨q, hq⟩ := hT _ (tgt_mem e).1
        exact irrPi_ne hα q hq
      · obtain ⟨q, hq⟩ := hT _ (tgt_mem e).1
        exact irrPi_ne hα (1 / 3 - q) (by push_cast; linarith)
      · obtain ⟨q, hq⟩ := hT _ (tgt_mem e).1
        exact irrPi_ne hα q hq
      · obtain ⟨q, hq⟩ := hT _ (tgt_mem e).1
        exact irrPi_ne hα (1 / 3 - q) (by push_cast; linarith)
  · obtain ⟨α, β, a, b, c, hα, hrel, hd, hsh⟩ := hc
    rcases hsh with e | e | e | e | e
    · obtain ⟨q, hq⟩ := hT _ (tgt_mem e).1
      exact irrPi_ne hα ((1 - 2 * q) / 3) (by push_cast; linarith)
    · obtain ⟨q, hq⟩ := hT _ (tgt_mem e).2.2
      exact irrPi_ne hα q hq
    · obtain ⟨q, hq⟩ := hT _ (tgt_mem e).1
      exact irrPi_ne hα (q / 2) (by push_cast; linarith)
    · obtain ⟨q, hq⟩ := hT _ (tgt_mem e).2.1
      exact irrPi_ne hα q hq
    · obtain ⟨q, hq⟩ := hT _ (tgt_mem e).1
      exact irrPi_ne hα q hq

/-- **Beeson-Rosu Lemma 1, both claims.** -/
theorem lemma1 {N : ℕ} (D : CongruentDissection N) :
    (CommAngles D.model → CommAngles D.target) ∧
      (¬ Equilateral D → CommAngles D.target → CommAngles D.model) :=
  ⟨lemma1a D, lemma1b D⟩

/-- Non-vacuity of `lemma1b`: a real dissection (`CaseALemmaHPiFour`, target angles `π/4,π/4,π/2`)
has a non-equilateral commensurable target. -/
theorem lemma1b_witness :
    ∃ (N : ℕ) (D : CongruentDissection N), ¬ Equilateral D ∧ CommAngles D.target := by
  refine ⟨_, Erdos634.Draft.CaseALemmaHPiFour.dissection, ?_,
    Erdos634.Draft.LaczFormal.lemma1a_witness_target⟩
  intro hE
  have h0 := hE 0
  rw [Erdos634.Draft.CaseALemmaHPiFour.target_angleAt0] at h0
  have := Real.pi_pos
  linarith

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.lemma1b
#print axioms Erdos634.Draft.LaczFormal.lemma1
#print axioms Erdos634.Draft.LaczFormal.lemma1b_witness

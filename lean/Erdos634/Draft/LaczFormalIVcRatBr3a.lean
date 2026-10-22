-- Draft/LaczFormalIVcRatBr3a.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, rational branch): BRIDGE stage Br3a (B-b, the combinatorial core of the V/W clause).
--   `involution_count`: S a finite set closed under an involution `sigma`, `lab` a 2-colouring with equally many points of each colour: the number of points whose sigma-partner has the SAME colour
--   is the same for both colours (A = B).  This is the counting behind "V(Q) = W(Q') for some kite Q'" (blueprint P2): at a vertex X the pi- and rho-corners are equinumerous (regularity)
--   and the partner map pairs them up; kite pairs preserve the label, parallelogram pairs swap it.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3, Lemma 4.8), Beeson, Beeson-Zhang.
import Mathlib

open scoped Classical

namespace Erdos634.Draft.LaczFormal.RG

theorem card_split {ι : Type*} (S : Finset ι) (p q : ι → Prop) :
    (S.filter p).card = (S.filter (fun x => p x ∧ q x)).card + (S.filter (fun x => p x ∧ ¬ q x)).card := by
  have := Finset.card_filter_add_card_filter_not (s := S.filter p) q
  simp only [Finset.filter_filter] at this
  exact this.symm

/-- Equally many points of each colour and a colour-respecting involution: equally many same-colour pairs of each colour. -/
theorem involution_count {ι : Type*} (S : Finset ι) (σ : ι → ι) (lab : ι → Prop) (hσS : ∀ x ∈ S, σ x ∈ S)
    (hinv : ∀ x ∈ S, σ (σ x) = x) (hcard : (S.filter lab).card = (S.filter (fun x => ¬ lab x)).card) :
    (S.filter (fun x => lab x ∧ lab (σ x))).card = (S.filter (fun x => ¬ lab x ∧ ¬ lab (σ x))).card := by
  have h1 : (S.filter lab).card = (S.filter (fun x => lab x ∧ lab (σ x))).card + (S.filter (fun x => lab x ∧ ¬ lab (σ x))).card := by
    convert card_split S lab (fun x => lab (σ x))
  have h2 : (S.filter (fun x => ¬ lab x)).card = (S.filter (fun x => ¬ lab x ∧ lab (σ x))).card + (S.filter (fun x => ¬ lab x ∧ ¬ lab (σ x))).card := by
    convert card_split S (fun x => ¬ lab x) (fun x => lab (σ x))
  have hC : (S.filter (fun x => lab x ∧ ¬ lab (σ x))).card = (S.filter (fun x => ¬ lab x ∧ lab (σ x))).card := by
    apply Finset.card_nbij' σ σ
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe] at hx ⊢
      obtain ⟨hxS, hl, hn⟩ := hx
      refine ⟨hσS x hxS, hn, ?_⟩
      rw [hinv x hxS]; exact hl
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe] at hx ⊢
      obtain ⟨hxS, hn, hl⟩ := hx
      refine ⟨hσS x hxS, hl, ?_⟩
      rw [hinv x hxS]; exact hn
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter] at hx
      exact hinv x hx.1
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter] at hx
      exact hinv x hx.1
  omega

#print axioms Erdos634.Draft.LaczFormal.RG.involution_count

end Erdos634.Draft.LaczFormal.RG

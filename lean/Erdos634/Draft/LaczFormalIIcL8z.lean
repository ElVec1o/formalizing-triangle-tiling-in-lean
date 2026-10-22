-- Draft/LaczFormalIIcL8z.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, Lemma 6.3 assembly, TWO exceptional points: `lemma63_two`.
-- Conclusion (v) without its printed inequality: `Concl5Rest` (M = 2k, k >= 4, RationalPoly, all angles alpha + beta, central symmetry) and `Concl5Seq` (the side sequence read from the first corner sent to E,
-- forwards or backwards, geometric of ratio q = sin alpha / sin beta along n + 2 < k).  `concl5_of_parts` adds the printed inequality a_k >= q^(k-1) a_1 (G11), which is NOT proved here.
-- NOTE, UNAUDITED.  CONDITIONAL on `kiteB = empty` (NoKites) and on the Case IIc hypothesis block (witnessed by GenWitK (204-tile octagon, genTiling_thm21) and IsoWitM).  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcL8y

open scoped Classical Fin.NatCast
open EuclideanGeometry Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- Everything in `Concl5` except the side sequence and the inequality. -/
def Concl5Rest (C : CongruentRegionDissection N) (P : ConvPoly M) (k : ℕ) : Prop :=
  M = 2 * k ∧ 4 ≤ k ∧ RationalPoly P ∧ (∀ i, P.angle i = angleAt C.model 0 + angleAt C.model 1) ∧
    (∀ i : Fin M, P.side i = P.side (i + Fin.ofNat M k))

/-- The side sequence of `Concl5`, with its geometric recursion (but without the final inequality). -/
def Concl5Seq (C : CongruentRegionDissection N) (P : ConvPoly M) (k : ℕ) (s : Fin M) (rev : Bool) (a : ℕ → ℝ) : Prop :=
  (∀ n, a n = if rev then P.side (s - (Fin.ofNat M n) - 1) else P.side (s + (Fin.ofNat M n))) ∧
    (∀ n, n + 2 < k → a (n + 1) = Real.sin (angleAt C.model 0) / Real.sin (angleAt C.model 1) * a n)

theorem concl5_of_parts {C : CongruentRegionDissection N} {P : ConvPoly M} {k : ℕ} {s : Fin M} {rev : Bool} {a : ℕ → ℝ}
    (h1 : Concl5Rest C P k) (h2 : Concl5Seq C P k s rev a)
    (h3 : (Real.sin (angleAt C.model 0) / Real.sin (angleAt C.model 1)) ^ (k - 1) * a 0 ≤ a (k - 1)) : Concl5 C P :=
  ⟨k, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2, Real.sin (angleAt C.model 0) / Real.sin (angleAt C.model 1), Or.inl rfl, s, rev, a, h2.1, h2.2, h3⟩

theorem ofNat_cast_fin (n : ℕ) : (Fin.ofNat M n : Fin M) = (n : Fin M) := by
  apply Fin.ext
  simp [Fin.ofNat, Fin.val_natCast]

set_option maxHeartbeats 12800000 in
/-- **Lemma 6.3, two exceptional points** (conclusion (v) without its printed inequality). -/
theorem lemma63_two {k : ℕ} [NeZero (2 * k)] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly (2 * k)) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l))
    (hcor : ∀ j : Fin (2 * k), cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0)
    (hNK : kiteB D idx = ∅) (W : Fin (2 * k) → Plane) (hW : ∀ j, GExc D idx (P.v j) (W j)) (hdiff : ∃ j, W j ≠ W 0) :
    Concl5Rest D P k ∧ ∃ (s : Fin (2 * k)) (rev : Bool) (a : ℕ → ℝ), Concl5Seq D P k s rev a := by
  obtain ⟨E, F, hEF, hI⟩ := index_split D P hreg idx hC hab hac h1 h3 G hcor hNK W hW hdiff
  obtain ⟨hang, hMγ⟩ := corner_angles_gamma D P hreg idx hC h1 h3 hcor
  have hk4 := k_ge_four (model_angle_pos' D 2) h1 h3 hMγ
  have hint : ∀ E ∈ excVerts2 D idx P, E ∈ interior D.region := fun E hE =>
    (gexc_exc_interior_exact D P hreg idx hC hab hac h1 h3 G hcor E hE).1
  have hsym := central_symmetry_two_exc D P hreg idx hC hab hac h1 h3 G hcor hNK W hW hdiff
  have hαβγ := angleAt_sum D.model
  refine ⟨⟨rfl, hk4, rational_of_caseC D idx hC hab P hreg, fun i => ?_, fun i => ?_⟩, ?_⟩
  · change P.angle i = D.model.angleAt 0 + D.model.angleAt 1
    rw [hang i]; linarith
  · rw [ofNat_cast_fin]; exact hsym i
  obtain ⟨a, b, hab', s0, hrec⟩ := geometric_sides_of_spokes D P hreg idx hC h1 h3 hcor (by omega) hint W hW E F hI
  have hpos0 : 0 < Real.sin (D.model.angleAt 0) := Real.sin_pos_of_pos_of_lt_pi (model_angle_pos' D 0) (by linarith [model_angle_pos' D 1, model_angle_pos' D 2])
  have hpos1 : 0 < Real.sin (D.model.angleAt 1) := Real.sin_pos_of_pos_of_lt_pi (model_angle_pos' D 1) (by linarith [model_angle_pos' D 0, model_angle_pos' D 2])
  rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨s0, false, fun n => P.side (s0 + (Fin.ofNat (2 * k) n)), ⟨fun n => by simp, fun n hn => ?_⟩⟩
    simp only [ofNat_cast_fin]
    show P.side (s0 + ((n + 1 : ℕ) : Fin (2 * k))) = Real.sin (D.model.angleAt 0) / Real.sin (D.model.angleAt 1) * P.side (s0 + (n : Fin (2 * k)))
    have := hrec n hn
    rw [div_mul_eq_mul_div, eq_div_iff hpos1.ne']
    linarith
  · refine ⟨s0 + ((k - 1 : ℕ) : Fin (2 * k)), true, fun n => P.side (s0 + ((k - 1 : ℕ) : Fin (2 * k)) - (Fin.ofNat (2 * k) n) - 1), ⟨fun n => by simp, fun n hn => ?_⟩⟩
    simp only [ofNat_cast_fin]
    have hm := hrec (k - 3 - n) (by omega)
    have e1 : s0 + ((k - 1 : ℕ) : Fin (2 * k)) - ((n + 1 : ℕ) : Fin (2 * k)) - 1 = s0 + ((k - 3 - n : ℕ) : Fin (2 * k)) := by
      have : (k - 3 - n : ℕ) + (n + 1) + 1 = k - 1 := by omega
      have h' : ((k - 1 : ℕ) : Fin (2 * k)) = ((k - 3 - n : ℕ) : Fin (2 * k)) + ((n + 1 : ℕ) : Fin (2 * k)) + 1 := by
        rw [← this]; push_cast; ring
      rw [h']; abel
    have e2 : s0 + ((k - 1 : ℕ) : Fin (2 * k)) - (n : Fin (2 * k)) - 1 = s0 + ((k - 3 - n + 1 : ℕ) : Fin (2 * k)) := by
      have : (k - 3 - n + 1 : ℕ) + n + 1 = k - 1 := by omega
      have h' : ((k - 1 : ℕ) : Fin (2 * k)) = ((k - 3 - n + 1 : ℕ) : Fin (2 * k)) + (n : Fin (2 * k)) + 1 := by
        rw [← this]; push_cast; ring
      rw [h']; abel
    rw [e1, e2]
    show P.side (s0 + ((k - 3 - n : ℕ) : Fin (2 * k))) = Real.sin (D.model.angleAt 0) / Real.sin (D.model.angleAt 1) * P.side (s0 + ((k - 3 - n + 1 : ℕ) : Fin (2 * k)))
    rw [div_mul_eq_mul_div, eq_div_iff hpos1.ne']
    linarith

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.lemma63_two

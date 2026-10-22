-- Draft/LaczFormalIIcL8x.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, ONE exceptional point: `lemma63_one` gives `Concl7` (the polygon is regular, alpha = beta = pi/2 - pi/M, gamma = 2 pi/M).
-- Route: `spokes_angle` (all corners to the same point E), the similarity chain `spoke_chain_alpha_eq_beta` gives alpha = beta, the law of sines in each triangle E V_i V_{i+1} makes the sides equal; the angle sum gives the angles.
-- NOTE, UNAUDITED.  CONDITIONAL on the Case IIc hypothesis block (witnessed by GenWitK (204-tile octagon, genTiling_thm21) and IsoWitM); `kiteB = empty` is NOT needed here (W is given).  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcL8v
import Erdos634.Draft.LaczFormalIIcSpoke1

open scoped Classical Fin.NatCast
open EuclideanGeometry Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

theorem gexc_ne (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) {X Y : Plane} (h : GExc D idx X Y) : Y ≠ X := by
  obtain ⟨d, Z, L1, L2, H1, H2, T1, T2, hd, -, -, -, -, -, -, hT1, hT2, hH1, hH2, hY⟩ := gexc_data D idx h
  have hne : ∀ {H : Plane} {T : ℝ}, 0 < T → toV2 (H - X) = (T * d.1, T * d.2) → H ≠ X := by
    intro H T hT hH hHX
    subst hHX
    have : toV2 (H - H) = (0, 0) := by unfold toV2; ext <;> simp
    rw [this] at hH
    have h1 := congrArg Prod.fst hH
    have h2 := congrArg Prod.snd hH
    simp only at h1 h2
    apply hd
    ext
    · exact (mul_eq_zero.mp h1.symm).resolve_left hT.ne'
    · exact (mul_eq_zero.mp h2.symm).resolve_left hT.ne'
  rcases hY with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact hne hT1 hH1
  · exact hne hT2 hH2

set_option maxHeartbeats 12800000 in
/-- **Lemma 6.3, one exceptional point** (all corners send their edge to the same point). -/
theorem lemma63_one [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l))
    (hcor : ∀ j : Fin M, cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0)
    (W : Fin M → Plane) (hW : ∀ j, GExc D idx (P.v j) (W j)) (hsame : ∀ j, W j = W 0) : Concl7 D P := by
  have hint : ∀ E ∈ excVerts2 D idx P, E ∈ interior D.region := fun E hE =>
    (gexc_exc_interior_exact D P hreg idx hC hab hac h1 h3 G hcor E hE).1
  obtain ⟨a, b, hab', hsp⟩ := spokes_angle D P hreg idx hC h1 h3 hcor hint W hW
  obtain ⟨hang, hMγ⟩ := corner_angles_gamma D P hreg idx hC h1 h3 hcor
  have hpi := Real.pi_pos
  have hγ0 := model_angle_pos' D 2
  have hαβγ : D.model.angleAt a + D.model.angleAt b + D.model.angleAt 2 = Real.pi := by
    have := angleAt_sum D.model
    rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact this
    · linarith
  set E := W 0 with hE
  set V : ℕ → Plane := fun n => P.v (n : Fin M) with hV
  have hVs : ∀ n, V (n + 1) = P.v ((n : Fin M) + 1) := fun n => by simp only [hV, Nat.cast_succ]
  have hper : ∀ i, V (i + M) = V i := fun i => by simp [hV, Nat.cast_add]
  have hne : ∀ i, V i ≠ E := fun i => by
    have := gexc_ne D idx (hW (i : Fin M))
    rw [hsame (i : Fin M)] at this
    exact fun h => this h.symm
  have hA : ∀ i, ∠ E (V i) (V (i + 1)) = D.model.angleAt a := by
    intro i
    have := (hsp ((i : Fin M) - 1)).1
    rw [sub_add_cancel, hsame (i : Fin M)] at this
    rw [hVs i, EuclideanGeometry.angle_comm]
    exact this
  have hB : ∀ i, ∠ (V i) (V (i + 1)) E = D.model.angleAt b := by
    intro i
    have := (hsp (i : Fin M)).2
    rw [hsame ((i : Fin M) + 1)] at this
    rw [hVs i]
    exact this
  have hαβlt : D.model.angleAt a + D.model.angleAt b < Real.pi := by linarith
  have hαeqβ := spoke_chain_alpha_eq_beta (n := M) (by have := P.three_le; omega) V E (D.model.angleAt a) (D.model.angleAt b) hper hne hA hB
    (model_angle_pos' D a) (model_angle_pos' D b) hαβlt
  have h01 : D.model.angleAt 0 = D.model.angleAt 1 := by
    rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hαeqβ
    · exact hαeqβ.symm
  have sα : 0 < Real.sin (D.model.angleAt a) := Real.sin_pos_of_pos_of_lt_pi (model_angle_pos' D a) (by linarith)
  have sγ : 0 < Real.sin (D.model.angleAt 2) := Real.sin_pos_of_pos_of_lt_pi hγ0 (by linarith [model_angle_pos' D a, model_angle_pos' D b])
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by have := P.three_le; omega : 0 < M)
  -- the distances to E are constant
  have step : ∀ i, dist (V (i + 1)) E = dist (V i) E := by
    intro i
    have h := EuclideanGeometry.sin_angle_mul_dist_eq_sin_angle_mul_dist (V i) (V (i + 1)) E
    rw [hB i, hA i, dist_comm E (V i), ← hαeqβ] at h
    have := mul_right_cancel₀ sα.ne' (by linarith : dist (V (i + 1)) E * Real.sin (D.model.angleAt a) = dist (V i) E * Real.sin (D.model.angleAt a))
    exact this
  have hr : ∀ i, dist (V i) E = dist (V 0) E := by
    intro i; induction i with
    | zero => rfl
    | succ i ih => rw [step i, ih]
  have hVne : ∀ i, V i ≠ V (i + 1) := by
    intro i h
    rw [hVs i] at h
    have := vtx_inj' P h
    have hf := (ConvPoly.fin_facts P.three_le (i : Fin M)).1
    exact hf this.symm
  -- side length
  have hside : ∀ i : ℕ, P.side (i : Fin M) = Real.sin (D.model.angleAt 2) * dist (V 0) E / Real.sin (D.model.angleAt a) := by
    intro i
    have hsd : P.side (i : Fin M) = dist (V i) (V (i + 1)) := by
      unfold ConvPoly.side; rw [hVs i]
    have hs1 := EuclideanGeometry.angle_add_angle_add_angle_eq_pi (p₁ := V i) (p₂ := V (i + 1)) E (hVne i).symm
    have hl := EuclideanGeometry.law_sin (V i) E (V (i + 1))
    have e1 : ∠ (V (i + 1)) (V i) E = D.model.angleAt a := by rw [EuclideanGeometry.angle_comm]; exact hA i
    have e2 : ∠ (V i) E (V (i + 1)) = D.model.angleAt 2 := by
      rw [EuclideanGeometry.angle_comm]
      have : ∠ (V (i + 1)) E (V i) = Real.pi - D.model.angleAt b - D.model.angleAt a := by
        have hB' := hB i
        have hA' := hA i
        linarith
      rw [this]; linarith
    rw [e1, e2, dist_comm E (V (i + 1)), hr (i + 1)] at hl
    rw [hsd, dist_comm (V i) (V (i + 1))]
    rw [eq_div_iff sα.ne']
    linarith
  have hang0 : ∀ i : Fin M, P.angle i = P.angle 0 := fun i => by rw [hang i, hang 0]
  have hγM : D.model.angleAt 2 = 2 * Real.pi / M := by
    field_simp; linarith
  refine ⟨fun i => ?_, hang0, h01, ?_, hγM⟩
  · have h1' := hside (i.val)
    have h0' := hside 0
    rw [Fin.cast_val_eq_self] at h1'
    simpa using h1'.trans h0'.symm
  · change D.model.angleAt 0 = Real.pi / 2 - Real.pi / M
    have e : 2 * Real.pi / (M : ℝ) = 2 * (Real.pi / M) := by ring
    rw [hγM, e] at hαβγ
    rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> linarith [h01]

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.lemma63_one

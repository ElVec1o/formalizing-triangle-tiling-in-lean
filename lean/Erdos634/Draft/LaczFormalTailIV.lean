-- Draft/LaczFormalTailIV.lean -- tail case (iv) of Laczkovich 1995 Thm 5.3 (p. 93): congruent tiles (pi/6, pi/6, 2pi/3) cannot dissect the
-- 30-60-90 triangle.  Paper argument (own words): each side of T is packed with tile sides, giving 1 = x a + y sqrt3 a, sqrt3 = z a + u sqrt3 a
-- (irrationality of sqrt 3: xy = zu = 0); so some side is packed with a-edges only, hence the 2pi/3 angle touches it, and two obtuse angles
-- would meet on that side (the corner angles of T are < 2pi/3): impossible.  Here: `Row2.lemmaR_gen` (Lemma R without similarity), the
-- algebra, and the relabelling glue.  UNAUDITED.  Credit: Laczkovich (1995), Beeson (Lemma 11 of Triangle tiling I = Lemma R).
import Erdos634.Draft.LaczFormalT6
import Erdos634.Draft.FluxERow2R
import Erdos634.Draft.LaczFormalL9Wit
import Erdos634.Draft.LaczFormalL6Wit2

open scoped Classical

namespace Erdos634.Geometry

open Real

variable {N : ℕ}

/-- `Row2.lemmaR_le` without similarity: the target angles at the two corners of the side `AB` are only required to be below `γ`. -/
theorem Row2.lemmaR_gen (D : CongruentDissection N)
    (ht0 : D.target.angleAt 0 < D.model.angleAt 2) (ht1 : D.target.angleAt 1 < D.model.angleAt 2)
    (h01 : D.model.angleAt 0 ≤ D.model.angleAt 1) (h12 : D.model.angleAt 1 < D.model.angleAt 2)
    (hnoc : ∀ e ∈ D.sideEdges 0, D.eLen e ≠ D.model.oppLen 2) :
    2 * D.model.angleAt 2 = π := by
  classical
  have A_mem : D.target.pts 0 ∈ D.target.edge 0 := left_mem_segment ℝ _ _
  have B_mem : D.target.pts 1 ∈ D.target.edge 0 := right_mem_segment ℝ _ _
  have hnA : ∀ i k, (D.tile i).angleAt k = D.model.angleAt 2 →
      (D.tile i).pts k ≠ D.target.pts 0 :=
    fun i k hk => Row2.no_gamma_corner D 0 i k hk ht0
  have hnB : ∀ i k, (D.tile i).angleAt k = D.model.angleAt 2 →
      (D.tile i).pts k ≠ D.target.pts 1 :=
    fun i k hk => Row2.no_gamma_corner D 1 i k hk ht1
  -- a `γ`-vertex on `AB` lies strictly between `A` and `B`
  have tau_lt : ∀ i k, (D.tile i).angleAt k = D.model.angleAt 2 →
      (D.tile i).pts k ∈ D.target.edge 0 →
      0 < Row2.tau D.target ((D.tile i).pts k) ∧ Row2.tau D.target ((D.tile i).pts k) < 1 := by
    intro i k hk hmem
    obtain ⟨-, h0, h1, h2⟩ := Row2.edge0_coord D.target hmem
    constructor
    · rcases h1.lt_or_eq with h | h
      · exact h
      · exact absurd (Row2.tau_inj D.target hmem A_mem (h.symm.trans (Row2.tau_A D.target).symm))
          (hnA i k hk)
    · rcases (show Row2.tau D.target ((D.tile i).pts k) ≤ 1 by linarith).lt_or_eq with h | h
      · exact h
      · exact absurd (Row2.tau_inj D.target hmem B_mem (h.trans (Row2.tau_B D.target).symm))
          (hnB i k hk)
  -- the `γ`-end of each edge on `AB`
  have gend : ∀ e ∈ D.sideEdges 0, ∃ k, (D.tile e.1).angleAt k = D.model.angleAt 2 ∧
      (D.tile e.1).pts k ∈ D.eSet e ∧
      (Row2.tau D.target ((D.tile e.1).pts k) = Row2.lo D.toDissection e ∨
        Row2.tau D.target ((D.tile e.1).pts k) = Row2.hi D.toDissection e) := by
    intro e he
    obtain ⟨k, hk, hke⟩ := Row2.gamma_endpoint D (hnoc e he)
    obtain ⟨hX, hY⟩ := Row2.eq_inf_or_sup (Row2.tau D.target ((D.tile e.1).pts e.2))
      (Row2.tau D.target ((D.tile e.1).pts (e.2 + 1)))
    rcases hke with rfl | rfl
    · exact ⟨_, hk, left_mem_segment ℝ _ _, hX⟩
    · exact ⟨_, hk, right_mem_segment ℝ _ _, hY⟩
  -- `R`: the edges whose `γ`-end is the far end; the edge at `A` is one
  obtain ⟨R, hR⟩ : ∃ R : Finset (Fin N × Fin 3), R = (D.sideEdges 0).filter (fun e =>
      ∃ k, (D.tile e.1).angleAt k = D.model.angleAt 2 ∧ (D.tile e.1).pts k ∈ D.eSet e ∧
        Row2.tau D.target ((D.tile e.1).pts k) = Row2.hi D.toDissection e) := ⟨_, rfl⟩
  obtain ⟨eA, heA, hAe⟩ := D.toDissection.exists_sideEdge_mem 0 A_mem
  have hReA : eA ∈ R := by
    obtain ⟨k, hk, hkm, hlh⟩ := gend eA heA
    have hpos := (tau_lt _ _ hk (Row2.sideEdge_sub D.toDissection heA hkm)).1
    have hlo : Row2.lo D.toDissection eA ≤ 0 := by
      have := ((Row2.mem_eSet_iff D.toDissection heA A_mem).mp hAe).1
      rwa [Row2.tau_A] at this
    rw [hR, Finset.mem_filter]
    refine ⟨heA, k, hk, hkm, ?_⟩
    rcases hlh with h | h
    · exfalso; linarith
    · exact h
  obtain ⟨eS, heSR, hmax⟩ := R.exists_max_image (Row2.hi D.toDissection) ⟨eA, hReA⟩
  rw [hR, Finset.mem_filter] at heSR
  obtain ⟨heS, kS, hkS, hkSm, hkSt⟩ := heSR
  obtain ⟨s, hs⟩ : ∃ s, s = Row2.hi D.toDissection eS := ⟨_, rfl⟩
  have hkSedge := Row2.sideEdge_sub D.toDissection heS hkSm
  have hs1 : s < 1 := by rw [hs, ← hkSt]; exact (tau_lt _ _ hkS hkSedge).2
  have hs0 : 0 < s := by rw [hs, ← hkSt]; exact (tau_lt _ _ hkS hkSedge).1
  -- `F`: the edges reaching past `s`; the edge at `B` is one
  obtain ⟨F, hF⟩ : ∃ F : Finset (Fin N × Fin 3),
      F = (D.sideEdges 0).filter (fun e => s < Row2.hi D.toDissection e) := ⟨_, rfl⟩
  obtain ⟨eB, heB, hBe⟩ := D.toDissection.exists_sideEdge_mem 0 B_mem
  have hFB : eB ∈ F := by
    rw [hF, Finset.mem_filter]
    refine ⟨heB, ?_⟩
    have := ((Row2.mem_eSet_iff D.toDissection heB B_mem).mp hBe).2
    rw [Row2.tau_B] at this
    linarith
  obtain ⟨e', he'F, hmin⟩ := F.exists_min_image (Row2.lo D.toDissection) ⟨eB, hFB⟩
  have he'F' := he'F
  rw [hF, Finset.mem_filter] at he'F'
  obtain ⟨he', he's⟩ := he'F'
  -- `lo e' ≤ s` (covering)
  have hlo' : Row2.lo D.toDissection e' ≤ s := by
    by_contra hc
    push Not at hc
    obtain ⟨-, hhi1⟩ := Row2.lo_hi_bounds D.toDissection he'
    have hlohi := Row2.lo_lt_hi D.toDissection he'
    obtain ⟨z, hz, hzw⟩ := Row2.tau_surj D.target (s := (s + Row2.lo D.toDissection e') / 2)
      (by linarith) (by linarith)
    obtain ⟨e'', he'', hze''⟩ := D.toDissection.exists_sideEdge_mem 0 hz
    have hz'' := (Row2.mem_eSet_iff D.toDissection he'' hz).mp hze''
    rw [hzw] at hz''
    have he''F : e'' ∈ F := by
      rw [hF, Finset.mem_filter]; exact ⟨he'', by linarith [hz''.2]⟩
    have := hmin e'' he''F
    linarith [hz''.1]
  have hne : e' ≠ eS := by
    intro h; rw [h, ← hs] at he's; exact lt_irrefl _ he's
  -- `lo e' = s` (disjoint interiors)
  have hlo'eq : Row2.lo D.toDissection e' = s := by
    by_contra hc
    have hlt : Row2.lo D.toDissection e' < s := lt_of_le_of_ne hlo' hc
    have hSlo := Row2.lo_lt_hi D.toDissection heS
    rw [← hs] at hSlo
    have hm1 := le_max_left (Row2.lo D.toDissection eS) (Row2.lo D.toDissection e')
    have hm2 := le_max_right (Row2.lo D.toDissection eS) (Row2.lo D.toDissection e')
    have hus : max (Row2.lo D.toDissection eS) (Row2.lo D.toDissection e') < s := max_lt hSlo hlt
    exact Row2.interiors_disjoint D.toDissection heS he' hne.symm
      (s := (max (Row2.lo D.toDissection eS) (Row2.lo D.toDissection e') + s) / 2)
      (by linarith) (by rw [← hs]; linarith) (by linarith) (by linarith)
  -- the `γ`-end of `e'` is its near end, at `s`
  obtain ⟨k', hk', hk'm, hk't⟩ := gend e' he'
  have hk's : Row2.tau D.target ((D.tile e'.1).pts k') = s := by
    rcases hk't with h | h
    · rw [h, hlo'eq]
    · exfalso
      have he'R : e' ∈ R := by
        rw [hR, Finset.mem_filter]; exact ⟨he', k', hk', hk'm, h⟩
      have := hmax e' he'R
      rw [← hs] at this
      linarith
  -- the two `γ`-vertices are one point `P`, of two different tiles
  have hk'edge := Row2.sideEdge_sub D.toDissection he' hk'm
  have hP : (D.tile e'.1).pts k' = (D.tile eS.1).pts kS :=
    Row2.tau_inj D.target hk'edge hkSedge (hk's.trans (hs.trans hkSt.symm))
  have htiles : eS.1 ≠ e'.1 := Row2.distinct_tiles D.toDissection heS he' hne.symm
  -- the angle sum at `P`
  have hPfr : (D.tile eS.1).pts kS ∈ frontier D.target.carrier :=
    Erdos634.SideWall.edge_subset_frontier D.target 0 hkSedge
  have hPnv : (D.tile eS.1).pts kS ∉ Set.range D.target.pts := by
    rintro ⟨m, hm⟩
    have hsP : Row2.tau D.target ((D.tile eS.1).pts kS) = s := hkSt.trans hs.symm
    rcases (show m = 0 ∨ m = 1 ∨ m = 2 by fin_cases m <;> simp) with rfl | rfl | rfl
    · rw [← hm, Row2.tau_A] at hsP; linarith
    · rw [← hm, Row2.tau_B] at hsP; linarith
    · have h2 := (Row2.edge0_coord D.target hkSedge).1
      rw [← hm] at h2
      have h1 : D.target.basis.coord 2 (D.target.pts 2) = 1 := D.target.basis.coord_apply_eq 2
      rw [h1] at h2; exact one_ne_zero h2
  have hsum := Erdos634.PinPlumbing.pin_angle_sum D.toDissection hPfr hPnv
  have hS : (D.tile eS.1).localAngle ((D.tile eS.1).pts kS) = D.model.angleAt 2 := by
    rw [(D.tile eS.1).localAngle_vertex kS]; exact hkS
  have h' : (D.tile e'.1).localAngle ((D.tile eS.1).pts kS) = D.model.angleAt 2 := by
    rw [← hP, (D.tile e'.1).localAngle_vertex k']; exact hk'
  have h2π := Row2.angle2_lt_pi D.model
  refine Row2.two_gamma (fun i => (D.tile i).localAngle ((D.tile eS.1).pts kS))
    (θ0 := D.model.angleAt 0) (θ1 := D.model.angleAt 1)
    (fun i => (D.tile i).localAngle_nonneg _) ?_ hsum D.model.angleAt_sum h12 htiles hS h'
  intro i hi
  have hi' : (D.tile i).localAngle ((D.tile eS.1).pts kS) ≠ 0 := hi
  show D.model.angleAt 0 ≤ (D.tile i).localAngle ((D.tile eS.1).pts kS)
  have hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = D.model.angleAt 0 := rfl
  have hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = D.model.angleAt 1 := rfl
  have hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = D.model.angleAt 2 := rfl
  have hv := Dissection.congruentDissection_localAngle_mem_boundary D
    (D.model.angleAt 0) (D.model.angleAt 1) (D.model.angleAt 2) hα' hβ' hγ' hPfr hPnv i
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with h | h | h | h | h
  · rw [h]
  · rw [h]; linarith
  · rw [h]; linarith
  · rw [h]; linarith
  · exact absurd h hi'

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Row2.lemmaR_gen

namespace Erdos634.Draft.LaczFormal

open Real Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
  Erdos634.Draft.LemmaCFinal

theorem sqrt3_indep {u v : ℝ} (hu : ∃ r : ℚ, u = r) (hv : ∃ r : ℚ, v = r) (h : u + v * Real.sqrt 3 = 0) :
    u = 0 ∧ v = 0 := by
  have h3 : ¬ IsSquare 3 := by
    rintro ⟨m, hm⟩
    have : m ≤ 2 := by nlinarith
    interval_cases m <;> omega
  have hirr : Irrational (Real.sqrt 3) := by
    have := irrational_sqrt_natCast_iff.mpr h3
    simpa using this
  obtain ⟨ru, rfl⟩ := hu
  obtain ⟨rv, rfl⟩ := hv
  by_cases hv0 : rv = 0
  · subst hv0; simp at h; simp [h]
  · exfalso
    apply hirr
    refine ⟨-ru / rv, ?_⟩
    have : (rv : ℝ) ≠ 0 := by exact_mod_cast hv0
    push_cast
    field_simp
    linarith

theorem iv_arith {N A0 B0 A1 B1 A2 B2 : ℕ} {u : ℝ}
    (hNu : (N : ℝ) = 2 * u ^ 2)
    (e0 : u = A0 + B0 * Real.sqrt 3) (e1 : (A1 : ℝ) + B1 * Real.sqrt 3 = Real.sqrt 3 * u)
    (e2 : (A2 : ℝ) + B2 * Real.sqrt 3 = 2 * u) : (B0 = 0 ∧ B2 = 0) ∨ B1 = 0 := by
  have s2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  set s := Real.sqrt 3 with hs
  have hAB : (A0 : ℝ) * B0 = 0 := by
    have h : (((A0 : ℚ) ^ 2 + 3 * B0 ^ 2 - N / 2 : ℚ) : ℝ) + (((2 * A0 * B0 : ℚ)) : ℝ) * s = 0 := by
      push_cast
      have : (N : ℝ) / 2 = u ^ 2 := by rw [hNu]; ring
      rw [e0] at this
      linear_combination (-1 : ℝ) * this - (B0 : ℝ) ^ 2 * s2
    obtain ⟨-, h2⟩ := sqrt3_indep ⟨_, rfl⟩ ⟨_, rfl⟩ h
    have : ((2 * A0 * B0 : ℚ) : ℝ) = 0 := h2
    push_cast at this
    linarith
  rcases mul_eq_zero.mp hAB with ha | hb
  · -- A0 = 0 : u = B0 s, then B1 = 0
    right
    have hA0 : A0 = 0 := by exact_mod_cast ha
    have h : (((A1 : ℚ) - 3 * B0 : ℚ) : ℝ) + ((B1 : ℚ) : ℝ) * s = 0 := by
      push_cast
      rw [hA0] at e0; simp at e0
      rw [e0] at e1
      linear_combination e1 + (B0 : ℝ) * s2
    obtain ⟨-, h2⟩ := sqrt3_indep ⟨_, rfl⟩ ⟨_, rfl⟩ h
    exact_mod_cast h2
  · left
    have hB0 : B0 = 0 := by exact_mod_cast hb
    refine ⟨hB0, ?_⟩
    have h : (((A2 : ℚ) - 2 * A0 : ℚ) : ℝ) + ((B2 : ℚ) : ℝ) * s = 0 := by
      push_cast
      rw [hB0] at e0; simp at e0
      rw [e0] at e2
      linarith
    obtain ⟨-, h2⟩ := sqrt3_indep ⟨_, rfl⟩ ⟨_, rfl⟩ h
    exact_mod_cast h2

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.iv_arith

namespace Erdos634.Draft.LaczFormal

open Real Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
  Erdos634.Draft.LemmaCFinal

set_option maxHeartbeats 1600000 in
/-- **Tail case (iv) of Laczkovich 1995 Thm 5.3.**  No congruent dissection of the triangle with angles `(π/6, π/3, π/2)` has a tile with
angles `(π/6, π/6, 2π/3)`.  (Role: with Thm 5.1 this excludes case (iv) for congruent tiles.) -/
theorem tail_iv {N : ℕ} (D : CongruentDissection N)
    (hM : TileAngles D (π / 6) (π / 6) (2 * π / 3)) (hT : TgtAngles D (π / 6) (π / 3) (π / 2)) : False := by
  obtain ⟨σm, m0, m1, m2⟩ := hM
  obtain ⟨σt, t0, t1, t2⟩ := hT
  let D' : CongruentDissection N :=
    { toDissection := Erdos634.NormalPosition.relabelTarget D.toDissection σt
      model := D.model.relabel σm
      tiles_congruent := fun i => (D.tiles_congruent i).relabel σm }
  have hTa := Row2.angleAt_comp D.target D'.target σt (fun k => rfl)
  have hMa := Row2.angleAt_comp D.model D'.model σm (fun k => rfl)
  have a0 : D'.model.angleAt 0 = π / 6 := by rw [(hMa 0).1]; exact m0
  have a1 : D'.model.angleAt 1 = π / 6 := by rw [(hMa 1).1]; exact m1
  have a2 : D'.model.angleAt 2 = 2 * π / 3 := by rw [(hMa 2).1]; exact m2
  have b0 : D'.target.angleAt 0 = π / 6 := by rw [(hTa 0).1]; exact t0
  have b1 : D'.target.angleAt 1 = π / 3 := by rw [(hTa 1).1]; exact t1
  have b2 : D'.target.angleAt 2 = π / 2 := by rw [(hTa 2).1]; exact t2
  have hpi := Real.pi_pos
  have s6 : Real.sin (π / 6) = 1 / 2 := Real.sin_pi_div_six
  have s3 : Real.sin (π / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
  have s23 : Real.sin (2 * π / 3) = Real.sqrt 3 / 2 := by
    rw [show 2 * π / 3 = π - π / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]
  have hp3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h33 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hv0 := D'.model.oppLen_pos 0
  have hw0 := D'.target.oppLen_pos 0
  have v1 : D'.model.oppLen 1 = D'.model.oppLen 0 := by
    have h := D'.model.lawSin 0 1
    rw [a0, a1, s6] at h; linarith
  have v2 : D'.model.oppLen 2 = Real.sqrt 3 * D'.model.oppLen 0 := by
    have h := D'.model.lawSin 0 2
    rw [a0, a2, s6, s23] at h; linarith
  have w1 : D'.target.oppLen 1 = Real.sqrt 3 * D'.target.oppLen 0 := by
    have h := D'.target.lawSin 0 1
    rw [b0, b1, s6, s3] at h; linarith
  have w2 : D'.target.oppLen 2 = 2 * D'.target.oppLen 0 := by
    have h := D'.target.lawSin 0 2
    rw [b0, b2, s6, Real.sin_pi_div_two] at h; linarith
  -- area
  have harea := Row3.RP.abs_det_target D'
  rw [Row3.RP.abs_det_eq, Row3.RP.abs_det_eq, b0, a0, s6, w1, w2, v1, v2] at harea
  have hN : (N : ℝ) = 2 * (D'.target.oppLen 0 / D'.model.oppLen 0) ^ 2 := by
    field_simp
    have : Real.sqrt 3 * (2 * D'.target.oppLen 0 ^ 2 - N * D'.model.oppLen 0 ^ 2) = 0 := by
      linear_combination 2 * harea
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hp3.ne'
    · linarith
  -- side equations
  have hrow := fun j => D'.sideCountT_sum j
  have r0 := hrow 0
  have r1 := hrow 1
  have r2 := hrow 2
  rw [Fin.sum_univ_three, v1, v2] at r0 r1 r2
  have e0 : D'.target.oppLen 0 / D'.model.oppLen 0 =
      ((D'.sideCountT 0 0 + D'.sideCountT 0 1 : ℕ) : ℝ) + (D'.sideCountT 0 2 : ℝ) * Real.sqrt 3 := by
    rw [div_eq_iff hv0.ne']; push_cast; linarith
  have e1 : ((D'.sideCountT 1 0 + D'.sideCountT 1 1 : ℕ) : ℝ) + (D'.sideCountT 1 2 : ℝ) * Real.sqrt 3 =
      Real.sqrt 3 * (D'.target.oppLen 0 / D'.model.oppLen 0) := by
    have key : (((D'.sideCountT 1 0 + D'.sideCountT 1 1 : ℕ) : ℝ) + (D'.sideCountT 1 2 : ℝ) * Real.sqrt 3) *
        D'.model.oppLen 0 = Real.sqrt 3 * D'.target.oppLen 0 := by
      push_cast; linear_combination r1 + w1
    field_simp
    linear_combination key
  have e2 : ((D'.sideCountT 2 0 + D'.sideCountT 2 1 : ℕ) : ℝ) + (D'.sideCountT 2 2 : ℝ) * Real.sqrt 3 =
      2 * (D'.target.oppLen 0 / D'.model.oppLen 0) := by
    have key : (((D'.sideCountT 2 0 + D'.sideCountT 2 1 : ℕ) : ℝ) + (D'.sideCountT 2 2 : ℝ) * Real.sqrt 3) *
        D'.model.oppLen 0 = 2 * D'.target.oppLen 0 := by
      push_cast; linear_combination r2 + w2
    field_simp
    linear_combination key
  have hne0 : D'.model.oppLen 0 ≠ D'.model.oppLen 2 := by
    rw [v2]; intro h
    have : (1 - Real.sqrt 3) * D'.model.oppLen 0 = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · have : Real.sqrt 3 > 1 := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      linarith
    · exact hv0.ne' h'
  have hne1 : D'.model.oppLen 1 ≠ D'.model.oppLen 2 := by rw [v1]; exact hne0
  have h01 : D'.model.angleAt 0 ≤ D'.model.angleAt 1 := by rw [a0, a1]
  have h12 : D'.model.angleAt 1 < D'.model.angleAt 2 := by rw [a1, a2]; linarith
  have hcase := iv_arith (N := N) (u := D'.target.oppLen 0 / D'.model.oppLen 0) hN e0 e1 e2
  rcases hcase with ⟨-, hB2⟩ | hB1
  · have hR := Row2.lemmaR_gen D' (by rw [b0, a2]; linarith) (by rw [b1, a2]; linarith) h01 h12
      (noc_of_sideCountT D' hne0 hne1 hB2)
    rw [a2] at hR; linarith
  · -- relabel the target by swapping vertices 1 and 2
    let Dc : CongruentDissection N :=
      { toDissection := Erdos634.NormalPosition.relabelTarget D'.toDissection (Equiv.swap 1 2)
        model := D'.model
        tiles_congruent := D'.tiles_congruent }
    have hTc := Row2.angleAt_comp D'.target Dc.target (Equiv.swap 1 2) (fun k => rfl)
    have t0c : Dc.target.angleAt 0 = π / 6 := by
      rw [(hTc 0).1, show (Equiv.swap (1 : Fin 3) 2) 0 = 0 by decide]; exact b0
    have t1c : Dc.target.angleAt 1 = π / 2 := by
      rw [(hTc 1).1, show (Equiv.swap (1 : Fin 3) 2) 1 = 2 by decide]; exact b2
    have hedge : Dc.target.edge 0 = D'.target.edge 2 := by
      show segment ℝ (D'.target.pts ((Equiv.swap (1 : Fin 3) 2) 0))
        (D'.target.pts ((Equiv.swap (1 : Fin 3) 2) (0 + 1))) =
        segment ℝ (D'.target.pts 2) (D'.target.pts (2 + 1))
      rw [show (Equiv.swap (1 : Fin 3) 2) 0 = 0 by decide,
        show (Equiv.swap (1 : Fin 3) 2) (0 + 1) = 2 by decide, show (2 : Fin 3) + 1 = 0 from rfl]
      exact segment_symm ℝ _ _
    have hnoc : ∀ e ∈ Dc.sideEdges 0, Dc.eLen e ≠ Dc.model.oppLen 2 := by
      intro e he heq
      have he1 : e ∈ D'.sideEdges 2 := by
        unfold Dissection.sideEdges at he ⊢
        rw [Finset.mem_filter] at he ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        have := he.2
        rw [hedge] at this
        exact this
      have hty : D'.eType e = 2 := by
        have h' := D'.eLen_eType e
        have : D'.eLen e = D'.model.oppLen 2 := heq
        rcases (show D'.eType e = 0 ∨ D'.eType e = 1 ∨ D'.eType e = 2 by
          generalize D'.eType e = k; fin_cases k <;> simp) with h'' | h'' | h''
        · rw [h''] at h'; exact absurd (h'.symm.trans this) hne0
        · rw [h''] at h'; exact absurd (h'.symm.trans this) hne1
        · exact h''
      have hcard : 0 < D'.sideCountT 1 2 := by
        unfold CongruentDissection.sideCountT
        rw [show (1 : Fin 3) + 1 = 2 from rfl]
        exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he1, hty⟩⟩
      omega
    have hR := Row2.lemmaR_gen Dc (by rw [t0c]; show π / 6 < D'.model.angleAt 2; rw [a2]; linarith)
      (by rw [t1c]; show π / 2 < D'.model.angleAt 2; rw [a2]; linarith) h01 h12 hnoc
    have : 2 * D'.model.angleAt 2 = π := hR
    rw [a2] at this; linarith

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.tail_iv

namespace Erdos634.Draft.LaczFormal

open Real Erdos634.Geometry Erdos634.TilePlacement Erdos634.Subdivision Erdos634.Draft.TheoremPConditional

/-- The two hypotheses of `tail_iv` are individually satisfiable: a dissection with target angles `(π/6, π/3, π/2)` exists (ladder of a
30-60-90 tile) and a dissection by the `(π/6, π/6, 2π/3)` tile exists (`equilateral_tile_ii_witness`, N = 3); `tail_iv` says they never
hold together. -/
theorem tail_iv_hyps_individually :
    (∃ (N : ℕ) (D : CongruentDissection N), TgtAngles D (π / 6) (π / 3) (π / 2)) ∧
    (∃ (N : ℕ) (D : CongruentDissection N), TileAngles D (π / 6) (π / 6) (2 * π / 3)) := by
  refine ⟨?_, ?_⟩
  · have hpi := Real.pi_pos
    obtain ⟨T, h0, h1⟩ := exists_tri_angles (α := π / 6) (β := π / 3) (by positivity) (by positivity)
      (by linarith)
    have h2 : T.angleAt 2 = π / 2 := by
      have := angleAt_sum T; rw [h0, h1] at this; linarith
    have hpts : (![T.pts 0, T.pts 1, T.pts 2] : Fin 3 → Plane) = T.pts := by
      funext i; fin_cases i <;> rfl
    have hind : AffineIndependent ℝ ![T.pts 0, T.pts 1, T.pts 2] := by rw [hpts]; exact T.indep
    set Tm : Tri := ⟨![T.pts 0, T.pts 1, T.pts 2], hind⟩ with hTm
    have hang : ∀ k, Tm.angleAt k = T.angleAt k := by
      intro k
      have : Tm.pts = T.pts := hpts
      simp only [Tri.angleAt, this]
    let D : CongruentDissection (2 * 2) :=
      { toDissection := ladderDissection (T.pts 0) (T.pts 1) (T.pts 2) hind 2 (by norm_num)
        model := Tm
        tiles_congruent := fun n =>
          (ladderDissection_congruent (T.pts 0) (T.pts 1) (T.pts 2) hind 2 (by norm_num) n).symm }
    refine ⟨_, D, 1, ?_, ?_, ?_⟩
    · show (bigTri (T.pts 0) (T.pts 1) (T.pts 2) hind 2 (by norm_num)).angleAt 0 = _
      rw [bigTri_angleAt]; exact h0
    · show (bigTri (T.pts 0) (T.pts 1) (T.pts 2) hind 2 (by norm_num)).angleAt 1 = _
      rw [bigTri_angleAt]; exact h1
    · show (bigTri (T.pts 0) (T.pts 1) (T.pts 2) hind 2 (by norm_num)).angleAt 2 = _
      rw [bigTri_angleAt]; exact h2
  · obtain ⟨N, D, -, h⟩ := equilateral_tile_ii_witness
    exact ⟨N, D, h⟩

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.tail_iv_hyps_individually

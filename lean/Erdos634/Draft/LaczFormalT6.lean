-- Draft/LaczFormalT6.lean -- killing the last unresolved model of `LaczFormalT4.similar_partial`: the 30-30-120 triangle
-- (N = 3m^2) is not a similar-reptile model.  Two ingredients, both new here:
--  (1) `Row2.lemmaR_le`: `Row2.lemmaR` (Draft/FluxERow2R.lean) re-run with the hypothesis `angleAt 0 < angleAt 1`
--      weakened to `angleAt 0 <= angleAt 1` (the only use of it is a `linarith` for `angleAt 0 < angleAt 2`), so it applies
--      to isosceles models;  its conclusion is `2*gamma = pi` when the side AB carries no gamma-length edge;
--  (2) the base row of the side matrix at the model (1, 1, sqrt 3): `X + Y*sqrt 3 = mu*sqrt 3`, `mu^2 = N`, `mu` irrational
--      force `Y = 0`, i.e. the base carries no `c`-edge;  then `2*(2pi/3) = pi` is absurd.
-- UNAUDITED.  Credit: Snover-Waiveris-Williams, Beeson (Triangle tiling I, Lemma 11 = Lemma R), Beeson-Rosu.
import Erdos634.Draft.LaczFormalT5
import Erdos634.Draft.FluxERow2R

open scoped Classical

namespace Erdos634.Geometry

open Real

variable {N : ℕ}

/-- `Row2.lemmaR` with `angleAt 0 ≤ angleAt 1` (isosceles allowed). -/
theorem Row2.lemmaR_le (D : CongruentDissection N)
    (hang : ∀ k, D.target.angleAt k = D.model.angleAt k)
    (h01 : D.model.angleAt 0 ≤ D.model.angleAt 1) (h12 : D.model.angleAt 1 < D.model.angleAt 2)
    (hnoc : ∀ e ∈ D.sideEdges 0, D.eLen e ≠ D.model.oppLen 2) :
    2 * D.model.angleAt 2 = π := by
  classical
  have A_mem : D.target.pts 0 ∈ D.target.edge 0 := left_mem_segment ℝ _ _
  have B_mem : D.target.pts 1 ∈ D.target.edge 0 := right_mem_segment ℝ _ _
  have hnA : ∀ i k, (D.tile i).angleAt k = D.model.angleAt 2 →
      (D.tile i).pts k ≠ D.target.pts 0 :=
    fun i k hk => Row2.no_gamma_corner D 0 i k hk (by rw [hang 0]; linarith)
  have hnB : ∀ i k, (D.tile i).angleAt k = D.model.angleAt 2 →
      (D.tile i).pts k ≠ D.target.pts 1 :=
    fun i k hk => Row2.no_gamma_corner D 1 i k hk (by rw [hang 1]; exact h12)
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

#print axioms Erdos634.Geometry.Row2.lemmaR_le

namespace Erdos634.Draft.LaczFormal

open Real Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
  Erdos634.Draft.LemmaCFinal

theorem thirty_arith {N X Y : ℕ} {μ : ℝ} (hNm : μ ^ 2 = N) (hμq : ¬ ∃ r : ℚ, μ = r)
    (h : (X : ℝ) + Y * Real.sqrt 3 = μ * Real.sqrt 3) : Y = 0 := by
  have h3 : ¬ IsSquare 3 := by
    rintro ⟨m, hm⟩
    have : m ≤ 2 := by nlinarith
    interval_cases m <;> omega
  have hirr : Irrational (Real.sqrt 3) := by
    have := irrational_sqrt_natCast_iff.mpr h3
    simpa using this
  have s2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hμ : μ = (X : ℝ) / 3 * Real.sqrt 3 + Y := by
    have : μ * Real.sqrt 3 * Real.sqrt 3 = ((X : ℝ) + Y * Real.sqrt 3) * Real.sqrt 3 := by rw [h]
    have h33 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    linear_combination (1 / 3) * this - ((μ - Y) / 3) * h33
  by_contra hY
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast Nat.pos_of_ne_zero hY
  by_cases hX : X = 0
  · exact hμq ⟨Y, by rw [hμ, hX]; simp⟩
  have hXpos : (0 : ℝ) < X := by exact_mod_cast Nat.pos_of_ne_zero hX
  have hc : 0 < 2 * (X : ℝ) * Y / 3 := by positivity
  apply hirr
  refine ⟨((N : ℚ) - (X : ℚ) ^ 2 / 3 - (Y : ℚ) ^ 2) / (2 * (X : ℚ) * Y / 3), ?_⟩
  push_cast
  rw [div_eq_iff hc.ne']
  have hN' : (N : ℝ) = ((X : ℝ) / 3 * Real.sqrt 3 + Y) ^ 2 := by rw [← hμ, hNm]
  linear_combination hN' + ((X : ℝ) / 3) ^ 2 * s2

theorem noc_of_sideCountT {N : ℕ} (D : CongruentDissection N)
    (hv0 : D.model.oppLen 0 ≠ D.model.oppLen 2) (hv1 : D.model.oppLen 1 ≠ D.model.oppLen 2)
    (h : D.sideCountT 2 2 = 0) : ∀ e ∈ D.sideEdges 0, D.eLen e ≠ D.model.oppLen 2 := by
  intro e he heq
  have hty : D.eType e = 2 := by
    by_contra hne
    have := D.eLen_eType e
    rcases (show D.eType e = 0 ∨ D.eType e = 1 ∨ D.eType e = 2 by
      generalize D.eType e = k; fin_cases k <;> simp) with h' | h' | h'
    · rw [h'] at this; exact hv0 (this.symm.trans heq)
    · rw [h'] at this; exact hv1 (this.symm.trans heq)
    · exact hne h'
  have hcard : 0 < D.sideCountT 2 2 := by
    unfold CongruentDissection.sideCountT
    rw [show (2 : Fin 3) + 1 = 0 from rfl]
    exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hty⟩⟩
  omega

/-- **The 30-30-120 triangle is not a similar-reptile model** (N non-square). -/
theorem kill_30_30_120 {N : ℕ} (D : CongruentDissection N) (μ : ℝ)
    (hsim : ∀ k, D.target.angleAt k = D.model.angleAt k ∧ D.target.oppLen k = μ * D.model.oppLen k)
    (hN : ¬ IsSquare N) (hT : TileAngles D (π / 6) (π / 6) (2 * π / 3)) : False := by
  obtain ⟨σ, h0, h1, h2⟩ := hT
  let D' : CongruentDissection N :=
    { toDissection := Erdos634.NormalPosition.relabelTarget D.toDissection σ
      model := D.model.relabel σ
      tiles_congruent := fun i => (D.tiles_congruent i).relabel σ }
  have hTa := Row2.angleAt_comp D.target D'.target σ (fun k => rfl)
  have hMa := Row2.angleAt_comp D.model D'.model σ (fun k => rfl)
  have hsim' : ∀ k, D'.target.angleAt k = D'.model.angleAt k ∧
      D'.target.oppLen k = μ * D'.model.oppLen k := by
    intro k
    rw [(hTa k).1, (hMa k).1, (hTa k).2, (hMa k).2]
    exact hsim (σ k)
  have a0 : D'.model.angleAt 0 = π / 6 := by rw [(hMa 0).1]; exact h0
  have a1 : D'.model.angleAt 1 = π / 6 := by rw [(hMa 1).1]; exact h1
  have a2 : D'.model.angleAt 2 = 2 * π / 3 := by rw [(hMa 2).1]; exact h2
  have hside : ∀ k, D'.target.oppLen k = μ * D'.model.oppLen k := fun k => (hsim' k).2
  obtain ⟨⟨hNμ, hμq⟩, -⟩ := similar_reduction D' μ hsim' hN
  have hpi := Real.pi_pos
  have s6 : Real.sin (π / 6) = 1 / 2 := Real.sin_pi_div_six
  have s23 : Real.sin (2 * π / 3) = Real.sqrt 3 / 2 := by
    rw [show 2 * π / 3 = π - π / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]
  have hp3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hv0 := D'.model.oppLen_pos 0
  have v1 : D'.model.oppLen 1 = D'.model.oppLen 0 := by
    have h := D'.model.lawSin 0 1
    rw [a0, a1, s6] at h
    linarith
  have v2 : D'.model.oppLen 2 = Real.sqrt 3 * D'.model.oppLen 0 := by
    have h := D'.model.lawSin 0 2
    rw [a0, a2, s6, s23] at h
    linarith
  have hrow := Row2.sideCountT_eigen D' μ hside 2
  rw [Fin.sum_univ_three, v1, v2] at hrow
  have hY : D'.sideCountT 2 2 = 0 := by
    refine thirty_arith (N := N) (X := D'.sideCountT 2 0 + D'.sideCountT 2 1) hNμ.symm hμq ?_
    push_cast
    have := mul_right_cancel₀ hv0.ne' (by nlinarith [hrow] :
      ((↑(D'.sideCountT 2 0) + ↑(D'.sideCountT 2 1)) + ↑(D'.sideCountT 2 2) * Real.sqrt 3) * D'.model.oppLen 0
        = (μ * Real.sqrt 3) * D'.model.oppLen 0)
    linarith
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
  have hR := Row2.lemmaR_le D' (fun k => (hsim' k).1) (by rw [a0, a1])
    (by rw [a1, a2]; linarith) (noc_of_sideCountT D' hne0 hne1 hY)
  rw [a2] at hR
  linarith

/-- **Reptile theorem, partial, third form**: every similar tiling with non-square N has a right tile with
`N = A²+B²`, or a 30-60-90 tile with `N = 3m²`.  This is the Snover-Waiveris-Williams / Beeson-Rosu Theorem 5
(non-square case) except that the right triangle's leg ratio `A : B` is not stated. -/
theorem similar_reptile {N : ℕ} (D : CongruentDissection N) (μ : ℝ)
    (hsim : ∀ k, D.target.angleAt k = D.model.angleAt k ∧ D.target.oppLen k = μ * D.model.oppLen k)
    (hN : ¬ IsSquare N) :
    (∃ A B : ℕ, N = A ^ 2 + B ^ 2 ∧ RightLegs D A B) ∨
    ((∃ m : ℕ, N = 3 * m ^ 2) ∧ TileAngles D (π / 6) (π / 3) (π / 2)) := by
  rcases similar_partial2 D μ hsim hN with h | h | ⟨-, hT⟩
  · exact Or.inl h
  · exact Or.inr h
  · exact (kill_30_30_120 D μ hsim hN hT).elim

/-- **The reptile theorem (Snover-Waiveris-Williams 1991; Beeson-Rosu Thm 5), any `N`, any similarity.**
If the target of a congruent dissection is similar to the tile (any vertex correspondence), then `N` is a perfect
square, or the tile is a right triangle with legs in ratio `A : B` and `N = A² + B²`, or the tile is the 30-60-90 triangle
and `N = 3m²`. -/
theorem reptile_SWW {N : ℕ} (D : CongruentDissection N) (hs : SimilarTM D) :
    IsSquare N ∨ (∃ A B : ℕ, N = A ^ 2 + B ^ 2 ∧ RightLegs D A B) ∨
    ((∃ m : ℕ, N = 3 * m ^ 2) ∧ TileAngles D (π / 6) (π / 3) (π / 2)) := by
  by_cases hN : IsSquare N
  · exact Or.inl hN
  right
  obtain ⟨μ, τ, h⟩ := hs
  have hMa := Row2.angleAt_comp D.model (D.relabelModel τ).model τ (fun k => rfl)
  have hsim : ∀ k, (D.relabelModel τ).target.angleAt k = (D.relabelModel τ).model.angleAt k ∧
      (D.relabelModel τ).target.oppLen k = μ * (D.relabelModel τ).model.oppLen k := fun k => by
    rw [(hMa k).1, (hMa k).2]; exact h k
  rcases similar_reptile (D.relabelModel τ) μ hsim hN with ⟨A, B, hAB, i, j, k, hij, hik, hjk, hk, hl⟩ |
    ⟨m, σ, h0, h1, h2⟩
  · exact Or.inl ⟨A, B, hAB, τ i, τ j, τ k, τ.injective.ne hij, τ.injective.ne hik, τ.injective.ne hjk,
      by rw [← (hMa k).1]; exact hk, by rw [← (hMa i).2, ← (hMa j).2]; exact hl⟩
  · refine Or.inr ⟨m, σ.trans τ, ?_, ?_, ?_⟩
    · rw [Equiv.trans_apply, ← (hMa (σ 0)).1]; exact h0
    · rw [Equiv.trans_apply, ← (hMa (σ 1)).1]; exact h1
    · rw [Equiv.trans_apply, ← (hMa (σ 2)).1]; exact h2

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.reptile_SWW
#print axioms Erdos634.Draft.LaczFormal.kill_30_30_120
#print axioms Erdos634.Draft.LaczFormal.similar_reptile

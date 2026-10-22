-- Draft/H1gPosStep.lean — ATOM H1.g (position half): sub-atoms P3/P4/P5 assembled.
--   `chains_coset`   : a near-side and a far-side chain edge on one line, meeting in a point, have all
--                      four endpoints in one coset `P + edgeGroup`  (P = start of the common wall run).
--   `adj_coset`      : adjacent tiles have all six corners in one coset `P + edgeGroup`.
--   `L1_pos`         : all tile vertices of a dissection lie in one coset of the edge group.
-- Formalization debt; NOT /goal progress.  Standard axioms, no sorry.
import Erdos634.Draft.H1gPosCover
import Erdos634.Draft.H1fNGEdge

open Set

namespace Erdos634.H1gPos

open Erdos634.Geometry Erdos634.H1fNG

variable {N : ℕ}

theorem endpoints_mem {D : Dissection N} {d O : Plane} (hd : d ≠ 0) {e : Fin N × Fin 3}
    (he : OnLine D O d e) {p : ℝ} (hlo : (eLo D O d e - p) • d ∈ edgeGroup D) :
    (D.tile e.1).pts e.2 - pt O d p ∈ edgeGroup D ∧
      (D.tile e.1).pts (e.2 + 1) - pt O d p ∈ edgeGroup D := by
  obtain ⟨h1, h2⟩ := pts_eq_pt hd he
  have hhl := hi_sub_lo_mem hd he
  have key : ∀ v : ℝ, (v = eLo D O d e ∨ v = eHi D O d e) → (pt O d v - pt O d p ∈ edgeGroup D) := by
    intro v hv
    have e1 : pt O d v - pt O d p = (v - p) • d := by simp only [pt]; module
    rw [e1]
    rcases hv with rfl | rfl
    · exact hlo
    · have : (eHi D O d e - p) • d = (eHi D O d e - eLo D O d e) • d + (eLo D O d e - p) • d := by
        module
      rw [this]; exact (edgeGroup D).add_mem hhl hlo
  have hc : (eA D O d e = eLo D O d e ∧ eB D O d e = eHi D O d e) ∨
      (eA D O d e = eHi D O d e ∧ eB D O d e = eLo D O d e) := by
    unfold eLo eHi
    rcases le_total (eA D O d e) (eB D O d e) with h | h
    · left; exact ⟨(min_eq_left h).symm, (max_eq_right h).symm⟩
    · right; exact ⟨(max_eq_left h).symm, (min_eq_right h).symm⟩
  rw [h1, h2]
  rcases hc with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact ⟨key _ (Or.inl ha), key _ (Or.inr hb)⟩
  · exact ⟨key _ (Or.inr ha), key _ (Or.inl hb)⟩

/-- The intervals of a chain have pairwise disjoint interiors. -/
theorem chain_disj {D : Dissection N} {d O : Plane} (hd : d ≠ 0) {f : Plane →ₗ[ℝ] ℝ} {c : ℝ}
    (hf : f ≠ 0) (hon : ∀ e ∈ D.lineChain f c, OnLine D O d e) :
    ∀ k ∈ D.lineChain f c, ∀ k' ∈ D.lineChain f c, k ≠ k' →
      Disjoint (Ioo (eLo D O d k) (eHi D O d k)) (Ioo (eLo D O d k') (eHi D O d k')) := by
  intro k hk k' hk' hne
  refine open_disjoint hd (hon k hk) (hon k' hk') ?_
  obtain ⟨-, -, hle1⟩ := Dissection.mem_lineChain.mp hk
  obtain ⟨-, -, hle2⟩ := Dissection.mem_lineChain.mp hk'
  exact D.sameside_edges_subsingleton f c hf hne
    ((D.tile k.1).carrier_subset_halfplane f c hle1)
    ((D.tile k'.1).carrier_subset_halfplane f c hle2)
    (D.lineChain_edge_subset hk) (D.lineChain_edge_subset hk')

/-- **Opposite-side chain edges on one line, meeting in a point, lie in one coset.** -/
theorem line_chain_coset {D : Dissection N} {d O r : Plane} (hd : d ≠ 0)
    (hr : r ∈ interior D.target.carrier) (hrl : cross d (r - O) = 0)
    {e e' : Fin N × Fin 3} (he : e ∈ D.lineChain (crossL d) (cross d O))
    (he' : e' ∈ D.lineChain (-(crossL d)) (-(cross d O)))
    {z : Plane} (hz : z ∈ (D.tile e.1).edge e.2) (hz' : z ∈ (D.tile e'.1).edge e'.2) :
    ∃ P : Plane, (D.tile e.1).pts e.2 - P ∈ edgeGroup D ∧
      (D.tile e.1).pts (e.2 + 1) - P ∈ edgeGroup D ∧
      (D.tile e'.1).pts e'.2 - P ∈ edgeGroup D ∧
      (D.tile e'.1).pts (e'.2 + 1) - P ∈ edgeGroup D := by
  classical
  have hf : crossL d ≠ 0 := crossL_ne_zero hd
  have hf' : (-(crossL d) : Plane →ₗ[ℝ] ℝ) ≠ 0 := fun h => hf (neg_eq_zero.mp h)
  have hon : ∀ x ∈ D.lineChain (crossL d) (cross d O), OnLine D O d x :=
    fun x hx => onLine_of_mem_lineChain hx
  have hon' : ∀ x ∈ D.lineChain (-(crossL d)) (-(cross d O)), OnLine D O d x :=
    fun x hx => onLine_of_mem_lineChain_neg hx
  have hone := hon e he
  have hone' := hon' e' he'
  let M := edgeGroup D
  let R : ℝ → ℝ → Prop := fun a b => (a - b) • d ∈ M
  have hsymm : ∀ a b, R a b → R b a := by
    intro a b h
    have := M.neg_mem h
    show (b - a) • d ∈ M
    convert this using 1; module
  have htrans : ∀ a b c, R a b → R b c → R a c := by
    intro a b c h1 h2
    have := M.add_mem h1 h2
    show (a - c) • d ∈ M
    convert this using 1; module
  have hRp : ∀ k ∈ D.lineChain (crossL d) (cross d O), R (eHi D O d k) (eLo D O d k) :=
    fun k hk => hi_sub_lo_mem hd (hon k hk)
  have hRm : ∀ k ∈ D.lineChain (-(crossL d)) (-(cross d O)), R (eHi D O d k) (eLo D O d k) :=
    fun k hk => hi_sub_lo_mem hd (hon' k hk)
  obtain ⟨p₁, hp₁, hc₁, hs₁, hR₁⟩ := chain_start (D.lineChain (crossL d) (cross d O))
    (eLo D O d) (eHi D O d) (fun k hk => eLo_lt_eHi hd (hon k hk))
    (chain_disj hd hf hon) R hsymm htrans hRp e he
  obtain ⟨p₂, hp₂, hc₂, hs₂, hR₂⟩ := chain_start (D.lineChain (-(crossL d)) (-(cross d O)))
    (eLo D O d) (eHi D O d) (fun k hk => eLo_lt_eHi hd (hon' k hk))
    (chain_disj hd hf' hon') R hsymm htrans hRm e' he'
  -- common point z = pt t₀
  have hzl : cross d (z - O) = 0 := by
    have := D.lineChain_edge_subset he z hz
    simp only [crossL_apply] at this
    rw [cross_sub_right, this, sub_self]
  have hz0 : pt O d (pos O d z) = z := pt_pos hd hzl
  set t₀ := pos O d z
  have hzE : eLo D O d e ≤ t₀ ∧ t₀ ≤ eHi D O d e :=
    (pt_mem_edge_iff hd hone t₀).mp (by rw [hz0]; exact hz)
  have hzE' : eLo D O d e' ≤ t₀ ∧ t₀ ≤ eHi D O d e' :=
    (pt_mem_edge_iff hd hone' t₀).mp (by rw [hz0]; exact hz')
  have hsig := sig_iff (D := D) hd hr hrl
  -- transport the minus-side facts to the plus-side `Σ`
  have hs₂' : IsStart (D.lineChain (crossL d) (cross d O)) (eLo D O d) (eHi D O d) p₂ := by
    obtain ⟨ε, hε, h⟩ := hs₂
    exact ⟨ε, hε, fun t h1 h2 hh => h t h1 h2 ((hsig t).mp hh)⟩
  have hc₂' : ∀ t, p₂ ≤ t → t ≤ eLo D O d e' →
      InSig (D.lineChain (crossL d) (cross d O)) (eLo D O d) (eHi D O d) t :=
    fun t h1 h2 => (hsig t).mpr (hc₂ t h1 h2)
  have hpp : p₁ = p₂ := by
    rcases le_total (eLo D O d e) (eLo D O d e') with hle | hle
    · refine start_unique _ _ _ (x := eLo D O d e') ?_ hp₂ ?_ hc₂' hs₁ hs₂'
      · exact hp₁.trans hle
      · intro t h1 h2
        by_cases ht : t ≤ eLo D O d e
        · exact hc₁ t h1 ht
        · push Not at ht
          exact ⟨e, he, ht.le, h2.trans (hzE'.1.trans hzE.2)⟩
    · refine start_unique _ _ _ (x := eLo D O d e) hp₁ ?_ hc₁ ?_ hs₁ hs₂'
      · exact hp₂.trans hle
      · intro t h1 h2
        by_cases ht : t ≤ eLo D O d e'
        · exact hc₂' t h1 ht
        · push Not at ht
          exact (hsig t).mpr ⟨e', he', ht.le, h2.trans (hzE.1.trans hzE'.2)⟩
  subst hpp
  have hlo₁ : (eLo D O d e - p₁) • d ∈ M := by
    have := M.neg_mem hR₁
    convert this using 1; module
  have hlo₂ : (eLo D O d e' - p₁) • d ∈ M := by
    have := M.neg_mem hR₂
    convert this using 1; module
  obtain ⟨a1, a2⟩ := endpoints_mem hd hone hlo₁
  obtain ⟨b1, b2⟩ := endpoints_mem hd hone' hlo₂
  exact ⟨pt O d p₁, a1, a2, b1, b2⟩

/-- A tile in the half plane with its edge on the line: classification into the two chains. -/
theorem mem_chain_or (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0) (i : Fin N)
    (k : Fin 3) (h1 : f ((D.tile i).pts k) = c) (h2 : f ((D.tile i).pts (k + 1)) = c) :
    (i, k) ∈ D.lineChain f c ∨ (i, k) ∈ D.lineChain (-f) (-c) := by
  have h3 : ∀ m k : Fin 3, m = k ∨ m = k + 1 ∨ m = k + 2 := by decide
  have hne : f ((D.tile i).pts (k + 2)) ≠ c := by
    intro h
    exact two_vertices_on_line (D.tile i) f c hf (fun m => by
      rcases h3 m k with rfl | rfl | rfl
      exacts [h1, h2, h])
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · left
    rw [Dissection.mem_lineChain]
    refine ⟨h1, h2, fun m => ?_⟩
    rcases h3 m k with rfl | rfl | rfl
    exacts [h1.le, h2.le, hlt.le]
  · right
    rw [Dissection.mem_lineChain]
    refine ⟨by simp [h1], by simp [h2], fun m => ?_⟩
    simp only [LinearMap.neg_apply]
    rcases h3 m k with rfl | rfl | rfl
    · rw [h1]
    · rw [h2]
    · linarith

/-- An opposite-side pair of chain edges on one line yields a point of the target interior on it. -/
theorem exists_interior_on_line (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0)
    {e e' : Fin N × Fin 3} (he : e ∈ D.lineChain f c) (he' : e' ∈ D.lineChain (-f) (-c)) :
    ∃ r ∈ interior D.target.carrier, f r = c := by
  have hf' : (-f : Plane →ₗ[ℝ] ℝ) ≠ 0 := fun h => hf (neg_eq_zero.mp h)
  obtain ⟨-, -, hle⟩ := Dissection.mem_lineChain.mp he
  obtain ⟨-, -, hle'⟩ := Dissection.mem_lineChain.mp he'
  obtain ⟨p, hp⟩ := (D.tile e.1).interior_nonempty
  obtain ⟨q, hq⟩ := (D.tile e'.1).interior_nonempty
  have hp1 : f p < c := (D.tile e.1).interior_lt_of_le f c hf
    ((D.tile e.1).carrier_subset_halfplane f c hle) hp
  have hq1 : (-f) q < -c := (D.tile e'.1).interior_lt_of_le (-f) (-c) hf'
    ((D.tile e'.1).carrier_subset_halfplane (-f) (-c) hle') hq
  simp only [LinearMap.neg_apply] at hq1
  have hpT : p ∈ interior D.target.carrier := interior_mono (tile_subset_target D e.1) hp
  have hqT : q ∈ interior D.target.carrier := interior_mono (tile_subset_target D e'.1) hq
  have hden : 0 < f q - f p := by linarith
  set θ := (c - f p) / (f q - f p) with hθ
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hden.le
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hden]; linarith
  refine ⟨p + θ • (q - p), ?_, ?_⟩
  · have hconv := D.target.convex.interior
    have hmem : p + θ • (q - p) ∈ segment ℝ p q :=
      ⟨1 - θ, θ, by linarith, hθ0, by ring, by module⟩
    exact hconv.segment_subset hpT hqT hmem
  · rw [map_add, map_smul, map_sub, smul_eq_mul]
    have : θ * (f q - f p) = c - f p := by rw [hθ]; exact div_mul_cancel₀ _ hden.ne'
    rw [this]; ring

/-- **Opposite-side chain edges, meeting in a point, have all endpoints in one coset.** -/
theorem chains_coset {D : Dissection N} {d O : Plane} (hd : d ≠ 0)
    {e e' : Fin N × Fin 3} (he : e ∈ D.lineChain (crossL d) (cross d O))
    (he' : e' ∈ D.lineChain (-(crossL d)) (-(cross d O)))
    {z : Plane} (hz : z ∈ (D.tile e.1).edge e.2) (hz' : z ∈ (D.tile e'.1).edge e'.2) :
    ∃ P : Plane, (D.tile e.1).pts e.2 - P ∈ edgeGroup D ∧
      (D.tile e.1).pts (e.2 + 1) - P ∈ edgeGroup D ∧
      (D.tile e'.1).pts e'.2 - P ∈ edgeGroup D ∧
      (D.tile e'.1).pts (e'.2 + 1) - P ∈ edgeGroup D := by
  obtain ⟨r, hr, hfr⟩ := exists_interior_on_line D (crossL d) (cross d O) (crossL_ne_zero hd) he he'
  refine line_chain_coset hd hr ?_ he he' hz hz'
  simp only [crossL_apply] at hfr
  rw [cross_sub_right, hfr, sub_self]

theorem corners_of {D : Dissection N} {i : Fin N} {k : Fin 3} {P : Plane}
    (h : (D.tile i).pts k - P ∈ edgeGroup D) (a : Fin 3) : (D.tile i).pts a - P ∈ edgeGroup D := by
  have := (edgeGroup D).add_mem (corner_sub_mem D i a k) h
  convert this using 1; abel

/-- Two points of an edge of a tile lie in the edge: edge points have `f = c`. -/
theorem edge_f_eq {T : Tri} {k : Fin 3} {f : Plane →ₗ[ℝ] ℝ} {c : ℝ}
    (h1 : f (T.pts k) = c) (h2 : f (T.pts (k + 1)) = c) {y : Plane} (hy : y ∈ T.edge k) :
    f y = c := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, h1, h2, ← add_mul, hab, one_mul]

/-- **P4: adjacent tiles have all their corners in one coset of the edge group.** -/
theorem adj_coset (D : Dissection N) {i j : Fin N} (h : (nbrGraph D).Adj i j) :
    ∃ P : Plane, (∀ a, (D.tile i).pts a - P ∈ edgeGroup D) ∧
      ∀ a, (D.tile j).pts a - P ∈ edgeGroup D := by
  have hij : i ≠ j := h.1
  obtain ⟨k, l, u, v, huv, h1, h2⟩ := adj_shared_edge D h
  set d := (D.tile i).pts (k + 1) - (D.tile i).pts k with hdd
  set O := (D.tile i).pts k with hO
  have hd : d ≠ 0 := by
    rw [hdd, sub_ne_zero]
    intro h'
    have h3 := (D.tile i).indep.injective h'
    have h4 : ∀ m : Fin 3, m + 1 ≠ m := by decide
    exact h4 _ h3
  have hf : crossL d ≠ 0 := crossL_ne_zero hd
  have hf' : (-(crossL d) : Plane →ₗ[ℝ] ℝ) ≠ 0 := fun h => hf (neg_eq_zero.mp h)
  have hi1 : crossL d ((D.tile i).pts k) = cross d O := rfl
  have hi2 : crossL d ((D.tile i).pts (k + 1)) = cross d O := by
    have : (D.tile i).pts (k + 1) = O + d := by rw [hdd, hO]; abel
    rw [this, map_add]; simp only [crossL_apply, cross_self, add_zero]
  have hfE : ∀ y ∈ (D.tile i).edge k, crossL d y = cross d O := fun y hy => edge_f_eq hi1 hi2 hy
  have hfu : crossL d u = cross d O := hfE u (h1 (left_mem_segment ℝ u v))
  obtain ⟨r, hr0, hrd⟩ := edge_parallel_of_shared _ _ huv h1 h2
  set dj := (D.tile j).pts (l + 1) - (D.tile j).pts l with hdj
  have hfdj : crossL d dj = 0 := by
    have h0 : crossL d (r • dj) = 0 := by
      rw [← hrd]; exact cross_self d
    rw [map_smul, smul_eq_mul] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h hr0
    · exact h
  obtain ⟨b, hb⟩ := edge_param (D.tile j) (h2 (left_mem_segment ℝ u v))
  have hj1 : crossL d ((D.tile j).pts l) = cross d O := by
    have : crossL d u = crossL d ((D.tile j).pts l) + b * crossL d dj := by
      rw [hb, map_add, map_smul, smul_eq_mul]
    rw [hfdj, mul_zero, add_zero] at this
    rw [← this, hfu]
  have hj2 : crossL d ((D.tile j).pts (l + 1)) = cross d O := by
    have : (D.tile j).pts (l + 1) = (D.tile j).pts l + dj := by rw [hdj]; abel
    rw [this, map_add, hfdj, add_zero, hj1]
  have hci := mem_chain_or D (crossL d) (cross d O) hf i k hi1 hi2
  have hcj := mem_chain_or D (crossL d) (cross d O) hf j l hj1 hj2
  have hui : u ∈ (D.tile i).edge k := h1 (left_mem_segment ℝ u v)
  have huj : u ∈ (D.tile j).edge l := h2 (left_mem_segment ℝ u v)
  have hvi : v ∈ (D.tile i).edge k := h1 (right_mem_segment ℝ u v)
  have hvj : v ∈ (D.tile j).edge l := h2 (right_mem_segment ℝ u v)
  have hne : (i, k) ≠ (j, l) := fun h' => hij (congrArg Prod.fst h')
  -- same chain is impossible
  have same : ∀ (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0), (i, k) ∈ D.lineChain f c →
      (j, l) ∈ D.lineChain f c → False := by
    intro f c hf hI hJ
    obtain ⟨-, -, hle1⟩ := Dissection.mem_lineChain.mp hI
    obtain ⟨-, -, hle2⟩ := Dissection.mem_lineChain.mp hJ
    have := D.sameside_edges_subsingleton f c hf hne
      ((D.tile i).carrier_subset_halfplane f c hle1)
      ((D.tile j).carrier_subset_halfplane f c hle2)
      (D.lineChain_edge_subset hI) (D.lineChain_edge_subset hJ)
    exact huv (this ⟨hui, huj⟩ ⟨hvi, hvj⟩)
  have hfin : ∃ P : Plane, (D.tile i).pts k - P ∈ edgeGroup D ∧ (D.tile j).pts l - P ∈ edgeGroup D := by
    rcases hci with hI | hI <;> rcases hcj with hJ | hJ
    · exact (same _ _ hf hI hJ).elim
    · obtain ⟨P, a1, -, b1, -⟩ := chains_coset hd hI hJ hui huj
      exact ⟨P, a1, b1⟩
    · obtain ⟨P, a1, -, b1, -⟩ := chains_coset hd hJ hI huj hui
      exact ⟨P, b1, a1⟩
    · exact (same _ _ hf' hI hJ).elim
  obtain ⟨P, hP1, hP2⟩ := hfin
  exact ⟨P, corners_of hP1, corners_of hP2⟩

/-- **L1.pos.**  All tile vertices of a dissection lie in one coset of the edge group. -/
theorem L1_pos {N : ℕ} (D : Dissection N) (i0 : Fin N) (c0 : Fin 3) :
    ∀ i k, (D.tile i).pts k - (D.tile i0).pts c0 ∈ edgeGroup D := by
  have hQ : ∀ i, Relation.ReflTransGen (nbrGraph D).Adj i0 i →
      ∀ a, (D.tile i).pts a - (D.tile i0).pts c0 ∈ edgeGroup D := by
    intro i hi
    induction hi with
    | refl => exact fun a => corner_sub_mem D i0 a c0
    | tail _ hbc ih =>
      rename_i b c
      obtain ⟨P, hb, hc⟩ := adj_coset D hbc
      intro a
      have := (edgeGroup D).add_mem (hc a) ((edgeGroup D).neg_mem (hb c0))
      -- pts_c a - P - (pts_b c0 - P) = pts_c a - pts_b c0 ; then add pts_b c0 - pts_i0 c0
      have h2 := (edgeGroup D).add_mem this (ih c0)
      convert h2 using 1; abel
  intro i k
  have hreach := (nbrGraph_connected D).preconnected i0 i
  exact hQ i (SimpleGraph.reachable_iff_reflTransGen _ _ |>.mp hreach) k

end Erdos634.H1gPos

#print axioms Erdos634.H1gPos.line_chain_coset
#print axioms Erdos634.H1gPos.adj_coset
#print axioms Erdos634.H1gPos.L1_pos

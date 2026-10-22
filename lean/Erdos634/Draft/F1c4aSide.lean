-- Draft/F1c4aSide.lean — GapF1c4a at N = 15 (the (3,5) branch c = 4a), by the "short side" argument of
-- (private working notes, not included)  UNAUDITED.
--
-- Argument.  c = 4a and c² = a²+ab+b² give b²+ab = 15a²; the area identity 15 b = μ²(a+b) then gives
-- μ a = b (no use of Ma).  The target side opposite the α-corner has length μa = b.  `side_walk` covers
-- it by whole tile edges, each of length a, b or 4a.  If none had length b, the side length b would be
-- (a natural number)·a; then m²+m = 15 has no natural solution.  So some edge e of length b lies in that
-- side; its two endpoints lie on the side and are at distance b = side length, so they ARE the two
-- corners.  The b-edge of a 2π/3-tile has a 2π/3 endpoint, hence a tile has localAngle 2π/3 at a target
-- corner, contradicting `f1_no_gamma_at_corners`.
--
-- Note: no irrationality of b/a is used (only m²+m ≠ 15 over ℕ); IrrPi enters only through
-- `f1_no_gamma_at_corners`.
import Erdos634.Draft.Chain15F1
import Erdos634.Draft.F1K2Core
import Erdos634.EdgeChain

open scoped Classical

namespace Erdos634.Draft.F1c4aSide

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15

private lemma c_sq {T : Tri} {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) :
    c ^ 2 = a ^ 2 + a * b + b ^ 2 := by
  obtain ⟨σ, -, ha, -, hb, hγ, hc⟩ := h
  have hl := T.lawCos_perm σ
  rw [ha, hb, hc, hγ,
      show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three] at hl
  linarith

/-! ## Algebra -/

lemma mu_eq {a b c μ : ℝ} {N : ℕ} (hN : N = 15) (ha : 0 < a) (hb : 0 < b) (hμ : 0 < μ)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) (hc : c = 4 * a)
    (harea : (N : ℝ) * b = μ ^ 2 * (a + b)) : μ * a = b := by
  have hN' : (N : ℝ) = 15 := by exact_mod_cast hN
  rw [hN'] at harea
  have h1 : b * (a + b) = 15 * a ^ 2 := by rw [hc] at hc2; nlinarith
  have h2 : (μ * a) ^ 2 = b ^ 2 := by
    have : b * (15 * b) = b * (μ ^ 2 * (a + b)) := by rw [← harea]
    nlinarith [h1, this]
  have := (sq_eq_sq₀ (by positivity) hb.le).mp h2
  exact this

lemma no_nat_multiple {a b c : ℝ} (ha : 0 < a) (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hc : c = 4 * a) (m : ℕ) : b ≠ (m : ℝ) * a := by
  intro h
  rw [hc, h] at hc2
  have h1 : ((m : ℝ) ^ 2 + m) * a ^ 2 = 15 * a ^ 2 := by nlinarith
  have h2 : ((m : ℝ) ^ 2 + m) = 15 := by
    have := mul_right_cancel₀ (by positivity : a ^ 2 ≠ 0) h1
    exact this
  have h3 : m ^ 2 + m = 15 := by exact_mod_cast h2
  have : m ≤ 3 := by nlinarith
  interval_cases m <;> omega

/-! ## Angle at the γ vertex -/

lemma cornerAngle_gamma {p q r : Plane} {u v w : ℝ} (hu : 0 < u) (hv : 0 < v)
    (h1 : dist p q = u) (h2 : dist r q = v) (h3 : dist p r = w)
    (hw : w ^ 2 = u ^ 2 + v ^ 2 + u * v) :
    cornerAngle p q r = 2 * Real.pi / 3 := by
  have hl := EuclideanGeometry.law_cos p q r
  rw [h1, h2, h3] at hl
  have hcos : Real.cos (EuclideanGeometry.angle p q r) = -1 / 2 := by
    have : (2 * u * v) * Real.cos (EuclideanGeometry.angle p q r) = -(u * v) := by nlinarith
    have huv : 0 < u * v := mul_pos hu hv
    field_simp
    nlinarith
  show EuclideanGeometry.angle p q r = 2 * Real.pi / 3
  apply Real.injOn_cos
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  rw [hcos, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring, Real.cos_pi_sub,
    Real.cos_pi_div_three]
  norm_num

/-- If the edge `k → k+1` of a triangle has length `b` and the other two edges are `a` and `c` (either
order), with `c² = a²+ab+b²`, one of its endpoints has local angle `2π/3`. -/
lemma gamma_of_yz (T : Tri) (k : Fin 3) {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hx : dist (T.pts k) (T.pts (k + 1)) = b)
    (hyz : (dist (T.pts (k + 2)) (T.pts k) = a ∧ dist (T.pts (k + 1)) (T.pts (k + 2)) = c) ∨
           (dist (T.pts (k + 2)) (T.pts k) = c ∧ dist (T.pts (k + 1)) (T.pts (k + 2)) = a)) :
    T.localAngle (T.pts k) = 2 * Real.pi / 3 ∨ T.localAngle (T.pts (k + 1)) = 2 * Real.pi / 3 := by
  rcases hyz with ⟨hy, hz⟩ | ⟨hy, hz⟩
  · left
    rw [Tri.localAngle_vertex]
    refine cornerAngle_gamma (u := b) (v := a) (w := c) hb ha ?_ ?_ ?_ ?_
    · rw [dist_comm]; exact hx
    · exact hy
    · exact hz
    · rw [hc2]; ring
  · right
    rw [Tri.localAngle_vertex]
    have e1 : k + 1 + 1 = k + 2 := (show ∀ k : Fin 3, k + 1 + 1 = k + 2 from by decide) k
    have e2 : k + 1 + 2 = k := (show ∀ k : Fin 3, k + 1 + 2 = k from by decide) k
    rw [e1, e2]
    refine cornerAngle_gamma (u := a) (v := b) (w := c) ha hb ?_ ?_ ?_ ?_
    · rw [dist_comm]; exact hz
    · exact hx
    · exact hy
    · rw [hc2]; ring

/-! ## A tile edge of length b has a γ endpoint -/

lemma tile_b_edge_gamma {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ}
    (hm : D.model.TwoPiThreeData α a b c) (hc : c = 4 * a)
    (j : Fin N) (k : Fin 3) (hk : dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = b) :
    (D.tile j).localAngle ((D.tile j).pts k) = 2 * Real.pi / 3 ∨
    (D.tile j).localAngle ((D.tile j).pts (k + 1)) = 2 * Real.pi / 3 := by
  obtain ⟨-, hc0, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  have hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2 := c_sq hm
  have hba : b ≠ a := by
    intro h; rw [h, hc] at hc2; nlinarith
  have hbc : b ≠ c := by
    intro h; rw [← h] at hc2; rw [← h] at hc; rw [hc] at hc2; nlinarith
  have hac : a ≠ c := by intro h; rw [hc] at h; linarith
  -- a, c are in the tile's side multiset
  have hmulti := (D.tiles_congruent j).sideMultiset_eq
  have hmodel_mem : ∀ t : Fin 3, D.model.oppLen t ∈
      ({dist (D.model.pts 0) (D.model.pts 1), dist (D.model.pts 2) (D.model.pts 0),
        dist (D.model.pts 1) (D.model.pts 2)} : Multiset ℝ) := by
    intro t
    have hshift := Tri.sideMultiset_shift D.model t
    rw [← hshift]
    simp [Tri.oppLen]
  obtain ⟨σ, -, ha_op, -, hb_op, -, hc_op⟩ := hm
  have ha_mem := hmodel_mem (σ 0)
  have hc_mem := hmodel_mem (σ 2)
  rw [ha_op] at ha_mem
  rw [hc_op] at hc_mem
  rw [← hmulti] at ha_mem hc_mem
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at ha_mem hc_mem
  -- reduce to the (y,z) statement
  apply gamma_of_yz (D.tile j) k ha0 hb0 hc2 hk
  have key : ∀ x y z : ℝ, x = b → (a = x ∨ a = y ∨ a = z) → (c = x ∨ c = y ∨ c = z) →
      (y = a ∧ z = c) ∨ (y = c ∧ z = a) := by
    intro x y z hx h1 h2
    subst hx
    rcases h1 with h | h | h <;> rcases h2 with h' | h' | h'
    all_goals first
      | (exfalso; exact hba h.symm)
      | (exfalso; exact hbc h'.symm)
      | (exfalso; exact hac (h.trans h'.symm))
      | (first | exact Or.inl ⟨h.symm, h'.symm⟩ | exact Or.inr ⟨h'.symm, h.symm⟩)
  have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  rcases hk3 with rfl | rfl | rfl
  · have e1 : (0 : Fin 3) + 1 = 1 := rfl
    have e2 : (0 : Fin 3) + 2 = 2 := rfl
    rw [e1] at hk; rw [e1, e2]
    exact key _ _ _ hk (by tauto) (by tauto)
  · have e1 : (1 : Fin 3) + 1 = 2 := rfl
    have e2 : (1 : Fin 3) + 2 = 0 := rfl
    rw [e1] at hk; rw [e1, e2]
    exact key _ _ _ hk (by tauto) (by tauto)
  · have e1 : (2 : Fin 3) + 1 = 0 := rfl
    have e2 : (2 : Fin 3) + 2 = 1 := rfl
    rw [e1] at hk; rw [e1, e2]
    exact key _ _ _ hk (by tauto) (by tauto)


/-! ## Endpoints of a segment -/

lemma segment_endpoints {x y p q : Plane} (hp : p ∈ segment ℝ x y) (hq : q ∈ segment ℝ x y)
    (h : dist p q = dist x y) (hxy : x ≠ y) :
    (p = x ∧ q = y) ∨ (p = y ∧ q = x) := by
  rw [segment_eq_image_lineMap] at hp hq
  obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := hp
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hq
  rw [dist_lineMap_lineMap] at h
  have hd : 0 < dist x y := dist_pos.mpr hxy
  have hst : dist s t = 1 := by
    have : (dist s t - 1) * dist x y = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · linarith
    · linarith
  rw [Real.dist_eq] at hst
  rcases abs_cases (s - t) with ⟨h1, _⟩ | ⟨h1, _⟩
  · have hs : s = 1 := by linarith
    have ht : t = 0 := by linarith
    subst hs; subst ht
    right; simp
  · have hs : s = 0 := by linarith
    have ht : t = 1 := by linarith
    subst hs; subst ht
    left; simp

/-! ## Main theorem -/

private lemma tile_edges_abc {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ}
    (hm : D.model.TwoPiThreeData α a b c) :
    ∀ (j : Fin N) (k : Fin 3),
      dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = a ∨
      dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = b ∨
      dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = c := by
  intro j k
  obtain ⟨m, hm_eq⟩ := D.eLen_mem ⟨j, k⟩
  have hdef : D.eLen ⟨j, k⟩ = dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) := rfl
  rw [← hdef, hm_eq]
  obtain ⟨σ, -, ha_op, -, hb_op, -, hc_op⟩ := hm
  obtain ⟨i, rfl⟩ := σ.surjective m
  fin_cases i
  · exact Or.inl ha_op
  · exact Or.inr (Or.inl hb_op)
  · exact Or.inr (Or.inr hc_op)

theorem gapF1c4a_holds : GapF1c4a := by
  intro D α a b c μ hirr hm hF1 hμ hc
  obtain ⟨-, hc0, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  have hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2 := c_sq hm
  have harea := Erdos634.Draft.F1AreaIdentity.F1_area_identity D hm hF1 ha0 hb0 hμ
  have hμa : μ * a = b := mu_eq (N := 15) rfl ha0 hb0 hμ hc2 hc harea
  have htabc := tile_edges_abc D hm
  obtain ⟨-, hgrid⟩ := id hF1
  obtain ⟨σ, -, hopp, -, -, -, -⟩ := hgrid
  have e12 : ∀ k : Fin 3, k + 1 + 1 = k + 2 := by decide
  set i : Fin 3 := σ 0 + 1 with hi
  have hi1 : i + 1 = σ 0 + 2 := by rw [hi]; exact e12 _
  have hside : dist (D.target.pts i) (D.target.pts (i + 1)) = b := by
    rw [hi1, ← hμa, ← hopp]; rfl
  obtain ⟨part, hcov, -, hsum⟩ := Dissection.side_walk D.toDissection i
  rw [hside] at hsum
  -- some covering edge has length b
  have hex : ∃ e ∈ part, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = b := by
    by_contra hno
    push Not at hno
    have hlen : ∀ e ∈ part, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) =
        ((if dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = a then 1 else 4 : ℕ) : ℝ)
          * a := by
      intro e he
      rcases htabc e.1 e.2 with h | h | h
      · rw [if_pos h]; simp [h]
      · exact absurd h (hno e he)
      · have hne : ¬ dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = a := by
          rw [h, hc]; intro h'; linarith
        rw [if_neg hne]; rw [h, hc]; push_cast; ring
    rw [Finset.sum_congr rfl hlen, ← Finset.sum_mul] at hsum
    apply no_nat_multiple ha0 hc2 hc (∑ e ∈ part,
      (if dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = a then 1 else 4 : ℕ))
    rw [← hsum]; push_cast; rfl
  obtain ⟨e, he, hlenb⟩ := hex
  have hsub : (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts i) (D.target.pts (i + 1)) := by
    intro x hx
    have hx' : x ∈ ⋃ e ∈ part, (D.tile e.1).edge e.2 := Set.mem_iUnion₂.mpr ⟨e, he, hx⟩
    rwa [hcov] at hx'
  have hp : (D.tile e.1).pts e.2 ∈ segment ℝ (D.target.pts i) (D.target.pts (i + 1)) :=
    hsub (left_mem_segment ℝ _ _)
  have hq : (D.tile e.1).pts (e.2 + 1) ∈ segment ℝ (D.target.pts i) (D.target.pts (i + 1)) :=
    hsub (right_mem_segment ℝ _ _)
  have hxy : D.target.pts i ≠ D.target.pts (i + 1) := by
    intro h; rw [h, dist_self] at hside; linarith
  have hend := segment_endpoints hp hq (by rw [hlenb, hside]) hxy
  have hγ := tile_b_edge_gamma D hm hc e.1 e.2 hlenb
  have hno := f1_no_gamma_at_corners D hirr hm hF1
  rcases hend with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases hγ with h | h
    · rw [h1] at h; exact hno i e.1 h
    · rw [h2] at h; exact hno (i + 1) e.1 h
  · rcases hγ with h | h
    · rw [h1] at h; exact hno (i + 1) e.1 h
    · rw [h2] at h; exact hno i e.1 h

end Erdos634.Draft.F1c4aSide

#print axioms Erdos634.Draft.F1c4aSide.gapF1c4a_holds

import Erdos634.Draft.LaczFormalMJCell
import Erdos634.Draft.LaczFormalMJArith

/-!
# Generic chord covers with non-straddled ends, and positions of equal-length far edges

Erdős #634, base-`β` band, rule `M(j)`.  Credit: AI assistant (item 3, band program, principle E), Beeson–Roșu,
Beeson, Laczkovich (chord covers), Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.

* `L3_ns`: `wall_sum` for a chord `[P,G]` whose ends are merely not straddled by an edge of the far chain
  `lineChain g c` (the hypothesis `hbef` of `L3_sum_g`, "the line leaves the target before `P`", is replaced by
  `¬ Straddled P`; this is the interior-start version needed on a fault line).
* `lens_all_eq`: if a finite family of lengths in `{A,B,C}` has sum `n·L` and `xA+yB+zC = nL` forces every used
  length to be `L`, then every length is `L`.
-/

namespace Erdos634.LaczMJ

open Erdos634.Geometry Erdos634.Draft.TraceCovering Set Erdos634.LaczJunction Erdos634.LaczJunction.Walk

variable {N : ℕ}

open Classical in
/-- **L3, sum form, both ends only non-straddled.** -/
theorem L3_ns (D : Dissection N) {P G : Plane} (hne : P ≠ G) (g : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hg0 : g ≠ 0)
    (hgP : g P = c) (hgG : g G = c)
    (hint : ∀ t : ℝ, 0 < t → t < 1 → AffineMap.lineMap P G t ∈ interior D.target.carrier)
    (hwall : ∀ t : ℝ, 0 < t → t < 1 → ∀ i, AffineMap.lineMap P G t ∉ interior (D.tile i).carrier)
    (hP : ¬ Straddled D g c P) (hG : ¬ Straddled D g c G) :
    ∑ e ∈ (D.lineChain g c).filter (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ P G),
      dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = dist P G := by
  have hBr : 0 < dist P G := dist_pos.mpr hne
  set B := dist P G with hBdef
  have hu0 : B⁻¹ • (G - P) ≠ 0 := by
    apply smul_ne_zero (inv_ne_zero hBr.ne')
    exact sub_ne_zero.mpr (Ne.symm hne)
  set u : Plane := B⁻¹ • (G - P) with hu
  have hgu : g u = 0 := by
    rw [hu, map_smul, map_sub, hgG, hgP]; simp
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, Real.norm_of_nonneg hBr.le, ← dist_eq_norm, dist_comm, ← hBdef]
    field_simp
  have hend : P + B • u = G := by
    rw [hu, smul_smul, mul_inv_cancel₀ hBr.ne', one_smul]; abel
  have hsum := wall_sum (D := D) (X := P) (u := u) (f := g) (g := g) (c := c) (d := c) hg0
    (fun _ => Iff.rfl) hg0 hgP hgu hu1 (s := 0) (t := B) hBr.le
    (fun x hx => by
      rw [hu, line_param P G hBr.ne' x]
      exact hint _ (div_pos hx.1 hBr) ((div_lt_one hBr).mpr hx.2))
    (fun x hx i => by
      rw [hu, line_param P G hBr.ne' x]
      exact hwall _ (div_pos hx.1 hBr) ((div_lt_one hBr).mpr hx.2) i)
    (by rw [zero_smul, add_zero]; exact hP) (by rw [hend]; exact hG)
  rw [sub_zero, hend, zero_smul, add_zero] at hsum
  exact hsum


/-- **All lengths equal `L`.**  A finite family of lengths in `{A,B,C}` with total `n·L`, where the only
representations `xA + yB + zC = nL` use lengths equal to `L`, consists of lengths equal to `L`. -/
theorem lens_all_eq {ι : Type*} (s : Finset ι) (len : ι → ℝ) (A B C L n : ℕ)
    (hlen : ∀ e ∈ s, len e = A ∨ len e = B ∨ len e = C)
    (hsum : ∑ e ∈ s, len e = (n : ℝ) * L)
    (hcover : ∀ x y z : ℕ, x * A + y * B + z * C = n * L →
      (A = L ∨ x = 0) ∧ (B = L ∨ y = 0) ∧ (C = L ∨ z = 0)) :
    ∀ e ∈ s, len e = L := by
  classical
  have hsplit1 := Finset.sum_filter_add_sum_filter_not s (fun e => len e = A) len
  have hsplit2 := Finset.sum_filter_add_sum_filter_not
    (s.filter fun e => ¬ len e = A) (fun e => len e = B) len
  rw [Finset.filter_filter, Finset.filter_filter] at hsplit2
  set s1 := s.filter fun e => len e = A with hs1
  set s2 := s.filter fun e => ¬ len e = A ∧ len e = B with hs2
  set s3 := s.filter fun e => ¬ len e = A ∧ ¬ len e = B with hs3
  have hA : ∑ e ∈ s1, len e = (s1.card : ℝ) * A := by
    rw [Finset.sum_congr rfl (fun e he => (Finset.mem_filter.mp he).2), Finset.sum_const, nsmul_eq_mul]
  have hB : ∑ e ∈ s2, len e = (s2.card : ℝ) * B := by
    rw [Finset.sum_congr rfl (fun e he => (Finset.mem_filter.mp he).2.2), Finset.sum_const, nsmul_eq_mul]
  have hC : ∑ e ∈ s3, len e = (s3.card : ℝ) * C := by
    rw [Finset.sum_congr rfl (fun e he => ?_), Finset.sum_const, nsmul_eq_mul]
    have hmem := Finset.mem_filter.mp he
    rcases hlen e hmem.1 with h' | h' | h'
    · exact absurd h' hmem.2.1
    · exact absurd h' hmem.2.2
    · exact h'
  have heq : s1.card * A + s2.card * B + s3.card * C = n * L := by
    have : ((s1.card * A + s2.card * B + s3.card * C : ℕ) : ℝ) = ((n * L : ℕ) : ℝ) := by
      push_cast
      rw [← hsum, ← hsplit1, ← hsplit2, hA, hB, hC]
      ring
    exact_mod_cast this
  obtain ⟨c1, c2, c3⟩ := hcover _ _ _ heq
  intro e he
  by_cases h1 : len e = A
  · have hm : e ∈ s1 := Finset.mem_filter.mpr ⟨he, h1⟩
    have : s1.card ≠ 0 := (Finset.card_pos.mpr ⟨e, hm⟩).ne'
    rcases c1 with h | h
    · rw [h1, h]
    · exact absurd h this
  · by_cases h2 : len e = B
    · have hm : e ∈ s2 := Finset.mem_filter.mpr ⟨he, h1, h2⟩
      have : s2.card ≠ 0 := (Finset.card_pos.mpr ⟨e, hm⟩).ne'
      rcases c2 with h | h
      · rw [h2, h]
      · exact absurd h this
    · have h3 : len e = C := by
        rcases hlen e he with h | h | h
        · exact absurd h h1
        · exact absurd h h2
        · exact h
      have hm : e ∈ s3 := Finset.mem_filter.mpr ⟨he, h1, h2⟩
      have : s3.card ≠ 0 := (Finset.card_pos.mpr ⟨e, hm⟩).ne'
      rcases c3 with h | h
      · rw [h3, h]
      · exact absurd h this


open Classical in
/-- **Positions of the far edges of an equal-length wall.**  On the wall `[P,G]` (`|PG| = n·L`) with non-straddled
ends, if `xA+yB+zC = nL` forces every used length to be `L`, the far-chain edges inside `[P,G]` all have length `L`
and, for every `k < n`, some far-chain edge is exactly the segment between the points of parameters `k/n`,
`(k+1)/n`. -/
theorem far_positions (D : Dissection N) (A B C L n : ℕ)
    (hcover : ∀ x y z : ℕ, x * A + y * B + z * C = n * L →
      (A = L ∨ x = 0) ∧ (B = L ∨ y = 0) ∧ (C = L ∨ z = 0))
    (habc : ∀ (i : Fin N) (k : Fin 3),
      dist ((D.tile i).pts k) ((D.tile i).pts (k+1)) = (A : ℝ) ∨
      dist ((D.tile i).pts k) ((D.tile i).pts (k+1)) = (B : ℝ) ∨
      dist ((D.tile i).pts k) ((D.tile i).pts (k+1)) = (C : ℝ))
    {P G : Plane} (hne : P ≠ G) (hPG : dist P G = (n : ℝ) * L) (hL : 0 < L)
    (g : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hg0 : g ≠ 0) (hgP : g P = c) (hgG : g G = c)
    (hint : ∀ t : ℝ, 0 < t → t < 1 → AffineMap.lineMap P G t ∈ interior D.target.carrier)
    (hwall : ∀ t : ℝ, 0 < t → t < 1 → ∀ i, AffineMap.lineMap P G t ∉ interior (D.tile i).carrier)
    (hP : ¬ Straddled D g c P) (hG : ¬ Straddled D g c G) :
    (∀ e ∈ D.lineChain g c, (D.tile e.1).edge e.2 ⊆ segment ℝ P G →
        dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = L) ∧
    (∀ e ∈ D.lineChain g c, (D.tile e.1).edge e.2 ⊆ segment ℝ P G → ∃ k : ℕ, k < n ∧
      (((D.tile e.1).pts e.2 = AffineMap.lineMap P G ((k : ℝ) / n) ∧
        (D.tile e.1).pts (e.2 + 1) = AffineMap.lineMap P G (((k : ℝ) + 1) / n)) ∨
       ((D.tile e.1).pts e.2 = AffineMap.lineMap P G (((k : ℝ) + 1) / n) ∧
        (D.tile e.1).pts (e.2 + 1) = AffineMap.lineMap P G ((k : ℝ) / n)))) ∧
    ∀ k : ℕ, k < n → ∃ e ∈ D.lineChain g c,
      (((D.tile e.1).pts e.2 = AffineMap.lineMap P G ((k : ℝ) / n) ∧
        (D.tile e.1).pts (e.2 + 1) = AffineMap.lineMap P G (((k : ℝ) + 1) / n)) ∨
       ((D.tile e.1).pts e.2 = AffineMap.lineMap P G (((k : ℝ) + 1) / n) ∧
        (D.tile e.1).pts (e.2 + 1) = AffineMap.lineMap P G ((k : ℝ) / n))) := by
  have hsum := L3_ns D hne g c hg0 hgP hgG hint hwall hP hG
  set S := (D.lineChain g c).filter (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ P G) with hS
  have hallL : ∀ e ∈ S, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = L :=
    lens_all_eq S (fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))) A B C L n
      (fun e _ => habc e.1 e.2) (by rw [hsum, hPG]) hcover
  have part1 : ∀ e ∈ D.lineChain g c, (D.tile e.1).edge e.2 ⊆ segment ℝ P G →
      dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = L :=
    fun e he hs => hallL e (Finset.mem_filter.mpr ⟨he, hs⟩)
  have hBr : 0 < dist P G := dist_pos.mpr hne
  set B' := dist P G with hBdef
  have hu0 : B'⁻¹ • (G - P) ≠ 0 := by
    apply smul_ne_zero (inv_ne_zero hBr.ne')
    exact sub_ne_zero.mpr (Ne.symm hne)
  set u : Plane := B'⁻¹ • (G - P) with hu
  have hgu : g u = 0 := by
    rw [hu, map_smul, map_sub, hgG, hgP]; simp
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, Real.norm_of_nonneg hBr.le, ← dist_eq_norm, dist_comm, ← hBdef]
    field_simp
  have hend : P + B' • u = G := by
    rw [hu, smul_smul, mul_inv_cancel₀ hBr.ne', one_smul]; abel
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hnr : (0 : ℝ) < n := by
    by_contra h
    push Not at h
    have : (n : ℝ) * L ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hLr.le
    linarith
  have hint' : ∀ x ∈ Ioo (0:ℝ) B', P + x • u ∈ interior D.target.carrier := fun x hx => by
    rw [hu, line_param P G hBr.ne' x]
    exact hint _ (div_pos hx.1 hBr) ((div_lt_one hBr).mpr hx.2)
  have hwall' : ∀ x ∈ Ioo (0:ℝ) B', ∀ i, P + x • u ∉ interior (D.tile i).carrier := fun x hx i => by
    rw [hu, line_param P G hBr.ne' x]
    exact hwall _ (div_pos hx.1 hBr) ((div_lt_one hBr).mpr hx.2) i
  have hGseg : ∀ p, p ∈ segment ℝ P G → ∀ e' ∈ D.lineChain g c, (D.tile e'.1).edge e'.2 ⊆ segment ℝ P p →
      e' ∈ S := by
    intro p hp e' he' hsub
    refine Finset.mem_filter.mpr ⟨he', hsub.trans ?_⟩
    exact (convex_segment P G).segment_subset (left_mem_segment ℝ P G) hp
  -- every endpoint of an edge of S is at distance `m·L` from `P`
  have hpart : ∀ e ∈ S, ∀ p, (p = (D.tile e.1).pts e.2 ∨ p = (D.tile e.1).pts (e.2 + 1)) →
      ∃ m : ℕ, dist P p = m * L := by
    intro e he p hp
    have hem := Finset.mem_filter.mp he
    have hpseg : p ∈ segment ℝ P G := by
      rcases hp with rfl | rfl
      · exact hem.2 (left_mem_segment ℝ _ _)
      · exact hem.2 (right_mem_segment ℝ _ _)
    have hin : (D.tile e.1).edge e.2 ⊆ segment ℝ P (P + B' • u) := by rw [hend]; exact hem.2
    have key := junction_partial_sum (D := D) (X := P) (u := u) (f := g) (g := g) (c := c) (d := c) hg0
      (fun _ => Iff.rfl) hg0 hgP hgu hu1 (x₀ := B') hBr.le hint' hwall' hP hem.1 hin hp
    refine ⟨((D.lineChain g c).filter (fun e' => (D.tile e'.1).edge e'.2 ⊆ segment ℝ P p)).card, ?_⟩
    rw [← key, Finset.sum_congr rfl (fun e' he' => ?_), Finset.sum_const, nsmul_eq_mul]
    have hm := Finset.mem_filter.mp he'
    exact hallL e' (hGseg p hpseg e' hm.1 hm.2)
  have hdistP : ∀ t : ℝ, 0 ≤ t → dist P (P + t • u) = t := by
    intro t ht
    rw [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, hu1, mul_one, Real.norm_of_nonneg ht]
  have hBeq : B' = (n : ℝ) * L := hPG
  have hpt : ∀ j : ℝ, P + (j * L) • u = AffineMap.lineMap P G (j / n) := by
    intro j
    have h := line_param P G hBr.ne' (j * L)
    rw [hu, h, hBeq]
    congr 1
    field_simp
  -- every edge of `S` sits at consecutive multiples of `L`
  have key : ∀ e ∈ S, ∃ m : ℕ, m < n ∧ lo D P u e = m * L ∧ hi D P u e = ((m : ℝ) + 1) * L ∧
      (((D.tile e.1).pts e.2 = AffineMap.lineMap P G ((m : ℝ) / n) ∧
        (D.tile e.1).pts (e.2 + 1) = AffineMap.lineMap P G (((m : ℝ) + 1) / n)) ∨
       ((D.tile e.1).pts e.2 = AffineMap.lineMap P G (((m : ℝ) + 1) / n) ∧
        (D.tile e.1).pts (e.2 + 1) = AffineMap.lineMap P G ((m : ℝ) / n))) := by
    intro e heS
    have hem := Finset.mem_filter.mp heS
    have he := hem.1
    obtain ⟨h0e, h1e⟩ := onLine (D := D) (f := g) (g := g) (c := c) (d := c) (fun _ => Iff.rfl) he
    obtain ⟨hlt, hedge, hopen, hdist⟩ := edge_data (D := D) hg0 hgP hgu hu0 h0e h1e
    have hins := (inside_iff (D := D) (fun _ => Iff.rfl) hg0 hgP hgu hu0 he (s := 0) (t := B') hBr.le).mp
      (by rw [zero_smul, add_zero, hend]; exact hem.2)
    obtain ⟨hlo0, hhiB⟩ := hins
    have hLe := hallL e heS
    have hhl : hi D P u e = lo D P u e + L := by have := hdist hu1; linarith
    have e0 := par_spec (exists_param hg0 hgP hgu hu0 h0e)
    have e1 := par_spec (exists_param hg0 hgP hgu hu0 h1e)
    set t0 := par P u ((D.tile e.1).pts e.2) with ht0
    set t1 := par P u ((D.tile e.1).pts (e.2 + 1)) with ht1
    have ht0nn : 0 ≤ t0 := le_trans hlo0 (min_le_left _ _)
    have ht1nn : 0 ≤ t1 := le_trans hlo0 (min_le_right _ _)
    obtain ⟨m0, hm0⟩ := hpart e heS _ (Or.inl rfl)
    obtain ⟨m1, hm1⟩ := hpart e heS _ (Or.inr rfl)
    have ht0m : t0 = m0 * L := by
      have := hdistP t0 ht0nn
      rw [← e0] at this; linarith
    have ht1m : t1 = m1 * L := by
      have := hdistP t1 ht1nn
      rw [← e1] at this; linarith
    have hlo_m : ∃ m : ℕ, lo D P u e = m * L := by
      simp only [lo]
      rcases min_choice t0 t1 with h | h
      · exact ⟨m0, by rw [← ht0, ← ht1, h, ht0m]⟩
      · exact ⟨m1, by rw [← ht0, ← ht1, h, ht1m]⟩
    obtain ⟨m, hmL⟩ := hlo_m
    have hhmk : hi D P u e = ((m : ℝ) + 1) * L := by rw [hhl, hmL]; ring
    have hmn : m < n := by
      have : ((m : ℝ) + 1) * L ≤ n * L := by rw [← hhmk, ← hBeq]; exact hhiB
      have h1 : (m : ℝ) + 1 ≤ n := le_of_mul_le_mul_right this hLr
      have h2 : m + 1 ≤ n := by exact_mod_cast h1
      omega
    refine ⟨m, hmn, hmL, hhmk, ?_⟩
    rcases le_total t0 t1 with hle | hle
    · have hl : lo D P u e = t0 := by simp only [lo]; rw [← ht0, ← ht1, min_eq_left hle]
      have hh : hi D P u e = t1 := by simp only [hi]; rw [← ht0, ← ht1, max_eq_right hle]
      left
      constructor
      · rw [e0, ← hl, hmL, hpt]
      · rw [e1, ← hh, hhmk, hpt]
    · have hl : lo D P u e = t1 := by simp only [lo]; rw [← ht0, ← ht1, min_eq_right hle]
      have hh : hi D P u e = t0 := by simp only [hi]; rw [← ht0, ← ht1, max_eq_left hle]
      right
      constructor
      · rw [e0, ← hh, hhmk, hpt]
      · rw [e1, ← hl, hmL, hpt]
  refine ⟨part1, ?_, ?_⟩
  · intro e he hsub
    obtain ⟨m, hmn, -, -, hend'⟩ := key e (Finset.mem_filter.mpr ⟨he, hsub⟩)
    exact ⟨m, hmn, hend'⟩
  · intro k hk
    have hkr : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hfin := finite_vertex_params (D := D) (X := P) (u := u) hu0
    have hinf : (Ioo ((k : ℝ) * L) (((k : ℝ) + 1) * L)).Infinite :=
      Set.Ioo_infinite (by nlinarith)
    obtain ⟨x, hxI, hxv⟩ := hinf.exists_notMem_finite hfin
    have hxB : x ∈ Ioo (0:ℝ) B' := ⟨by nlinarith [hxI.1], by nlinarith [hxI.2]⟩
    obtain ⟨e, he, hlo, hhi⟩ := wall_cover_param (D := D) (X := P) (u := u) (f := g) (g := g) (c := c) (d := c)
      hg0 (fun _ => Iff.rfl) hg0 hgP hgu hu0 hBr hint' hwall' hxB hxv
    obtain ⟨h0e, h1e⟩ := onLine (D := D) (f := g) (g := g) (c := c) (d := c) (fun _ => Iff.rfl) he
    obtain ⟨hlt, hedge, hopen, hdist⟩ := edge_data (D := D) hg0 hgP hgu hu0 h0e h1e
    have hlo0 : 0 ≤ lo D P u e := by
      by_contra h
      push Not at h
      apply hP
      have := (str_iff (D := D) (fun _ => Iff.rfl) hg0 hgP hgu hu0 0).mpr
        ⟨e, he, h, lt_of_lt_of_le hxB.1 hhi⟩
      simpa using this
    have hhiB : hi D P u e ≤ B' := by
      by_contra h
      push Not at h
      apply hG
      have := (str_iff (D := D) (fun _ => Iff.rfl) hg0 hgP hgu hu0 B').mpr
        ⟨e, he, lt_of_le_of_lt hlo hxB.2, h⟩
      rwa [hend] at this
    have heS : e ∈ S := by
      refine Finset.mem_filter.mpr ⟨he, ?_⟩
      have := (inside_iff (D := D) (fun _ => Iff.rfl) hg0 hgP hgu hu0 he (s := 0) (t := B') hBr.le).mpr
        ⟨hlo0, hhiB⟩
      rwa [zero_smul, add_zero, hend] at this
    obtain ⟨m, hmn, hmL, hhmk, hends⟩ := key e heS
    have hmk : m = k := by
      have h1 : (m : ℝ) * L < ((k : ℝ) + 1) * L := by linarith [hxI.2]
      have h2 : (k : ℝ) * L < ((m : ℝ) + 1) * L := by nlinarith [hxI.1]
      have h1' : (m : ℝ) < k + 1 := lt_of_mul_lt_mul_right h1 hLr.le
      have h2' : (k : ℝ) < m + 1 := lt_of_mul_lt_mul_right h2 hLr.le
      have h1'' : m < k + 1 := by exact_mod_cast h1'
      have h2'' : k < m + 1 := by exact_mod_cast h2'
      omega
    subst hmk
    exact ⟨e, he, hends⟩

end Erdos634.LaczMJ

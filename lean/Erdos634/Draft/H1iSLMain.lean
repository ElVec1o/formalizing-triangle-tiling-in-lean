/-
Draft/H1iSLMain.lean — atom H1.i (sign lemma SL) of (private working notes, not included) §4.

Setting.  `D : CongruentDissection N`, `K ⊆ ℝ` a subfield containing every tile/target corner coordinate and every tile
edge length (`hlen`; in Case D, after the similarity `b = 1`, the lengths are `a, b, c ∈ K`), `ψ : K →+* ℝ` any ring
homomorphism (for `K = ℚ(√M)`: the nontrivial automorphism).  By CT (`conj_congruentDissection_subfield`) the
ψ-images of the corners form a `CongruentDissection N`.

* `sum_abs_eq_sign`  : `∑|x_e| = |∑ x_e|` ⇒ every `x_e` has the sign of the total (real analysis, pure).
* `side_sign_lemma`  : **SL.**  For each side `s` of the target, with `part` the (unique) set of tile edges lying on it,
  `L ∈ K` its length, for every `e ∈ part`:   `0 < ψ(len e) · ψ(L)`  and  `∑_{e ∈ part} |ψ(len e)| = |ψ(L)|`.
  Also `part` is characterised: `e ∈ part ↔ both endpoints collinear with the side`.
  NO orientation/reflection hypothesis on the conjugate tiles is needed: only `∑ ψ(len) = ψ(L)` (linearity) and the
  identity `∑ dist' = dist'` for the conjugate dissection (CT + `side_walk`), and `dist' = |ψ(len)|`
  (since `dist'² = ψ(dist²) = ψ(len)²`).  The partition of D and of D' coincide because collinearity is polynomial.
* `side_type_sign`   : the form consumed by D6–D9: for tile edge lengths in `{a,b,c} ⊂ K`, the walk equation
  `P a + Q b + R c = L` with `P+Q+R ≤ 3N`, and `P ≠ 0 → 0 < ψ a · ψ L` etc.: **an edge type occurs on a side only if
  ψ of its length has the sign of ψ of the side length.**
*** UNAUDITED.  Formalization debt, NOT /goal progress.  No sorry. ***
-/
import Erdos634.Draft.H1iSLChar
import Erdos634.Draft.H1hCTCong

namespace Erdos634.H1iSL

open Erdos634.Geometry Erdos634.H1hCT Set

/-- `∑|x_e| = |∑ x_e|` forces each `x_e` to agree in sign with the total. -/
theorem sum_abs_eq_sign {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (h : ∑ e ∈ s, |x e| = |∑ e ∈ s, x e|) : ∀ e ∈ s, 0 ≤ x e * ∑ e ∈ s, x e := by
  intro e he
  rcases le_total 0 (∑ e ∈ s, x e) with h0 | h0
  · rw [abs_of_nonneg h0] at h
    have hz : ∑ e ∈ s, (|x e| - x e) = 0 := by rw [Finset.sum_sub_distrib, h]; ring
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun e _ => sub_nonneg.mpr (le_abs_self (x e)))).mp hz e he
    have hx : 0 ≤ x e := by
      have : |x e| = x e := by linarith
      exact abs_eq_self.mp this
    exact mul_nonneg hx h0
  · rw [abs_of_nonpos h0] at h
    have hz : ∑ e ∈ s, (|x e| + x e) = 0 := by rw [Finset.sum_add_distrib, h]; ring
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun e _ => by
      have := neg_abs_le (x e); linarith)).mp hz e he
    have hx : x e ≤ 0 := by
      have : |x e| = -x e := by linarith
      exact abs_eq_neg_self.mp this
    exact mul_nonneg_of_nonpos_of_nonpos hx h0

/-- Collinearity is transported by a ring homomorphism out of the field of coordinates. -/
theorem col_transport {K : Type*} [Field K] (φ : K →+* ℝ) (P Q p : Plane) (P' Q' p' : Fin 2 → K)
    (hP : ∀ v, P v = φ (P' v)) (hQ : ∀ v, Q v = φ (Q' v)) (hp : ∀ v, p v = φ (p' v)) :
    Col P Q p ↔ (Q' 0 - P' 0) * (p' 1 - P' 1) - (Q' 1 - P' 1) * (p' 0 - P' 0) = 0 := by
  unfold Col
  rw [hP 0, hP 1, hQ 0, hQ 1, hp 0, hp 1]
  rw [← map_sub, ← map_sub, ← map_sub, ← map_sub, ← map_mul, ← map_mul, ← map_sub]
  exact map_eq_zero φ

/-- **SL (sign lemma on a side).** See the file header. -/
theorem side_sign_lemma {N : ℕ} (D : CongruentDissection N) (K : Subfield ℝ) (ψ : K →+* ℝ)
    (hK : ∀ i k v, (D.tile i).pts k v ∈ K) (hKT : ∀ k v, D.target.pts k v ∈ K)
    (hlen : ∀ i k, dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) ∈ K) (s : Fin 3) :
    ∃ (part : Finset (Fin N × Fin 3)) (hL : dist (D.target.pts s) (D.target.pts (s + 1)) ∈ K),
      ((⋃ e ∈ part, (D.tile e.1).edge e.2)
          = segment ℝ (D.target.pts s) (D.target.pts (s + 1)))
      ∧ (∀ e₁ ∈ part, ∀ e₂ ∈ part, e₁ ≠ e₂ →
          ((D.tile e₁.1).edge e₁.2 ∩ (D.tile e₂.1).edge e₂.2).Subsingleton)
      ∧ (∀ e, e ∈ part ↔ (Col (D.target.pts s) (D.target.pts (s + 1)) ((D.tile e.1).pts e.2) ∧
            Col (D.target.pts s) (D.target.pts (s + 1)) ((D.tile e.1).pts (e.2 + 1))))
      ∧ ∑ e ∈ part, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
          = dist (D.target.pts s) (D.target.pts (s + 1))
      ∧ (∀ e ∈ part, 0 < ψ ⟨dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)), hlen e.1 e.2⟩ *
            ψ ⟨dist (D.target.pts s) (D.target.pts (s + 1)), hL⟩)
      ∧ ∑ e ∈ part, |ψ ⟨dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)), hlen e.1 e.2⟩|
          = |ψ ⟨dist (D.target.pts s) (D.target.pts (s + 1)), hL⟩| := by
  classical
  obtain ⟨part, hcov, hdisj, hsum⟩ := D.toDissection.side_walk s
  have hL : dist (D.target.pts s) (D.target.pts (s + 1)) ∈ K := by
    rw [← hsum]; exact K.sum_mem (fun e _ => hlen e.1 e.2)
  obtain ⟨D', h1, h2, h3⟩ := conj_congruentDissection_subfield D K ψ hK hKT
  obtain ⟨part', hcov', hdisj', hsum'⟩ := D'.toDissection.side_walk s
  have hchar := part_char D.toDissection s part hcov
  have hchar' := part_char D'.toDissection s part' hcov'
  -- the two partitions coincide: collinearity is polynomial
  have hcolD : ∀ e : Fin N × Fin 3, (Col (D.target.pts s) (D.target.pts (s + 1)) ((D.tile e.1).pts e.2) ∧
        Col (D.target.pts s) (D.target.pts (s + 1)) ((D.tile e.1).pts (e.2 + 1))) ↔
      (Col (D'.target.pts s) (D'.target.pts (s + 1)) ((D'.tile e.1).pts e.2) ∧
        Col (D'.target.pts s) (D'.target.pts (s + 1)) ((D'.tile e.1).pts (e.2 + 1))) := by
    intro e
    let Pk : Fin 2 → K := fun v => ⟨D.target.pts s v, hKT s v⟩
    let Qk : Fin 2 → K := fun v => ⟨D.target.pts (s + 1) v, hKT (s + 1) v⟩
    let p1 : Fin 2 → K := fun v => ⟨(D.tile e.1).pts e.2 v, hK e.1 e.2 v⟩
    let p2 : Fin 2 → K := fun v => ⟨(D.tile e.1).pts (e.2 + 1) v, hK e.1 (e.2 + 1) v⟩
    have a1 := col_transport K.subtype _ _ ((D.tile e.1).pts e.2) Pk Qk p1 (fun v => rfl) (fun v => rfl) (fun v => rfl)
    have a2 := col_transport K.subtype _ _ ((D.tile e.1).pts (e.2 + 1)) Pk Qk p2 (fun v => rfl) (fun v => rfl) (fun v => rfl)
    have b1 := col_transport ψ (D'.target.pts s) (D'.target.pts (s + 1)) ((D'.tile e.1).pts e.2) Pk Qk p1
      (fun v => h2 s v) (fun v => h2 (s + 1) v) (fun v => h1 e.1 e.2 v)
    have b2 := col_transport ψ (D'.target.pts s) (D'.target.pts (s + 1)) ((D'.tile e.1).pts (e.2 + 1)) Pk Qk p2
      (fun v => h2 s v) (fun v => h2 (s + 1) v) (fun v => h1 e.1 (e.2 + 1) v)
    rw [a1, a2, b1, b2]
  have hpart : part = part' := by
    ext e
    rw [hchar e, hchar' e, hcolD e]
  subst hpart
  -- lengths
  set len : Fin N × Fin 3 → K := fun e => ⟨dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)), hlen e.1 e.2⟩
    with hlendef
  set L : K := ⟨dist (D.target.pts s) (D.target.pts (s + 1)), hL⟩ with hLdef
  have hsumK : ∑ e ∈ part, len e = L := by
    apply Subtype.ext
    exact (map_sum K.subtype len part).trans hsum
  have hlinear : ∑ e ∈ part, ψ (len e) = ψ L := by rw [← map_sum, hsumK]
  -- dist' = |ψ(len)|
  have hdist_tile : ∀ e : Fin N × Fin 3, dist ((D'.tile e.1).pts e.2) ((D'.tile e.1).pts (e.2 + 1))
      = |ψ (len e)| := by
    intro e
    have h := h3 e.1 e.2 (e.2 + 1)
    have hsq : dist ((D'.tile e.1).pts e.2) ((D'.tile e.1).pts (e.2 + 1)) ^ 2 = ψ (len e) ^ 2 := by
      rw [h, ← map_pow]
      congr 1
    rw [← sq_eq_sq₀ dist_nonneg (abs_nonneg _), hsq, sq_abs]
  have hdist_side : dist (D'.target.pts s) (D'.target.pts (s + 1)) = |ψ L| := by
    let c2 : Fin 3 → Fin 2 → K := fun k v => ⟨D.target.pts k v, hKT k v⟩
    have e1 := dist_sq_of_coords ψ D'.target c2 (fun k v => h2 k v) s (s + 1)
    have e2 := dist_sq_of_coords K.subtype D.target c2 (fun k v => rfl) s (s + 1)
    have hd2 : d2 c2 s (s + 1) = L ^ 2 := by
      apply K.subtype.injective
      rw [← e2]
      simp [hLdef]
    rw [hd2, map_pow] at e1
    rw [← sq_eq_sq₀ dist_nonneg (abs_nonneg _), e1, sq_abs]
  have hsumabs : ∑ e ∈ part, |ψ (len e)| = |ψ L| := by
    rw [← hdist_side, ← hsum']
    exact Finset.sum_congr rfl (fun e _ => (hdist_tile e).symm)
  have hsign := sum_abs_eq_sign part (fun e => ψ (len e)) (by rw [hsumabs, hlinear])
  refine ⟨part, hL, hcov, hdisj, hchar, hsum, ?_, hsumabs⟩
  intro e he
  have hle := hsign e he
  rw [hlinear] at hle
  have hk3 : ∀ k : Fin 3, k ≠ k + 1 := by decide
  have hlenpos : 0 < dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) :=
    dist_pos.mpr ((D.tile e.1).indep.injective.ne (by
      have hk : ∀ k : Fin 3, k ≠ k + 1 := by decide
      exact hk e.2))
  have hLpos : 0 < dist (D.target.pts s) (D.target.pts (s + 1)) :=
    dist_pos.mpr (D.target.indep.injective.ne (by
      have hk : ∀ k : Fin 3, k ≠ k + 1 := by decide
      exact hk s))
  have hne1 : ψ (len e) ≠ 0 := by
    intro h0
    have : len e = 0 := (map_eq_zero ψ).mp h0
    have := congrArg Subtype.val this
    simp [hlendef] at this
    exact (D.tile e.1).indep.injective.ne (hk3 e.2) this
  have hne2 : ψ L ≠ 0 := by
    intro h0
    have : L = 0 := (map_eq_zero ψ).mp h0
    have := congrArg Subtype.val this
    simp [hLdef] at this
    exact D.target.indep.injective.ne (hk3 s) this
  exact lt_of_le_of_ne hle (Ne.symm (mul_ne_zero hne1 hne2))

/-- `sum_three_values` with the multiplicities' support exposed: `P ≠ 0` iff an edge of length `a` occurs, etc. -/
theorem sum_three_values_support {ι : Type*} (s : Finset ι) (len : ι → ℝ) (a b c : ℝ)
    (h : ∀ e ∈ s, len e = a ∨ len e = b ∨ len e = c) :
    ∃ P Q R : ℕ, ((P : ℝ) * a + (Q : ℝ) * b + (R : ℝ) * c = ∑ e ∈ s, len e)
      ∧ P + Q + R = s.card ∧ (P ≠ 0 → ∃ e ∈ s, len e = a) ∧ (Q ≠ 0 → ∃ e ∈ s, len e = b)
      ∧ (R ≠ 0 → ∃ e ∈ s, len e = c) := by
  classical
  obtain ⟨P, Q, R, h1, h2⟩ := sum_three_values s len a b c h
  -- recover the supports by re-deriving with the explicit filters
  refine ⟨(s.filter fun e => len e = a).card,
          (s.filter fun e => ¬ len e = a ∧ len e = b).card,
          (s.filter fun e => ¬ len e = a ∧ ¬ len e = b).card, ?_, ?_, ?_, ?_, ?_⟩
  · have hsplit1 := Finset.sum_filter_add_sum_filter_not s (fun e => len e = a) len
    have hsplit2 := Finset.sum_filter_add_sum_filter_not
      (s.filter fun e => ¬ len e = a) (fun e => len e = b) len
    rw [Finset.filter_filter, Finset.filter_filter] at hsplit2
    have hA : ∑ e ∈ s.filter (fun e => len e = a), len e
        = ((s.filter fun e => len e = a).card : ℝ) * a := by
      rw [Finset.sum_congr rfl (fun e he => (Finset.mem_filter.mp he).2),
        Finset.sum_const, nsmul_eq_mul]
    have hB : ∑ e ∈ s.filter (fun e => ¬ len e = a ∧ len e = b), len e
        = ((s.filter fun e => ¬ len e = a ∧ len e = b).card : ℝ) * b := by
      rw [Finset.sum_congr rfl (fun e he => (Finset.mem_filter.mp he).2.2),
        Finset.sum_const, nsmul_eq_mul]
    have hC : ∑ e ∈ s.filter (fun e => ¬ len e = a ∧ ¬ len e = b), len e
        = ((s.filter fun e => ¬ len e = a ∧ ¬ len e = b).card : ℝ) * c := by
      rw [Finset.sum_congr rfl (fun e he => ?_), Finset.sum_const, nsmul_eq_mul]
      have hmem := Finset.mem_filter.mp he
      rcases h e hmem.1 with h' | h' | h'
      · exact absurd h' hmem.2.1
      · exact absurd h' hmem.2.2
      · exact h'
    rw [hA] at hsplit1
    rw [hB, hC] at hsplit2
    linarith [hsplit1, hsplit2]
  · have h1 := Finset.filter_card_add_filter_neg_card_eq_card
      (s := s) (p := fun e => len e = a)
    have h2 := Finset.filter_card_add_filter_neg_card_eq_card
      (s := s.filter fun e => ¬ len e = a) (p := fun e => len e = b)
    rw [Finset.filter_filter, Finset.filter_filter] at h2
    omega
  · intro hP
    obtain ⟨e, he⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hP)
    exact ⟨e, (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2⟩
  · intro hQ
    obtain ⟨e, he⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hQ)
    exact ⟨e, (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2.2⟩
  · intro hR
    obtain ⟨e, he⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hR)
    have hmem := Finset.mem_filter.mp he
    rcases h e hmem.1 with h' | h' | h'
    · exact absurd h' hmem.2.1
    · exact absurd h' hmem.2.2
    · exact ⟨e, hmem.1, h'⟩

/-- **SL, typed form (what D6–D9 consume).**  `a, b, c ∈ K` the three tile-edge lengths.  For every side `s` of the
target there are a side length `L ∈ K` (`L = dist` of the side) and multiplicities `P, Q, R` (numbers of tile edges of
type `a`, `b`, `c` lying on the side) with

* the walk equation in `K`: `P a + Q b + R c = L`, hence (apply `ψ`) `P ψ(a) + Q ψ(b) + R ψ(c) = ψ(L)`,
* `P + Q + R ≤ 3N`,
* **signs**: `P ≠ 0 → 0 < ψ a · ψ L`, `Q ≠ 0 → 0 < ψ b · ψ L`, `R ≠ 0 → 0 < ψ c · ψ L`.

So an edge type occurs on a side only if `ψ` of its length has the sign of `ψ` of the side length (the paper's D5). -/
theorem side_type_sign {N : ℕ} (D : CongruentDissection N) (K : Subfield ℝ) (ψ : K →+* ℝ)
    (hK : ∀ i k v, (D.tile i).pts k v ∈ K) (hKT : ∀ k v, D.target.pts k v ∈ K)
    (a b c : K)
    (habc : ∀ (j : Fin N) (k : Fin 3),
      dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = (a : ℝ)
      ∨ dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = (b : ℝ)
      ∨ dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = (c : ℝ)) (s : Fin 3) :
    ∃ (L : K) (P Q R : ℕ), (L : ℝ) = dist (D.target.pts s) (D.target.pts (s + 1)) ∧
      (P : K) * a + (Q : K) * b + (R : K) * c = L ∧
      (P : ℝ) * ψ a + (Q : ℝ) * ψ b + (R : ℝ) * ψ c = ψ L ∧ P + Q + R ≤ 3 * N ∧
      (P ≠ 0 → 0 < ψ a * ψ L) ∧ (Q ≠ 0 → 0 < ψ b * ψ L) ∧ (R ≠ 0 → 0 < ψ c * ψ L) := by
  classical
  have hlen : ∀ i k, dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) ∈ K := by
    intro i k
    rcases habc i k with h | h | h <;> rw [h]
    · exact a.2
    · exact b.2
    · exact c.2
  obtain ⟨part, hL, -, -, -, hsum, hpos, -⟩ := side_sign_lemma D K ψ hK hKT hlen s
  obtain ⟨P, Q, R, hPQR, hcard, hPs, hQs, hRs⟩ := sum_three_values_support part
    (fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))) (a : ℝ) b c
    (fun e _ => habc e.1 e.2)
  refine ⟨⟨_, hL⟩, P, Q, R, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    push_cast
    rw [hPQR]; exact hsum
  · have : (P : K) * a + (Q : K) * b + (R : K) * c = ⟨_, hL⟩ := by
      apply Subtype.ext
      push_cast
      rw [hPQR]; exact hsum
    have h2 := congrArg ψ this
    simpa using h2
  · have hle : part.card ≤ Fintype.card (Fin N × Fin 3) := Finset.card_le_univ part
    simp only [Fintype.card_prod, Fintype.card_fin] at hle
    omega
  · intro hP
    obtain ⟨e, he, hea⟩ := hPs hP
    have := hpos e he
    have hk : (⟨dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)), hlen e.1 e.2⟩ : K) = a :=
      Subtype.ext hea
    rwa [hk] at this
  · intro hQ
    obtain ⟨e, he, hea⟩ := hQs hQ
    have := hpos e he
    have hk : (⟨dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)), hlen e.1 e.2⟩ : K) = b :=
      Subtype.ext hea
    rwa [hk] at this
  · intro hR
    obtain ⟨e, he, hea⟩ := hRs hR
    have := hpos e he
    have hk : (⟨dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)), hlen e.1 e.2⟩ : K) = c :=
      Subtype.ext hea
    rwa [hk] at this

end Erdos634.H1iSL

#print axioms Erdos634.H1iSL.sum_abs_eq_sign
#print axioms Erdos634.H1iSL.side_sign_lemma
#print axioms Erdos634.H1iSL.side_type_sign

import Mathlib

/-!
# Beeson (arXiv 1206.2229 v4) Lemmas 29 and 30: the graph `H`, the parallelogram step, parallel edges, lattice

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Sect. 9: Definition 9, Lemma 29, Definition 10,
Lemma 30), Beeson-Rosu, Laczkovich (DCG 48 (2012)), Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.

Setting (pure plane geometry, no tiling object needed for the algebra): a model triangle `M.P : Fin 3 → ℝ²`, a family of
tiles `v : ι → Fin 3 → ℝ²` congruent to it (`Cong`: all pairwise squared distances equal the model's, so each tile is an
isometric image, reflections allowed).  Label `p` = the model vertex `P p`; the side `{a, b}` has the label of the model side.

* `Conn v i j`: printed Definition 9: tiles `i ≠ j` share two vertices (points) and do not have the same corner at both
  (here: not the same labels at both ends; the printed "different angles" is the same thing when the model angles are
  distinct, which the printed hypothesis 3α+2β=π, α irrational gives).
* `Sep v`: the consequence of interior-disjointness used by the printed proof ("S ∪ T is a parallelogram"): two tiles
  sharing an edge have their third vertices strictly on opposite sides of it.
* `Model.distinct`: the three side lengths are pairwise distinct (implicit in the printed proof: "S and T are congruent
  and UV is the same side of each"; for 3α+2β=π, α irrational it follows from a ≠ b, a ≠ c, b ≠ c; recorded as a printed gap).
Results: `parallelogram_step`, `lemma29_parallel`, `lemma29_diff_lengths`, `lemma30_lattice`.
-/

namespace Erdos634.BeesonCol6

/-- cross product of plane vectors. -/
def cr (x y : ℝ × ℝ) : ℝ := x.1 * y.2 - x.2 * y.1
/-- squared length. -/
def sq (x : ℝ × ℝ) : ℝ := x.1 ^ 2 + x.2 ^ 2

/-- Model triangle with pairwise distinct side lengths. -/
structure Model where
  P : Fin 3 → ℝ × ℝ
  nondeg : cr (P 1 - P 0) (P 2 - P 0) ≠ 0
  distinct : ∀ p q p' q' : Fin 3, p ≠ q → p' ≠ q' → sq (P p - P q) = sq (P p' - P q') →
    (p = p' ∧ q = q') ∨ (p = q' ∧ q = p')

section
variable {ι : Type*} (M : Model) (v : ι → Fin 3 → ℝ × ℝ)

/-- every tile is congruent to the model (SSS). -/
def Cong : Prop := ∀ i p q, sq (v i p - v i q) = sq (M.P p - M.P q)

/-- opposite sides of a shared edge (consequence of disjoint interiors). -/
def Sep : Prop := ∀ (i j : ι) (p q p' q' r r' : Fin 3), i ≠ j → p ≠ q → p ≠ r → q ≠ r → p' ≠ q' → p' ≠ r' → q' ≠ r' →
  v i p = v j p' → v i q = v j q' →
  cr (v i q - v i p) (v i r - v i p) * cr (v i q - v i p) (v j r' - v i p) < 0

/-- Definition 9: connection in the graph `H`. -/
def Conn (i j : ι) : Prop :=
  i ≠ j ∧ ∃ p q p' q' : Fin 3, p ≠ q ∧ v i p = v j p' ∧ v i q = v j q' ∧ ¬ (p = p' ∧ q = q')

/-- connected-ness inside a set `C`: reachability by connections between members of `C`. -/
def ReachIn (C : Set ι) : ι → ι → Prop := Relation.ReflTransGen (fun s t => s ∈ C ∧ t ∈ C ∧ Conn v s t)

/-- corresponding sides parallel. -/
def Par (i j : ι) : Prop := ∀ a b : Fin 3, cr (v i b - v i a) (v j b - v j a) = 0
end

theorem cr_sq_formula (A B C : ℝ × ℝ) :
    (cr (B - A) (C - A)) ^ 2 = sq (B - A) * sq (C - A) - ((sq (B - A) + sq (C - A) - sq (B - C)) / 2) ^ 2 := by
  simp only [cr, sq, Prod.fst_sub, Prod.snd_sub]; ring

section
variable {ι : Type*} {M : Model} {v : ι → Fin 3 → ℝ × ℝ}

theorem Dsq (hc : Cong M v) (i : ι) :
    (cr (v i 1 - v i 0) (v i 2 - v i 0)) ^ 2 = (cr (M.P 1 - M.P 0) (M.P 2 - M.P 0)) ^ 2 := by
  rw [cr_sq_formula, cr_sq_formula, hc i 1 0, hc i 2 0, hc i 1 2]

theorem Dne (hc : Cong M v) (i : ι) : cr (v i 1 - v i 0) (v i 2 - v i 0) ≠ 0 := by
  intro h
  have h2 : (cr (M.P 1 - M.P 0) (M.P 2 - M.P 0)) ^ 2 = 0 := by rw [← Dsq hc i, h]; ring
  exact M.nondeg (pow_eq_zero_iff two_ne_zero |>.mp h2)

theorem sq_ne_zero_of_pos {x : ℝ × ℝ} (h : x ≠ 0) : sq x ≠ 0 := by
  intro h0
  apply h
  have h1 : x.1 ^ 2 = 0 := by simp only [sq] at h0; nlinarith [sq_nonneg x.1, sq_nonneg x.2]
  have h2 : x.2 ^ 2 = 0 := by simp only [sq] at h0; nlinarith [sq_nonneg x.1, sq_nonneg x.2]
  exact Prod.ext (pow_eq_zero_iff two_ne_zero |>.mp h1) (pow_eq_zero_iff two_ne_zero |>.mp h2)

/-- two sides of a tile with different label pairs: cross product squared equals `D^2`. -/
theorem cr_sides_sq (i : ι) (a b a' b' : Fin 3) (hab : a ≠ b) (hab' : a' ≠ b')
    (h1 : ¬ (a = a' ∧ b = b')) (h2 : ¬ (a = b' ∧ b = a')) :
    (cr (v i b - v i a) (v i b' - v i a')) ^ 2 = (cr (v i 1 - v i 0) (v i 2 - v i 0)) ^ 2 := by
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;> simp at hab hab' h1 h2 <;>
    simp [cr] <;> ring

theorem cr_sides_ne (hc : Cong M v) (i : ι) (a b a' b' : Fin 3) (hab : a ≠ b) (hab' : a' ≠ b')
    (h1 : ¬ (a = a' ∧ b = b')) (h2 : ¬ (a = b' ∧ b = a')) :
    cr (v i b - v i a) (v i b' - v i a') ≠ 0 := by
  intro h0
  have := cr_sides_sq (v := v) i a b a' b' hab hab' h1 h2
  rw [h0] at this
  exact Dne hc i (pow_eq_zero_iff two_ne_zero |>.mp (by rw [← this]; ring))

theorem P_sub_ne (a b : Fin 3) (hab : a ≠ b) : M.P a - M.P b ≠ 0 := by
  intro h
  have hP : M.P a = M.P b := sub_eq_zero.mp h
  have := M.nondeg
  fin_cases a <;> fin_cases b <;> simp at hab hP <;>
    exact this (by simp only [cr, Prod.fst_sub, Prod.snd_sub, hP]; ring)

theorem side_ne (hc : Cong M v) (i : ι) (a b : Fin 3) (hab : a ≠ b) : v i b - v i a ≠ 0 := by
  intro h
  have h0 : sq (v i b - v i a) = 0 := by rw [h]; simp [sq]
  rw [hc i b a] at h0
  exact sq_ne_zero_of_pos (P_sub_ne b a hab.symm) h0

/-- the point-reflection lemma (real form): `U V P Q` with swapped distances and `P, Q` strictly on opposite sides of `UV`. -/
theorem refl_real (w1 w2 x1 x2 y1 y2 : ℝ)
    (h1 : y1 ^ 2 + y2 ^ 2 = (x1 - w1) ^ 2 + (x2 - w2) ^ 2)
    (h2 : (y1 - w1) ^ 2 + (y2 - w2) ^ 2 = x1 ^ 2 + x2 ^ 2)
    (hs : (w1 * x2 - w2 * x1) * (w1 * y2 - w2 * y1) < 0) :
    x1 + y1 - w1 = 0 ∧ x2 + y2 - w2 = 0 := by
  have hzw : (x1 + y1 - w1) * w1 + (x2 + y2 - w2) * w2 = 0 := by linear_combination (1 / 2) * h1 - (1 / 2) * h2
  have hw : w1 ^ 2 + w2 ^ 2 ≠ 0 := by
    intro h
    have a1 : w1 = 0 := by nlinarith [sq_nonneg w1, sq_nonneg w2]
    have a2 : w2 = 0 := by nlinarith [sq_nonneg w1, sq_nonneg w2]
    rw [a1, a2] at hs; simp at hs
  have hz2 : (x1 + y1 - w1) ^ 2 + (x2 + y2 - w2) ^ 2 = 2 * ((x1 + y1 - w1) * x1 + (x2 + y2 - w2) * x2) := by
    linear_combination h1 - 2 * hzw
  have key1 : (w1 ^ 2 + w2 ^ 2) * ((x1 + y1 - w1) ^ 2 + (x2 + y2 - w2) ^ 2)
      = ((w1 * x2 - w2 * x1) + (w1 * y2 - w2 * y1)) ^ 2 := by
    have e : (w1 ^ 2 + w2 ^ 2) * ((x1 + y1 - w1) ^ 2 + (x2 + y2 - w2) ^ 2)
        = ((x1 + y1 - w1) * w1 + (x2 + y2 - w2) * w2) ^ 2 + ((w1 * x2 - w2 * x1) + (w1 * y2 - w2 * y1)) ^ 2 := by ring
    rw [e, hzw]; ring
  have key2 : (w1 ^ 2 + w2 ^ 2) * ((x1 + y1 - w1) * x1 + (x2 + y2 - w2) * x2)
      = ((w1 * x2 - w2 * x1) + (w1 * y2 - w2 * y1)) * (w1 * x2 - w2 * x1) := by
    have e : (w1 ^ 2 + w2 ^ 2) * ((x1 + y1 - w1) * x1 + (x2 + y2 - w2) * x2)
        = ((x1 + y1 - w1) * w1 + (x2 + y2 - w2) * w2) * (w1 * x1 + w2 * x2)
          + ((w1 * x2 - w2 * x1) + (w1 * y2 - w2 * y1)) * (w1 * x2 - w2 * x1) := by ring
    rw [e, hzw]; ring
  set c := w1 * x2 - w2 * x1 with hc
  set c' := w1 * y2 - w2 * y1 with hc'
  have k3 : (c + c') * (c' - c) = 0 := by
    have : (c + c') ^ 2 = 2 * ((c + c') * c) := by
      calc (c + c') ^ 2 = (w1 ^ 2 + w2 ^ 2) * ((x1 + y1 - w1) ^ 2 + (x2 + y2 - w2) ^ 2) := key1.symm
        _ = (w1 ^ 2 + w2 ^ 2) * (2 * ((x1 + y1 - w1) * x1 + (x2 + y2 - w2) * x2)) := by rw [hz2]
        _ = 2 * ((w1 ^ 2 + w2 ^ 2) * ((x1 + y1 - w1) * x1 + (x2 + y2 - w2) * x2)) := by ring
        _ = 2 * ((c + c') * c) := by rw [key2]
    linear_combination this
  have hsum : c + c' = 0 := by
    rcases mul_eq_zero.mp k3 with h | h
    · exact h
    · exfalso
      have : c' = c := by linarith
      rw [this] at hs
      nlinarith [sq_nonneg c]
  have hz0 : (w1 ^ 2 + w2 ^ 2) * ((x1 + y1 - w1) ^ 2 + (x2 + y2 - w2) ^ 2) = 0 := by rw [key1, hsum]; ring
  have hz : (x1 + y1 - w1) ^ 2 + (x2 + y2 - w2) ^ 2 = 0 := by
    rcases mul_eq_zero.mp hz0 with h | h
    · exact absurd h hw
    · exact h
  have a1 : (x1 + y1 - w1) ^ 2 = 0 := le_antisymm (by linarith [sq_nonneg (x2 + y2 - w2)]) (sq_nonneg _)
  have a2 : (x2 + y2 - w2) ^ 2 = 0 := le_antisymm (by linarith [sq_nonneg (x1 + y1 - w1)]) (sq_nonneg _)
  exact ⟨pow_eq_zero_iff two_ne_zero |>.mp a1, pow_eq_zero_iff two_ne_zero |>.mp a2⟩

theorem refl_pt (U V P Q : ℝ × ℝ) (h1 : sq (Q - U) = sq (P - V)) (h2 : sq (Q - V) = sq (P - U))
    (hs : cr (V - U) (P - U) * cr (V - U) (Q - U) < 0) : Q = U + V - P := by
  simp only [sq, cr, Prod.fst_sub, Prod.snd_sub] at h1 h2 hs
  obtain ⟨a, b⟩ := refl_real (V.1 - U.1) (V.2 - U.2) (P.1 - U.1) (P.2 - U.2) (Q.1 - U.1) (Q.2 - U.2)
    (by linear_combination h1) (by linear_combination h2) hs
  ext
  · simp; linarith
  · simp; linarith

section
variable {ι : Type*} {M : Model} {v : ι → Fin 3 → ℝ × ℝ}

theorem exists_third (p q : Fin 3) : ∃ r : Fin 3, r ≠ p ∧ r ≠ q := by revert p q; decide

/-- The parallelogram step of Lemma 29: connected tiles `i`, `j` have the labels at the two shared vertices swapped and
the third vertex of `j` is the point reflection of the third vertex of `i` in the midpoint of the shared edge. -/
theorem parallelogram_step (hc : Cong M v) (hs : Sep v) {i j : ι} (h : Conn v i j) :
    ∃ p q r : Fin 3, p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ v j q = v i p ∧ v j p = v i q ∧ v j r = v i p + v i q - v i r := by
  obtain ⟨hij, p, q, p', q', hpq, e1, e2, hne⟩ := h
  have hp'q' : p' ≠ q' := by
    intro h'
    apply hpq
    have : v i p = v i q := by rw [e1, e2, h']
    by_contra hh
    have := side_ne hc i p q hh
    exact this (by rw [‹v i p = v i q›]; simp)
  have hlen : sq (M.P p - M.P q) = sq (M.P p' - M.P q') := by
    rw [← hc i p q, ← hc j p' q', e1, e2]
  rcases M.distinct p q p' q' hpq hp'q' hlen with ⟨a, b⟩ | ⟨a, b⟩
  · exact absurd ⟨a, b⟩ hne
  · subst a; subst b
    obtain ⟨r, hrp, hrq⟩ := exists_third p q
    have hpr : p ≠ r := fun h => hrp h.symm
    have hqr : q ≠ r := fun h => hrq h.symm
    refine ⟨p, q, r, hpq, hpr, hqr, ?_, ?_, ?_⟩
    · rw [← e1]
    · rw [← e2]
    · have hsp := hs i j p q q p r r hij hpq hpr hqr hpq.symm hqr hpr (by rw [e1]) (by rw [e2])
      -- distances
      have d1 : sq (v j r - v i p) = sq (v i r - v i q) := by
        rw [e1, hc j r q, hc i r q]
      have d2 : sq (v j r - v i q) = sq (v i r - v i p) := by
        rw [e2, hc j r p, hc i r p]
      have := refl_pt (v i p) (v i q) (v i r) (v j r) d1 d2 (by simpa using hsp)
      rw [this]
end
end

section
variable {ι : Type*} {M : Model} {v : ι → Fin 3 → ℝ × ℝ}

theorem cr_trans_of_ne {x y z : ℝ × ℝ} (hx : x ≠ 0) (hxy : cr x y = 0) (hxz : cr x z = 0) : cr y z = 0 := by
  by_cases h1 : x.1 = 0
  · have h2 : x.2 ≠ 0 := fun h2 => hx (Prod.ext h1 h2)
    have e : x.2 * cr y z = cr x z * y.2 - cr x y * z.2 := by simp only [cr]; ring
    rw [hxz, hxy] at e; simp at e
    rcases e with h | h
    · exact absurd h h2
    · exact h
  · have e : x.1 * cr y z = cr x z * y.1 - cr x y * z.1 := by simp only [cr]; ring
    rw [hxz, hxy] at e; simp at e
    rcases e with h | h
    · exact absurd h h1
    · exact h

theorem cover3 : ∀ p q r a : Fin 3, p ≠ q → p ≠ r → q ≠ r → a = p ∨ a = q ∨ a = r := by decide

/-- one connection gives parallel corresponding sides. -/
theorem conn_par (hc : Cong M v) (hs : Sep v) {i j : ι} (h : Conn v i j) : Par v i j := by
  obtain ⟨p, q, r, hpq, hpr, hqr, e1, e2, e3⟩ := parallelogram_step hc hs h
  intro a b
  have key : ∀ a : Fin 3, (a = p ∨ a = q ∨ a = r) := fun a => cover3 p q r a hpq hpr hqr
  rcases key a with rfl | rfl | rfl <;> rcases key b with rfl | rfl | rfl <;>
    simp [cr, e1, e2, e3] <;> ring

theorem par_refl (i : ι) : Par v i i := by
  intro a b; simp only [cr]; ring

theorem par_trans (hc : Cong M v) {i j k : ι} (h1 : Par v i j) (h2 : Par v j k) : Par v i k := by
  intro a b
  by_cases hab : a = b
  · subst hab; simp [cr]
  · have h1' : cr (v j b - v j a) (v i b - v i a) = 0 := by
      have := h1 a b; simp only [cr] at this ⊢; linarith
    exact cr_trans_of_ne (side_ne hc j a b hab) h1' (h2 a b)


theorem par_of_reach (hc : Cong M v) (hs : Sep v) {C : Set ι} {S T : ι} (hr : ReachIn v C S T) : Par v S T := by
  induction hr with
  | refl => exact par_refl _
  | tail _ hbc ih => exact par_trans hc ih (conn_par hc hs hbc.2.2)

/-- **Lemma 29 (first sentence).**  Tiles `S`, `T` of a connected set `C` (non-isosceles, i.e. the model has distinct side
lengths): two edges of the same length are parallel or on the same line (`cr = 0`). -/
theorem lemma29_parallel (hc : Cong M v) (hs : Sep v) {C : Set ι} {S T : ι} (hr : ReachIn v C S T)
    (a b a' b' : Fin 3) (hab : a ≠ b) (hab' : a' ≠ b')
    (hlen : sq (v S b - v S a) = sq (v T b' - v T a')) :
    cr (v S b - v S a) (v T b' - v T a') = 0 := by
  have hl : sq (M.P b - M.P a) = sq (M.P b' - M.P a') := by rw [← hc S b a, ← hc T b' a', hlen]
  rcases M.distinct b a b' a' hab.symm hab'.symm hl with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · subst e1; subst e2; exact par_of_reach hc hs hr a b
  · subst e1; subst e2
    have := par_of_reach hc hs hr a b
    simp only [cr, Prod.fst_sub, Prod.snd_sub] at this ⊢; linarith

/-- **Lemma 29 (second sentence).**  Two tile edges of different lengths lying on one line (all four endpoints collinear)
do not belong to one connected set. -/
theorem lemma29_diff_lengths (hc : Cong M v) (hs : Sep v) {C : Set ι} {S T : ι} (hr : ReachIn v C S T)
    (a b a' b' : Fin 3) (hab : a ≠ b) (hab' : a' ≠ b')
    (hlen : sq (v S b - v S a) ≠ sq (v T b' - v T a'))
    (hcol1 : cr (v S b - v S a) (v T a' - v S a) = 0) (hcol2 : cr (v S b - v S a) (v T b' - v S a) = 0) : False := by
  have hpar : cr (v S b - v S a) (v T b' - v T a') = 0 := by
    have : v T b' - v T a' = (v T b' - v S a) - (v T a' - v S a) := by abel
    rw [this]; simp only [cr, Prod.fst_sub, Prod.snd_sub] at hcol1 hcol2 ⊢; linarith
  have hPar := par_of_reach hc hs hr
  have h3 : cr (v T b - v T a) (v T b' - v T a') = 0 := by
    have h1' : cr (v S b - v S a) (v T b - v T a) = 0 := hPar a b
    exact cr_trans_of_ne (side_ne hc S a b hab) h1' hpar
  apply cr_sides_ne hc T a b a' b' hab hab' _ _ h3
  · rintro ⟨e1, e2⟩; subst e1; subst e2; exact hlen (by rw [hc S b a, hc T b a])
  · rintro ⟨e1, e2⟩; subst e1; subst e2
    apply hlen
    rw [hc S b a, hc T a b]
    simp only [sq, Prod.fst_sub, Prod.snd_sub]; ring

/-- **Lemma 30.**  A connected set `C` of tiles is a lattice tiling: all vertices lie in the (translated) lattice
`O + ℤ e₁ + ℤ e₂`, `e₁, e₂` independent (`cr e₁ e₂ ≠ 0`), generated by the sides of one tile `T₀`. -/
theorem lemma30_lattice (hc : Cong M v) (hs : Sep v) {C : Set ι} {T0 : ι} :
    ∃ O e1 e2 : ℝ × ℝ, cr e1 e2 ≠ 0 ∧
      ∀ T, ReachIn v C T0 T → ∀ p : Fin 3, ∃ m n : ℤ, v T p = O + (m : ℝ) • e1 + (n : ℝ) • e2 := by
  refine ⟨v T0 0, v T0 1 - v T0 0, v T0 2 - v T0 0, Dne hc T0, ?_⟩
  intro T hr
  induction hr with
  | refl =>
    intro p
    fin_cases p
    · exact ⟨0, 0, by simp⟩
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  | tail _ hbc ih =>
    rename_i S T'
    obtain ⟨p, q, r, hpq, hpr, hqr, e1, e2, e3⟩ := parallelogram_step hc hs hbc.2.2
    obtain ⟨m1, n1, h1⟩ := ih p
    obtain ⟨m2, n2, h2⟩ := ih q
    obtain ⟨m3, n3, h3⟩ := ih r
    intro a
    rcases cover3 p q r a hpq hpr hqr with rfl | rfl | rfl
    · exact ⟨m2, n2, by rw [e2, h2]⟩
    · exact ⟨m1, n1, by rw [e1, h1]⟩
    · refine ⟨m1 + m2 - m3, n1 + n2 - n3, ?_⟩
      rw [e3, h1, h2, h3]
      ext <;> simp <;> ring

end
end Erdos634.BeesonCol6

#print axioms Erdos634.BeesonCol6.parallelogram_step
#print axioms Erdos634.BeesonCol6.lemma29_parallel
#print axioms Erdos634.BeesonCol6.lemma29_diff_lengths
#print axioms Erdos634.BeesonCol6.lemma30_lattice

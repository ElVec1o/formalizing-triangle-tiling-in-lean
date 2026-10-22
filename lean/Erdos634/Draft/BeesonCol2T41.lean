import Mathlib
import Erdos634.Draft.CVCCevianCut

/-!
# Beeson-Rosu (arXiv 2607.23453 v2) Theorem 41 (j = 1, `(2 alpha, beta, alpha+beta)`): the gluing step, as dissections

NOTE, UNAUDITED.  Credit: Michael Beeson and Rosu (arXiv 2607.23453 v2, Lemma 40, Theorem 41, Theorem 37), Beeson (arXiv 1206.2229 v4,
Theorem 10), Laczkovich, Beeson-Zhang.  The fan decomposition `fan_cover`/`fan_disjoint`, `triOf`, `selfDissection`, `transport`
are from `Draft/CVCCevianCut.lean` (this project); formalization debt, not progress on the /goal outcomes.

Printed proof of Theorem 41: "tacking a quadratic tiling onto side AC as described in Lemma 40 ... we construct a j = 1 tiling of the
isosceles triangle of shape (beta, beta, 3 alpha). But that contradicts Theorem 37."

* `t41_glue`: from ANY `CongruentDissection D2` of a triangle `PQR` with sides `|PQ| = K c`, `|PR| = K b`, `|QR| = M (b+c)`
  (the sides of the triquadratic triangle, Lemma 39) with model tile of sides `(a,b,c) = (km, k^2-m^2, k^2)` and `K m = M k`
  (so `(M,K) = j (m,k)`), it builds a `CongruentDissection` of the triangle `Delta = (P, A', Q)` with `A'` on the line `QR` beyond
  `R`, `|RA'| = K a`: sides `K c, K c, M (b + 2c)` (the isosceles-beta triangle, Lemma 40), same model, `K^2 + N` tiles.
  No angle hypotheses are used: everything is determined by the three side lengths (law of cosines is replaced by the
  coordinate identity `|A'P|^2 = ...`).
* `NoIsoJ1` is the statement of printed Theorem 37 in side-length form (a NAMED hypothesis; Theorem 37 is formalized
  only partially in the project).  `t41`: `NoIsoJ1 -> no j = 1 tiling of the triquadratic triangle`.

Hypotheses not witnessed: for `j = 1` a tiling `D2` is exactly what Theorem 41 says cannot exist, so `t41_glue` is a construction
about a hypothetical dissection (like every "no tiling exists" reduction); the construction is for general `j` (`K = j k`, `M = j m`)
where such dissections exist (Fig. 10 of the printed paper: 28 tiles, `(m,k) = (1,2)`, `j = 2`), not formalized here.
-/

namespace Erdos634.BeesonCol2T41

open Erdos634.Geometry Erdos634.Draft.CVCCevianCut Erdos634.Draft.FDBBaseBetaE1

/-- `Cut (K t) t (K^2)` placed at any triangle with sides `K (a,b,c)`, for a tile with sides `(a,b,c)`. -/
theorem tileK_gen (t T : Tri) (K : ℕ) (hK : 0 < K) {a b c : ℝ} (ht : HasSides t a b c)
    (hT : HasSides T ((K : ℝ) * a) ((K : ℝ) * b) ((K : ℝ) * c)) :
    ∃ E : CongruentDissection (K * K * 1), E.target.carrier = T.carrier ∧ E.model = t := by
  obtain ⟨D, hDt, hDm⟩ := Erdos634.Realizable.cut_scale (T := t) (t := t) (N := 1)
    ⟨selfDissection t, rfl, rfl⟩ K hK
  have hS := Erdos634.Draft.FDCCevianAtom.hasSides_scaleN ht K hK
  obtain ⟨τ, h1, h2, h3⟩ := hT
  have hc : (Erdos634.Realizable.scaleN K hK t).Congruent T :=
    Tri.Congruent.trans (congruent_of_hasSides hS (U := T.relabel τ) h1 h2 h3)
      (Tri.congruent_relabel T τ).symm
  obtain ⟨E, hEc, hEm⟩ := transport D T (by rw [hDt]; exact hc)
  exact ⟨E, hEc, hEm.trans hDm⟩

theorem t41_glue {K M k m N : ℕ} {a b c : ℝ} (hm : 0 < m) (hmk : m < k) (hK : 0 < K) (hM : 0 < M)
    (hKM : (K : ℝ) * m = M * k)
    (ha : a = k * m) (hb : b = (k : ℝ) ^ 2 - m ^ 2) (hc : c = (k : ℝ) ^ 2)
    (D2 : CongruentDissection N) (ht : HasSides D2.model a b c)
    (P Q R : Plane) (hcr : cr P Q R ≠ 0) (hcar : D2.target.carrier = convexHull ℝ {P, Q, R})
    (hPQ : dist P Q = K * c) (hPR : dist P R = K * b) (hQR : dist Q R = M * (b + c)) :
    ∃ (Δ : Tri) (D' : CongruentDissection (K * K * 1 + N)), D'.target = Δ ∧
      HasSides Δ (K * c) (K * c) (M * (b + 2 * c)) ∧ D'.model = D2.model := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hmk' : (m : ℝ) < k := by exact_mod_cast hmk
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have ha0 : 0 < a := by rw [ha]; positivity
  have hc0 : 0 < c := by rw [hc]; positivity
  have hb0 : 0 < b := by rw [hb]; nlinarith
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = M * (b + c) := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; positivity
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = K * a / u := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs]; positivity
  have hsu : s * u = K * a := by rw [hs]; field_simp
  have hKa : (K : ℝ) * a = M * c := by rw [ha, hc]; linear_combination (k : ℝ) * hKM
  obtain ⟨A, hA⟩ : ∃ A : Plane, A = R + s • (R - Q) := ⟨_, rfl⟩
  have hA0 : A 0 = R 0 + s * (R 0 - Q 0) := by rw [hA]; simp
  have hA1 : A 1 = R 1 + s * (R 1 - Q 1) := by rw [hA]; simp
  rw [← hu] at hQR
  have hPQ' := sqd_of_dist _ _ _ hPQ
  have hPR' := sqd_of_dist _ _ _ hPR
  have hQR' := sqd_of_dist _ _ _ hQR
  -- distances from A
  have dRA : dist R A = K * a := by
    rw [dist_eq_norm, hA]
    have : R - (R + s • (R - Q)) = (-s) • (R - Q) := by module
    rw [this, norm_smul, ← dist_eq_norm, dist_comm, hQR, Real.norm_eq_abs, abs_neg, abs_of_pos hs0, hsu]
  have dAQ : dist A Q = M * (b + 2 * c) := by
    rw [dist_eq_norm, hA]
    have : R + s • (R - Q) - Q = (1 + s) • (R - Q) := by module
    rw [this, norm_smul, ← dist_eq_norm, dist_comm, hQR, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have : (1 + s) * u = u + K * a := by linear_combination hsu
    rw [this, hKa, hu]; ring
  have key : ((K : ℝ) * b) ^ 2 + s * u ^ 2 = ((K : ℝ) * c) ^ 2 := by
    have e1 : s * u ^ 2 = K * a * u := by linear_combination u * hsu
    rw [e1, hu, ha, hb, hc]
    linear_combination (-(((k : ℝ) ^ 2 - m ^ 2 + k ^ 2) * K * m)) * hKM
  have dAP : dist A P = K * c := by
    apply dist_of_sqd _ _ _ (by positivity)
    rw [hA0, hA1]
    linear_combination (1 + s) * hPR' + (s + s ^ 2) * hQR' - s * hPQ' + (1 + s) * key
  -- the fan point: R = A + tF (Q - A)
  obtain ⟨tF, htF⟩ : ∃ tF : ℝ, tF = s / (1 + s) := ⟨_, rfl⟩
  have htF0 : 0 < tF := by rw [htF]; positivity
  have htF1 : tF < 1 := by rw [htF, div_lt_one (by positivity)]; linarith
  have hRfan : R = A + tF • (Q - A) := by
    ext i
    fin_cases i
    · change R 0 = A 0 + tF * (Q 0 - A 0)
      rw [hA0, htF]; field_simp; ring
    · change R 1 = A 1 + tF * (Q 1 - A 1)
      rw [hA1, htF]; field_simp; ring
  have c1 : cr P A Q ≠ 0 := by
    have : cr P A Q = -(1 + s) * cr P Q R := by unfold cr; rw [hA0, hA1]; ring
    rw [this]; exact mul_ne_zero (neg_ne_zero.mpr (by positivity)) hcr
  have c2 : cr P A R ≠ 0 := by
    have : cr P A R = -s * cr P Q R := by unfold cr; rw [hA0, hA1]; ring
    rw [this]; exact mul_ne_zero (neg_ne_zero.mpr hs0.ne') hcr
  have hfan := fan_cover P A Q R tF htF0 htF1 hRfan
  have hdis := fan_disjoint P A Q R tF htF0 htF1 hRfan c1
  let T1 : Tri := triOf P A R c2
  let Δ : Tri := triOf P A Q c1
  have hT1 : HasSides T1 ((K : ℝ) * a) ((K : ℝ) * b) ((K : ℝ) * c) := by
    refine ⟨Equiv.refl _, ?_, ?_, ?_⟩
    · show dist A R = _
      rw [dist_comm, dRA]
    · show dist R P = _
      rw [dist_comm, hPR]
    · show dist P A = _
      rw [dist_comm, dAP]
  obtain ⟨E, hEc, hEm⟩ := tileK_gen D2.model T1 K hK ht hT1
  have hcov : E.target.carrier ∪ D2.target.carrier = Δ.carrier := by
    rw [hEc, hcar, carrier_triOf, show Δ.carrier = convexHull ℝ {P, A, Q} from carrier_triOf _ _ _ _, hfan,
      Set.pair_comm Q R]
  have hdisj : Disjoint (interior E.target.carrier) (interior D2.target.carrier) := by
    rw [hEc, hcar, carrier_triOf, Set.pair_comm Q R]; exact hdis
  refine ⟨Δ, unionCongruentDissection Δ E D2 (hEm) hcov hdisj, rfl, ?_, hEm⟩
  refine ⟨Equiv.swap 0 2, ?_, ?_, ?_⟩
  · show dist A P = _
    rw [dAP]
  · show dist P Q = _
    rw [hPQ]
  · show dist Q A = _
    rw [dist_comm, dAQ]

/-- Printed Theorem 37 in side-length form: no `CongruentDissection` with model tile `(a,b,c)` has target with sides
`(k c, k c, m (b + 2c))` (the isosceles-beta triangle with `j = 1`).  A NAMED hypothesis of `t41`. -/
def NoIsoJ1 (a b c : ℝ) (k m : ℕ) : Prop :=
  ∀ (N' : ℕ) (D' : CongruentDissection N'),
    HasSides D'.target ((k : ℝ) * c) ((k : ℝ) * c) ((m : ℝ) * (b + 2 * c)) → HasSides D'.model a b c → False

/-- **Printed Theorem 41, `j = 1`**, given printed Theorem 37 (`NoIsoJ1`, named): there is no `CongruentDissection` of a triangle
with sides `(k c, k b, m (b + c))` (the `j = 1` triquadratic triangle, Lemma 39) by the tile `(km, k^2 - m^2, k^2)`. -/
theorem t41 {k m N : ℕ} {a b c : ℝ} (H37 : NoIsoJ1 a b c k m) (hm : 0 < m) (hmk : m < k)
    (ha : a = k * m) (hb : b = (k : ℝ) ^ 2 - m ^ 2) (hc : c = (k : ℝ) ^ 2)
    (D2 : CongruentDissection N) (ht : HasSides D2.model a b c)
    (P Q R : Plane) (hcr : cr P Q R ≠ 0) (hcar : D2.target.carrier = convexHull ℝ {P, Q, R})
    (hPQ : dist P Q = k * c) (hPR : dist P R = k * b) (hQR : dist Q R = m * (b + c)) : False := by
  obtain ⟨Δ, D', hD', hs, hmod⟩ := t41_glue (K := k) (M := m) hm hmk (by omega) hm (mul_comm _ _) ha hb hc D2 ht P Q R hcr hcar
    hPQ hPR hQR
  exact H37 _ D' (hD' ▸ hs) (hmod ▸ ht)

end Erdos634.BeesonCol2T41

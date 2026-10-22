import Erdos634.BaseWalkGeneral
import Erdos634.AreaDet
import Erdos634.Draft.ZhangRat6Arith

/-!
# Zhang Lemma 3, geometric part: a tiling of an equilateral triangle gives `X in N` and `X^2 = a b N`

Zhang (arXiv 2512.22696v4) Lemma 3: "If `a, b` are square-free, then if `X` is equiconstructible, then we must have
`X = m a b`."  Proof printed: "We need `X^2 = abN`, where `N` is the number of tiles used. Since `gcd(a,b) = 1`, ... ".
`ZhangRat6Arith.lemma3` proved the arithmetic core with `X in N` and `X^2 = abN` as hypotheses.  Here both are DERIVED
from a real `CongruentDissection` of an equilateral target:
* `target_side_walk`: every side of the target of a `CongruentDissection` with scalene model is a natural
  combination `P s0 + Q s1 + R s2` of the model's side lengths (`SideWalk.side_walk_of_dissection` with the generic
  wall data `wallFun`/`dirFun`, sign of `dir` fixed by `le_total`);
* `det_target_eq`: `|det target| = N |det model|` from the area identity (`congruentDissection_volume_target`,
  `volume_stdCarrier_half`);
* `det_sq_sides`: `4 det^2 = 4 s2^2 s1^2 - (s2^2 + s1^2 - s0^2)^2` in the side lengths;
* `lemma3_geom`: model sides `(sideOpp 0, 1, 2) = (A, B, C)` naturals with `C^2 = A^2+B^2+AB` (the project's
  `RTri` convention `|12|=a, |20|=b, |01|=c`), equilateral target of side `X`  =>  `X = X'` natural, `X'^2 = A B N`;
* `zhang_lemma3_geom`: with `A, B` squarefree and coprime, `A B | X'`.
UNAUDITED.  Credit Zhang (arXiv 2512.22696v4), Beeson, Beeson-Zhang, Laczkovich.
-/

set_option maxHeartbeats 3200000

namespace Erdos634.ZhangRat7Int

open Erdos634.Geometry Erdos634.Geometry.Dissection Erdos634.SideWall Erdos634.TilePlacement
  Erdos634.SideWalk Erdos634.AreaDet MeasureTheory

theorem target_side_walk {N : ℕ} (D : CongruentDissection N) (hN : 0 < N)
    (hscalene : ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m') (k : Fin 3) :
    ∃ Pc Qc Rc : ℕ, dist (D.target.pts k) (D.target.pts (k + 1))
      = Pc * sideOpp D.model 0 + Qc * sideOpp D.model 1 + Rc * sideOpp D.model 2 := by
  have hne : k ≠ k + 1 := by fin_cases k <;> decide
  have hab : D.target.pts k ≠ D.target.pts (k + 1) := Erdos634.TilePlacement.pts_ne D.target hne
  have hthirdD : ∀ p ∈ Erdos634.BaseChain.wallList D.toDissection (wallFun D.target k) 0,
      wallFun D.target k ((D.tile p.1).pts (p.2 + 2)) < 0 :=
    hthird_general D.toDissection (wallFun D.target k) 0 (wallFun_linear_ne_zero D.target k)
      (fun y hy => by simpa using wallFun_le D.target k hy)
  have hsc : sideOpp D.model 0 ≠ sideOpp D.model 1 ∧ sideOpp D.model 0 ≠ sideOpp D.model 2 ∧
      sideOpp D.model 1 ≠ sideOpp D.model 2 :=
    ⟨hscalene 0 1 (by decide), hscalene 0 2 (by decide), hscalene 1 2 (by decide)⟩
  rcases le_total ((dirFun D.target k).linear (D.target.pts k))
      ((dirFun D.target k).linear (D.target.pts (k + 1))) with h | h
  · exact side_walk_of_dissection D (wallFun D.target k) 0 (dirFun D.target k).linear
      (hker_wallFun D.target k) (fun y hy => wallFun_le D.target k hy) (D.target.pts k)
      (D.target.pts (k + 1)) hab h (edge_subset_frontier D.target k)
      (fun y hy => wallFun_eq_zero D.target k hy) (hface_wallFun D.target k) hthirdD
      (hiso_wallFun' D.target k) hsc hN
  · exact side_walk_of_dissection D (wallFun D.target k) 0 (-(dirFun D.target k).linear)
      (fun v h1 h2 => hker_wallFun D.target k v h1 (by simpa using h2))
      (fun y hy => wallFun_le D.target k hy) (D.target.pts k)
      (D.target.pts (k + 1)) hab (by simpa using h) (edge_subset_frontier D.target k)
      (fun y hy => wallFun_eq_zero D.target k hy) (hface_wallFun D.target k) hthirdD
      (fun p q hp hq => by
        rw [hiso_wallFun' D.target k p q hp hq]
        simp only [LinearMap.neg_apply]
        rw [← abs_neg]; congr 1; ring) hsc hN

theorem dist_sq_coord (p q : Plane) : dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
  simp [Real.dist_eq, sq_abs]

theorem det_sq_sides (T : Erdos634.Geometry.Tri) :
    4 * (detTri T) ^ 2 = 4 * (sideOpp T 2) ^ 2 * (sideOpp T 1) ^ 2
      - ((sideOpp T 2) ^ 2 + (sideOpp T 1) ^ 2 - (sideOpp T 0) ^ 2) ^ 2 := by
  have e2 : sideOpp T 2 = dist (T.pts 0) (T.pts 1) := rfl
  have e1 : sideOpp T 1 = dist (T.pts 2) (T.pts 0) := rfl
  have e0 : sideOpp T 0 = dist (T.pts 1) (T.pts 2) := rfl
  rw [e2, e1, e0, dist_sq_coord, dist_sq_coord, dist_sq_coord, detTri_eq]
  simp only [PiLp.sub_apply]
  ring

theorem det_target_eq {N : ℕ} (D : CongruentDissection N) :
    |detTri D.target| = N * |detTri D.model| := by
  have h := Erdos634.CongruentArea.congruentDissection_volume_target D
  rw [volume_eq_det_mul, volume_eq_det_mul, volume_stdCarrier_half] at h
  have h2 := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
    ENNReal.toReal_ofReal (abs_nonneg _)] at h2
  simp at h2
  linarith

theorem ne_of_rel (A B C : ℕ) (hh : C * C = A * A + B * B + A * B) (hcop : Nat.Coprime A B) : A ≠ B := by
  rintro rfl
  have h1 : A = 1 := by simpa using hcop
  subst h1
  have : C * C = 3 := by simpa using hh
  rcases Nat.lt_or_ge C 2 with h2 | h2
  · interval_cases C <;> omega
  · nlinarith

/-- **Lemma 3, geometric part.** -/
theorem lemma3_geom {N : ℕ} (A B C : ℕ) (hA : 0 < A) (hB : 0 < B) (hh : C * C = A * A + B * B + A * B)
    (hcop : Nat.Coprime A B) (D : CongruentDissection N) (hN : 0 < N)
    (h0 : sideOpp D.model 0 = A) (h1 : sideOpp D.model 1 = B) (h2 : sideOpp D.model 2 = C)
    (X : ℝ) (hX : ∀ j, sideOpp D.target j = X) :
    ∃ X' : ℕ, X = X' ∧ X' * X' = A * B * N := by
  have hAB := ne_of_rel A B C hh hcop
  have hCA : A ≠ C := by intro h; subst h; nlinarith [Nat.mul_pos hA hB]
  have hCB : B ≠ C := by intro h; subst h; nlinarith [Nat.mul_pos hA hB]
  have hsc : ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m' := by
    intro m m' hm
    fin_cases m <;> fin_cases m' <;> simp [h0, h1, h2] <;> first | exact absurd rfl hm | skip
    all_goals first
      | exact_mod_cast hAB | exact_mod_cast hAB.symm | exact_mod_cast hCA | exact_mod_cast hCA.symm
      | exact_mod_cast hCB | exact_mod_cast hCB.symm
  obtain ⟨P, Q, R, hw⟩ := target_side_walk D hN hsc 0
  have hXd : X = dist (D.target.pts 0) (D.target.pts (0 + 1)) := by
    rw [← hX 2]; rfl
  refine ⟨P * A + Q * B + R * C, ?_, ?_⟩
  · rw [hXd, hw, h0, h1, h2]; push_cast; ring
  · have hXpos : 0 < X := by
      rw [hXd]
      exact dist_pos.mpr (Erdos634.TilePlacement.pts_ne D.target (by decide))
    have hdt := det_sq_sides D.target
    have hdm := det_sq_sides D.model
    rw [hX 2, hX 1, hX 0] at hdt
    rw [h0, h1, h2] at hdm
    have hrel : (C : ℝ) ^ 2 = A ^ 2 + B ^ 2 + A * B := by exact_mod_cast (by nlinarith [hh] : C ^ 2 = A ^ 2 + B ^ 2 + A * B)
    have habs := det_target_eq D
    have hsq : (detTri D.target) ^ 2 = (N : ℝ) ^ 2 * (detTri D.model) ^ 2 := by
      rw [← sq_abs (detTri D.target), habs, mul_pow, sq_abs]
    have e1 : (X ^ 2) ^ 2 = ((N : ℝ) * A * B) ^ 2 := by
      have : 3 * (X ^ 2) ^ 2 = (N : ℝ) ^ 2 * (3 * (A : ℝ) ^ 2 * (B : ℝ) ^ 2) := by
        have a1 : 4 * (detTri D.target) ^ 2 = 3 * (X ^ 2) ^ 2 := by rw [hdt]; ring
        have a2 : 4 * (detTri D.model) ^ 2 = 3 * (A : ℝ) ^ 2 * (B : ℝ) ^ 2 := by
          rw [hdm]; nlinarith [hrel]
        rw [← a1]
        have : 4 * (detTri D.target) ^ 2 = (N : ℝ) ^ 2 * (4 * (detTri D.model) ^ 2) := by rw [hsq]; ring
        rw [this, a2]
      nlinarith [this]
    have e2 : X ^ 2 = (N : ℝ) * A * B :=
      (sq_eq_sq₀ (by positivity) (by positivity)).mp e1
    have e3 : ((P * A + Q * B + R * C : ℕ) : ℝ) = X := by
      rw [hXd, hw, h0, h1, h2]; push_cast; ring
    have : (((P * A + Q * B + R * C) * (P * A + Q * B + R * C) : ℕ) : ℝ) = ((A * B * N : ℕ) : ℝ) := by
      push_cast at e3 ⊢
      rw [e3]; nlinarith [e2]
    exact_mod_cast this

/-- **Zhang Lemma 3, geometric form**: `A, B` squarefree and coprime, a `CongruentDissection` of an equilateral
triangle of side `X` by copies of the tile `(A, B, C)`: then `X = m A B` for a natural number `m`. -/
theorem zhang_lemma3_geom {N : ℕ} (A B C : ℕ) (hA : 0 < A) (hB : 0 < B)
    (hh : C * C = A * A + B * B + A * B) (hcop : Nat.Coprime A B) (hsA : Squarefree A) (hsB : Squarefree B)
    (D : CongruentDissection N) (hN : 0 < N)
    (h0 : sideOpp D.model 0 = A) (h1 : sideOpp D.model 1 = B) (h2 : sideOpp D.model 2 = C)
    (X : ℝ) (hX : ∀ j, sideOpp D.target j = X) :
    ∃ m : ℕ, X = (m * (A * B) : ℕ) := by
  obtain ⟨X', hX', hsq⟩ := lemma3_geom A B C hA hB hh hcop D hN h0 h1 h2 X hX
  obtain ⟨m, hm⟩ := Erdos634.ZhangRat6Arith.lemma3 A B X' N hsA hsB hcop (by rw [sq]; exact hsq)
  exact ⟨m, by rw [hX', hm]; push_cast; ring⟩

end Erdos634.ZhangRat7Int

#print axioms Erdos634.ZhangRat7Int.target_side_walk
#print axioms Erdos634.ZhangRat7Int.det_target_eq
#print axioms Erdos634.ZhangRat7Int.lemma3_geom
#print axioms Erdos634.ZhangRat7Int.zhang_lemma3_geom

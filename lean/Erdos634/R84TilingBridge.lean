import Erdos634.R84Tiling
import Erdos634.Z15Real
import Erdos634.CertGeom
import Erdos634.SssCongruent
import Erdos634.Ladder
import Erdos634.Tiling44Bridge

/-!
# `R84Tiling`, assembled into a genuine `CongruentDissection`

Erdős #634. The `cor:elevenm` half needing `R84Tiling` as a positive witness (`3 ∈ S`). Same
pattern that closed `thm:44`/`thm:63` (`Erdos634.Tiling44Bridge`/`Erdos634.CevianTiling63Bridge`):
`R84Tiling`'s `Z15`/`Pt`/`cross`/`dist2`/`znonneg` are literally `Z15Real`'s through `toZPt`, so
every general lemma applies unchanged. `R84Tiling` has a named `target` field, like `Tiling44`.

Not a paper-row flip until checked against `cor:elevenm`'s exact statement.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.R84TilingBridge

open Erdos634.Z15Real Erdos634.Geometry
open Erdos634.Tiling44Bridge (affNeg_apply lineFun_ne_zero_of_sq_ne)

def toZPt (p : R84Tiling.Pt) : ZPt := p

/-- **The real determinant of a `R84Tiling.Tri`'s three vertices**, transferred from its `ℤ[√15]`
cross product. -/
theorem det3_eq_toR_cross (t : R84Tiling.Tri) :
    Erdos634.CertCoord.det3
      (toR (zx (toZPt (R84Tiling.t1 t)))) (toR (zy (toZPt (R84Tiling.t1 t))))
      (toR (zx (toZPt (R84Tiling.t2 t)))) (toR (zy (toZPt (R84Tiling.t2 t))))
      (toR (zx (toZPt (R84Tiling.t3 t)))) (toR (zy (toZPt (R84Tiling.t3 t))))
    = toR (zcross (toZPt (R84Tiling.t1 t)) (toZPt (R84Tiling.t2 t)) (toZPt (R84Tiling.t3 t))) :=
  toR_zcross _ _ _

/-- **The target's determinant is `4224√15`**, positive. -/
theorem target_det_pos :
    (0:ℝ) < Erdos634.CertCoord.det3
      (toR (zx (toZPt (R84Tiling.t1 R84Tiling.target))))
      (toR (zy (toZPt (R84Tiling.t1 R84Tiling.target))))
      (toR (zx (toZPt (R84Tiling.t2 R84Tiling.target))))
      (toR (zy (toZPt (R84Tiling.t2 R84Tiling.target))))
      (toR (zx (toZPt (R84Tiling.t3 R84Tiling.target))))
      (toR (zy (toZPt (R84Tiling.t3 R84Tiling.target)))) := by
  rw [det3_eq_toR_cross]
  exact toR_pos (z := zcross (toZPt (R84Tiling.t1 R84Tiling.target))
    (toZPt (R84Tiling.t2 R84Tiling.target)) (toZPt (R84Tiling.t3 R84Tiling.target))) (by decide)

/-- **The target, as a real `Tri`.** -/
noncomputable def targetTri : Tri :=
  Erdos634.CertCoord.mkTri
    (toR (zx (toZPt (R84Tiling.t1 R84Tiling.target))))
    (toR (zy (toZPt (R84Tiling.t1 R84Tiling.target))))
    (toR (zx (toZPt (R84Tiling.t2 R84Tiling.target))))
    (toR (zy (toZPt (R84Tiling.t2 R84Tiling.target))))
    (toR (zx (toZPt (R84Tiling.t3 R84Tiling.target))))
    (toR (zy (toZPt (R84Tiling.t3 R84Tiling.target))))
    target_det_pos.ne'

/-- **The first piece's determinant is `48√15`**, positive — a smaller instance of the same
computation, confirming the pattern generalizes piece-by-piece. -/
theorem piece0_det_pos :
    (0:ℝ) < Erdos634.CertCoord.det3
      (toR (zx (toZPt (R84Tiling.t1 (R84Tiling.tiles.headI)))))
      (toR (zy (toZPt (R84Tiling.t1 (R84Tiling.tiles.headI)))))
      (toR (zx (toZPt (R84Tiling.t2 (R84Tiling.tiles.headI)))))
      (toR (zy (toZPt (R84Tiling.t2 (R84Tiling.tiles.headI)))))
      (toR (zx (toZPt (R84Tiling.t3 (R84Tiling.tiles.headI)))))
      (toR (zy (toZPt (R84Tiling.t3 (R84Tiling.tiles.headI))))) := by
  rw [det3_eq_toR_cross]
  exact toR_pos (z := zcross (toZPt (R84Tiling.t1 (R84Tiling.tiles.headI)))
    (toZPt (R84Tiling.t2 (R84Tiling.tiles.headI))) (toZPt (R84Tiling.t3 (R84Tiling.tiles.headI))))
    (by decide)

-- Every one of the 84 pieces is positively oriented.
set_option maxRecDepth 4000 in
theorem all_pieces_pos :
    ∀ t ∈ R84Tiling.tiles,
      zpos (zcross (toZPt (R84Tiling.t1 t)) (toZPt (R84Tiling.t2 t)) (toZPt (R84Tiling.t3 t)))
        = true := by
  decide

/-- **Every piece, as a real `Tri`**, uniformly — the general form `thm:44`'s data entry needs,
combining `all_pieces_pos` with `det3_eq_toR_cross` instead of writing 44 separate constructions. -/
noncomputable def pieceTri {t : R84Tiling.Tri} (ht : t ∈ R84Tiling.tiles) : Tri :=
  Erdos634.CertCoord.mkTri
    (toR (zx (toZPt (R84Tiling.t1 t)))) (toR (zy (toZPt (R84Tiling.t1 t))))
    (toR (zx (toZPt (R84Tiling.t2 t)))) (toR (zy (toZPt (R84Tiling.t2 t))))
    (toR (zx (toZPt (R84Tiling.t3 t)))) (toR (zy (toZPt (R84Tiling.t3 t))))
    (by
      rw [det3_eq_toR_cross]
      exact (toR_pos (all_pieces_pos t ht)).ne')

/-- **The `lineFun` of a certificate edge is nonconstant**, for two *concrete* endpoints `P ≠ Q`
whose real coordinates differ — resolved via `Z15Real.toR_ne_zero_of_sq_ne` rather than injectivity
of `toR` (which this project deliberately never proves). `hx`/`hy` are the decidable `ℤ[√15]`
side conditions (`zx Q - zx P` resp. `zy Q - zy P` squared-nonequal to `15 * (other coord)²`); one
of the two always holds for a genuine edge, matching whichever coordinate actually differs. -/
theorem lineFun_ne_zero_of_sq_ne {P Q : ZPt}
    (h : (zsub (zx P) (zx Q)).1 ^ 2 ≠ 15 * (zsub (zx P) (zx Q)).2 ^ 2
       ∨ (zsub (zy P) (zy Q)).1 ^ 2 ≠ 15 * (zsub (zy P) (zy Q)).2 ^ 2) :
    (Erdos634.CertGeom.lineFun (toR (zx P)) (toR (zy P)) (toR (zx Q)) (toR (zy Q))).linear ≠ 0 := by
  apply Erdos634.CertGeom.lineFun_linear_ne_zero
  rcases h with h | h
  · exact Or.inl (sub_ne_zero.mp (by rw [← toR_sub]; exact toR_ne_zero_of_sq_ne h))
  · exact Or.inr (sub_ne_zero.mp (by rw [← toR_sub]; exact toR_ne_zero_of_sq_ne h))

/-- Pointwise negation of an affine map into `ℝ`. -/
theorem affNeg_apply (g : Plane →ᵃ[ℝ] ℝ) (p : Plane) : (-g) p = -(g p) := by
  have := congrFun (AffineMap.coe_neg g) p
  simpa using this

/-- `R84Tiling.cross` is literally `Z15Real.zcross` read through `toZPt` — the two files define the
same operations on the same underlying type, so this is `rfl`. -/
theorem cross_eq_zcross (o a b : R84Tiling.Pt) :
    R84Tiling.cross o a b = zcross (toZPt o) (toZPt a) (toZPt b) := rfl

/-- `R84Tiling.dist2` is literally `Z15Real.zdist2` read through `toZPt` — again `rfl`. -/
theorem dist2_eq_zdist2 (p q : R84Tiling.Pt) :
    R84Tiling.dist2 p q = zdist2 (toZPt p) (toZPt q) := rfl

/-- **A piece's vertex, named by index.** -/
def vertexOf (t : R84Tiling.Tri) (i : Fin 3) : R84Tiling.Pt :=
  ![R84Tiling.t1 t, R84Tiling.t2 t, R84Tiling.t3 t] i

/-- **`pieceTri`'s vertices are exactly `vertexOf`, read as real points.** -/
theorem pieceTri_pts (t : R84Tiling.Tri) (ht : t ∈ R84Tiling.tiles) (i : Fin 3) :
    (pieceTri ht).pts i
      = Erdos634.CertCoord.mkPt (toR (zx (toZPt (vertexOf t i)))) (toR (zy (toZPt (vertexOf t i)))) := by
  fin_cases i <;> rfl

/-- **Squared distances between a piece's vertices, transferred to `ℝ` from the certificate's own
`dist2`.** -/
theorem pieceTri_dist_sq (t : R84Tiling.Tri) (ht : t ∈ R84Tiling.tiles) (i j : Fin 3) :
    dist ((pieceTri ht).pts i) ((pieceTri ht).pts j) ^ 2 = toR (R84Tiling.dist2 (vertexOf t i) (vertexOf t j)) := by
  rw [pieceTri_pts t ht i, pieceTri_pts t ht j, Erdos634.CertCoord.dist_sq_mkPt,
    dist2_eq_zdist2]
  exact toR_zdist2 _ _

/-- **A single `sepBy`-true witness gives a genuine separating affine functional** between two
pieces, read as real `Tri` objects — the assembly step `CertGeom.pairwise_disjoint_of_separating`
needs, for one pair. `hPQ` is `lineFun_ne_zero_of_sq_ne`'s decidable side condition on the edge
`(P, Q)`; the certificate's own `sepBy` supplies which sign pattern holds. -/
theorem sep_of_sepBy {P Q : R84Tiling.Pt} {A B : R84Tiling.Tri}
    (hPQ : (zsub (zx (toZPt P)) (zx (toZPt Q))).1 ^ 2
             ≠ 15 * (zsub (zx (toZPt P)) (zx (toZPt Q))).2 ^ 2
         ∨ (zsub (zy (toZPt P)) (zy (toZPt Q))).1 ^ 2
             ≠ 15 * (zsub (zy (toZPt P)) (zy (toZPt Q))).2 ^ 2)
    (hsep : R84Tiling.sepBy P Q A B = true) (hA : A ∈ R84Tiling.tiles) (hB : B ∈ R84Tiling.tiles) :
    ∃ (f : Plane →ᵃ[ℝ] ℝ) (_ : f.linear ≠ 0) (c : ℝ),
      (∀ x ∈ (pieceTri hA).carrier, f x ≤ c) ∧ (∀ x ∈ (pieceTri hB).carrier, c ≤ f x) := by
  set f : Plane →ᵃ[ℝ] ℝ :=
    Erdos634.CertGeom.lineFun (toR (zx (toZPt P))) (toR (zy (toZPt P)))
      (toR (zx (toZPt Q))) (toR (zy (toZPt Q))) with hfdef
  have hflin : f.linear ≠ 0 := lineFun_ne_zero_of_sq_ne hPQ
  have hfval : ∀ v : R84Tiling.Pt,
      f (Erdos634.CertCoord.mkPt (toR (zx (toZPt v))) (toR (zy (toZPt v))))
        = toR (R84Tiling.cross P Q v) := by
    intro v
    rw [hfdef, Erdos634.CertGeom.lineFun_apply, Erdos634.CertCoord.mkPt_zero,
      Erdos634.CertCoord.mkPt_one, cross_eq_zcross]
    exact toR_zcross _ _ _
  have hpts : ∀ (t : R84Tiling.Tri) (ht : t ∈ R84Tiling.tiles) (k : Fin 3),
      (pieceTri ht).pts k
        = Erdos634.CertCoord.mkPt (toR (zx (toZPt (![R84Tiling.t1 t, R84Tiling.t2 t, R84Tiling.t3 t] k))))
            (toR (zy (toZPt (![R84Tiling.t1 t, R84Tiling.t2 t, R84Tiling.t3 t] k)))) := by
    intro t ht k; fin_cases k <;> rfl
  simp only [R84Tiling.sepBy, List.all_eq_true, List.mem_cons, Bool.and_eq_true,
    Bool.or_eq_true, List.map, forall_eq_or_imp] at hsep
  rcases hsep with ⟨hsA, hsB⟩ | ⟨hsA, hsB⟩
  · -- A's vertices have cross ≥ 0, B's have cross ≤ 0 (znonpos)
    refine ⟨-f, neg_ne_zero.mpr hflin, 0, ?_, ?_⟩
    · exact Erdos634.CertGeom.le_of_forall_pts_le (-f) (t := pieceTri hA) (c := 0)
        (fun k => by
          rw [affNeg_apply, hpts A hA k, hfval, neg_le, neg_zero]
          fin_cases k <;> first | exact Erdos634.Z15Real.toR_nonneg hsA.1 | exact Erdos634.Z15Real.toR_nonneg hsA.2.1 | exact Erdos634.Z15Real.toR_nonneg hsA.2.2.1)
    · intro x hx
      have hb := Erdos634.CertGeom.le_of_forall_pts_le f (t := pieceTri hB) (c := 0)
        (fun k => by
          rw [hpts B hB k, hfval]
          fin_cases k <;> first | exact Erdos634.Z15Real.toR_nonpos hsB.1 | exact Erdos634.Z15Real.toR_nonpos hsB.2.1 | exact Erdos634.Z15Real.toR_nonpos hsB.2.2.1)
      have := hb x hx
      rw [affNeg_apply]
      linarith
  · -- A's vertices have cross ≤ 0 (znonpos), B's have cross ≥ 0
    refine ⟨f, hflin, 0, ?_, ?_⟩
    · exact Erdos634.CertGeom.le_of_forall_pts_le f (t := pieceTri hA) (c := 0)
        (fun k => by
          rw [hpts A hA k, hfval]
          fin_cases k <;> first | exact Erdos634.Z15Real.toR_nonpos hsA.1 | exact Erdos634.Z15Real.toR_nonpos hsA.2.1 | exact Erdos634.Z15Real.toR_nonpos hsA.2.2.1)
    · intro x hx
      have hb := Erdos634.CertGeom.le_of_forall_pts_le (-f) (t := pieceTri hB) (c := 0)
        (fun k => by
          rw [affNeg_apply, hpts B hB k, hfval, neg_le, neg_zero]
          fin_cases k <;> first | exact Erdos634.Z15Real.toR_nonneg hsB.1 | exact Erdos634.Z15Real.toR_nonneg hsB.2.1 | exact Erdos634.Z15Real.toR_nonneg hsB.2.2.1)
      have := hb x hx
      rw [affNeg_apply] at this
      linarith

/-! ## Every pair of distinct pieces is separated — the 946-pair assembly, decided at once

Rather than unpacking `Tiling44.wit`/`checkPairs`'s exact witness list (946 individual
extractions), it is far cheaper to `decide` the *existence* of a separating edge candidate per
pair directly: for each of the 44×44 ordered pairs, some one of the 6 candidate edges (3 from each
triangle) both separates them (`sepBy`) and satisfies `sep_of_sepBy`'s decidable side condition
(`sqCond`). This one `decide` (~12s) replaces per-pair data entry entirely. -/

/-- The 6 candidate separating edges for a pair: each triangle's own 3 edges. -/
def edgeCands (A B : R84Tiling.Tri) : List (R84Tiling.Pt × R84Tiling.Pt) :=
  [R84Tiling.edgeOf A 0, R84Tiling.edgeOf A 1, R84Tiling.edgeOf A 2,
   R84Tiling.edgeOf B 0, R84Tiling.edgeOf B 1, R84Tiling.edgeOf B 2]

/-- The decidable side condition `sep_of_sepBy` needs for an edge `(P, Q)`, as a `Bool` — a direct
`decide` of the exact `Prop` `sep_of_sepBy` wants, so `sqCond_iff` is immediate. -/
def sqCond (pq : R84Tiling.Pt × R84Tiling.Pt) : Bool :=
  decide ((zsub (zx (toZPt pq.1)) (zx (toZPt pq.2))).1 ^ 2
             ≠ 15 * (zsub (zx (toZPt pq.1)) (zx (toZPt pq.2))).2 ^ 2
         ∨ (zsub (zy (toZPt pq.1)) (zy (toZPt pq.2))).1 ^ 2
             ≠ 15 * (zsub (zy (toZPt pq.1)) (zy (toZPt pq.2))).2 ^ 2)

/-- Some candidate edge both separates `A` and `B` and satisfies the side condition. -/
def pairOK (A B : R84Tiling.Tri) : Bool :=
  (edgeCands A B).any (fun pq => R84Tiling.sepBy pq.1 pq.2 A B && sqCond pq)

-- Every one of the 84*84 ordered pairs of distinct pieces has a working separating edge.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem all_pairs_ok : ∀ A ∈ R84Tiling.tiles, ∀ B ∈ R84Tiling.tiles, A ≠ B → pairOK A B = true := by
  decide

/-- `sqCond`'s `Bool` and `sep_of_sepBy`'s `Prop` side condition agree. -/
theorem sqCond_iff (pq : R84Tiling.Pt × R84Tiling.Pt) :
    sqCond pq = true ↔
      (zsub (zx (toZPt pq.1)) (zx (toZPt pq.2))).1 ^ 2 ≠ 15 * (zsub (zx (toZPt pq.1)) (zx (toZPt pq.2))).2 ^ 2
        ∨ (zsub (zy (toZPt pq.1)) (zy (toZPt pq.2))).1 ^ 2
            ≠ 15 * (zsub (zy (toZPt pq.1)) (zy (toZPt pq.2))).2 ^ 2 := by
  rw [sqCond, decide_eq_true_iff]

/-- **Every two distinct pieces of `Tiling44` have disjoint interiors, as real `Tri` objects.**
This is (C3) fully assembled: existence of the separating edge (`all_pairs_ok`), transferred to a
genuine affine functional bounded on the whole carrier (`sep_of_sepBy`). -/
theorem pieces_interiors_disjoint {A B : R84Tiling.Tri} (hA : A ∈ R84Tiling.tiles)
    (hB : B ∈ R84Tiling.tiles) (hne : A ≠ B) :
    Disjoint (interior (pieceTri hA).carrier) (interior (pieceTri hB).carrier) := by
  have hok := all_pairs_ok A hA B hB hne
  simp only [pairOK, List.any_eq_true] at hok
  obtain ⟨pq, hmem, hsep⟩ := hok
  rw [Bool.and_eq_true] at hsep
  obtain ⟨hsepBy, hsq⟩ := hsep
  obtain ⟨f, hf, c, h1, h2⟩ := sep_of_sepBy ((sqCond_iff pq).mp hsq) hsepBy hA hB
  exact Erdos634.CertGeom.interiors_disjoint_of_separating f hf c h1 h2

/-! ## (C1): every piece is congruent to a fixed model — the first piece, decided at once -/

/-- **The model tile**: `Tiling44`'s first certificate piece. Any piece works as the model since
all are mutually congruent; picking one already in `tiles` avoids naming new coordinates. -/
theorem headI_mem_tiles : R84Tiling.tiles.headI ∈ R84Tiling.tiles := by decide

/-- **Some permutation matches a piece's squared side lengths to the model's, positionally.**
`decide` over the `Fintype (Equiv.Perm (Fin 3))` (6 elements) × 44 pieces × 9 pairs — cheap. -/
def congOK' (t : R84Tiling.Tri) : Bool :=
  decide (∃ σ : Equiv.Perm (Fin 3), ∀ i j : Fin 3,
    R84Tiling.dist2 (vertexOf t i) (vertexOf t j)
      = R84Tiling.dist2 (vertexOf R84Tiling.tiles.headI (σ i)) (vertexOf R84Tiling.tiles.headI (σ j)))

-- Every one of the 84 pieces has a matching permutation.
set_option maxRecDepth 4000 in
theorem all_pieces_cong : ∀ t ∈ R84Tiling.tiles, congOK' t = true := by decide

/-- **(C1) fully assembled**: every piece of `Tiling44`, as a real `Tri`, is congruent to the
model tile. -/
theorem pieceTri_congruent {t : R84Tiling.Tri} (ht : t ∈ R84Tiling.tiles) :
    (pieceTri ht).Congruent (pieceTri headI_mem_tiles) := by
  have hex := all_pieces_cong t ht
  simp only [congOK', decide_eq_true_eq] at hex
  obtain ⟨σ, hσ⟩ := hex
  refine Erdos634.SssCongruent.congruent_of_sq_dist_perm σ (fun i j => ?_)
  rw [pieceTri_dist_sq t ht, pieceTri_dist_sq R84Tiling.tiles.headI headI_mem_tiles]
  exact congrArg Erdos634.Z15Real.toR (hσ i j)

/-! ## (C2) containment: every piece lies in the target — the part `all_pieces_pos` skipped

`all_pieces_pos` only captured orientation (`insideOK`'s first conjunct); this is the actual
vertex-in-target containment, `insideOK`'s second conjunct. -/

/-- **Cyclic invariance of `cross`**: `cross o a b = cross a b o`. Twice the signed area of a
triangle does not depend on which vertex is named first, only the cyclic order. Needed to match
`insideOK`'s three checks (each anchored at a different target edge) against
`CertCoord.mem_carrier_of_dets`'s fixed vertex-0/1/2 convention. -/
theorem cross_cyclic (o a b : R84Tiling.Pt) : R84Tiling.cross o a b = R84Tiling.cross a b o := by
  simp only [R84Tiling.cross, R84Tiling.zsub, R84Tiling.zmul, R84Tiling.px, R84Tiling.py, Prod.ext_iff]
  constructor <;> ring

-- Every one of the 84 pieces' vertices lies in the closed target.
set_option maxRecDepth 4000 in
theorem all_pieces_inside : ∀ t ∈ R84Tiling.tiles, R84Tiling.insideOK t = true := by decide

/-- Abbreviations for the target's three vertices. -/
theorem insideOK_vertex {t : R84Tiling.Tri} (ht : t ∈ R84Tiling.tiles) (i : Fin 3) :
    R84Tiling.znonneg (R84Tiling.cross (R84Tiling.t1 R84Tiling.target) (R84Tiling.t2 R84Tiling.target)
        (vertexOf t i)) = true
    ∧ R84Tiling.znonneg (R84Tiling.cross (R84Tiling.t2 R84Tiling.target) (R84Tiling.t3 R84Tiling.target)
        (vertexOf t i)) = true
    ∧ R84Tiling.znonneg (R84Tiling.cross (R84Tiling.t3 R84Tiling.target) (R84Tiling.t1 R84Tiling.target)
        (vertexOf t i)) = true := by
  have hins := all_pieces_inside t ht
  simp only [R84Tiling.insideOK, Bool.and_eq_true, List.all_eq_true] at hins
  have hv : vertexOf t i ∈ ([R84Tiling.t1 t, R84Tiling.t2 t, R84Tiling.t3 t] : List R84Tiling.Pt) := by
    fin_cases i <;> simp [vertexOf]
  have h3 := hins.2 (vertexOf t i) hv
  simp only [Bool.and_eq_true] at h3
  exact ⟨h3.1.1, h3.1.2, h3.2⟩

/-- **The target, real vertex-by-vertex, matches `mem_carrier_of_dets`'s convention.** -/
theorem vertexOf_mem_targetTri {t : R84Tiling.Tri} (ht : t ∈ R84Tiling.tiles) (i : Fin 3) :
    Erdos634.CertCoord.mkPt (toR (zx (toZPt (vertexOf t i)))) (toR (zy (toZPt (vertexOf t i))))
      ∈ targetTri.carrier := by
  obtain ⟨h1, h2, h3⟩ := insideOK_vertex ht i
  refine Erdos634.CertCoord.mem_carrier_of_dets (x₀ := toR (zx (toZPt (R84Tiling.t1 R84Tiling.target))))
    (y₀ := toR (zy (toZPt (R84Tiling.t1 R84Tiling.target))))
    (x₁ := toR (zx (toZPt (R84Tiling.t2 R84Tiling.target))))
    (y₁ := toR (zy (toZPt (R84Tiling.t2 R84Tiling.target))))
    (x₂ := toR (zx (toZPt (R84Tiling.t3 R84Tiling.target))))
    (y₂ := toR (zy (toZPt (R84Tiling.t3 R84Tiling.target))))
    target_det_pos ?_ ?_ ?_
  · -- h0 : 0 ≤ det3 a b x1 y1 x2 y2 = cross(v, T2, T3) = cross(T2, T3, v) [cyclic]
    rw [show Erdos634.CertCoord.det3 (toR (zx (toZPt (vertexOf t i)))) (toR (zy (toZPt (vertexOf t i))))
        (toR (zx (toZPt (R84Tiling.t2 R84Tiling.target)))) (toR (zy (toZPt (R84Tiling.t2 R84Tiling.target))))
        (toR (zx (toZPt (R84Tiling.t3 R84Tiling.target)))) (toR (zy (toZPt (R84Tiling.t3 R84Tiling.target))))
      = toR (zcross (toZPt (vertexOf t i)) (toZPt (R84Tiling.t2 R84Tiling.target))
          (toZPt (R84Tiling.t3 R84Tiling.target))) from toR_zcross _ _ _,
      ← cross_eq_zcross, cross_cyclic (vertexOf t i) (R84Tiling.t2 R84Tiling.target) (R84Tiling.t3 R84Tiling.target)]
    exact Erdos634.Z15Real.toR_nonneg h2
  · -- h1 : 0 ≤ det3 x0 y0 a b x2 y2 = cross(T1, v, T3) = cross(T3, T1, v) [two cyclic rotations]
    rw [show Erdos634.CertCoord.det3 (toR (zx (toZPt (R84Tiling.t1 R84Tiling.target))))
        (toR (zy (toZPt (R84Tiling.t1 R84Tiling.target)))) (toR (zx (toZPt (vertexOf t i))))
        (toR (zy (toZPt (vertexOf t i)))) (toR (zx (toZPt (R84Tiling.t3 R84Tiling.target))))
        (toR (zy (toZPt (R84Tiling.t3 R84Tiling.target))))
      = toR (zcross (toZPt (R84Tiling.t1 R84Tiling.target)) (toZPt (vertexOf t i))
          (toZPt (R84Tiling.t3 R84Tiling.target))) from toR_zcross _ _ _,
      ← cross_eq_zcross,
      cross_cyclic (R84Tiling.t1 R84Tiling.target) (vertexOf t i) (R84Tiling.t3 R84Tiling.target),
      cross_cyclic (vertexOf t i) (R84Tiling.t3 R84Tiling.target) (R84Tiling.t1 R84Tiling.target)]
    exact Erdos634.Z15Real.toR_nonneg h3
  · -- h2 : 0 ≤ det3 x0 y0 x1 y1 a b = cross(T1, T2, v), direct match
    rw [show Erdos634.CertCoord.det3 (toR (zx (toZPt (R84Tiling.t1 R84Tiling.target))))
        (toR (zy (toZPt (R84Tiling.t1 R84Tiling.target)))) (toR (zx (toZPt (R84Tiling.t2 R84Tiling.target))))
        (toR (zy (toZPt (R84Tiling.t2 R84Tiling.target)))) (toR (zx (toZPt (vertexOf t i))))
        (toR (zy (toZPt (vertexOf t i))))
      = toR (zcross (toZPt (R84Tiling.t1 R84Tiling.target)) (toZPt (R84Tiling.t2 R84Tiling.target))
          (toZPt (vertexOf t i))) from toR_zcross _ _ _,
      ← cross_eq_zcross]
    exact Erdos634.Z15Real.toR_nonneg h1

/-- **(C2) fully assembled**: every piece of `Tiling44`, as a real `Tri`, lies in the target. -/
theorem pieceTri_subset_target {t : R84Tiling.Tri} (ht : t ∈ R84Tiling.tiles) :
    (pieceTri ht).carrier ⊆ targetTri.carrier :=
  Erdos634.CertGeom.carrier_subset_of_pts_mem (fun k => by
    rw [pieceTri_pts t ht k]; exact vertexOf_mem_targetTri ht k)

/-! ## (C4): the area sum, and the assembled `CongruentDissection`

`Tiling44`'s own `checkAll` already checks `zsum (tiles.map area2) == area2 target`; this section
transfers that Bool equality to the real determinant sum `AreaDet.area_identity_of_det` needs. -/

/-- Every piece of `Tiling44`, indexed by `Fin R84Tiling.tiles.length` (rather than a fixed literal
`44`, so no length-cast bookkeeping is needed anywhere in this section). -/
noncomputable def pieceAt (i : Fin R84Tiling.tiles.length) : Tri :=
  pieceTri (t := R84Tiling.tiles[i.val]) (List.getElem_mem i.isLt)

theorem detTri_pieceAt (i : Fin R84Tiling.tiles.length) :
    Erdos634.AreaDet.detTri (pieceAt i) = toR (R84Tiling.area2 (R84Tiling.tiles[i.val])) := by
  unfold pieceAt pieceTri
  rw [Erdos634.CertCoord.detTri_mkTri, det3_eq_toR_cross]
  rfl

theorem foldl_zadd_eq (l : List R84Tiling.Z15) (acc : R84Tiling.Z15) :
    l.foldl R84Tiling.zadd acc = acc + l.sum := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.sum_cons]
    rw [ih]; apply Prod.ext <;> simp [R84Tiling.zadd] <;> ring

theorem zsum_eq_sum (l : List R84Tiling.Z15) : R84Tiling.zsum l = l.sum := by
  simp only [R84Tiling.zsum]; rw [foldl_zadd_eq]; simp

theorem tiling84_zadd_eq_zreal (u v : R84Tiling.Z15) : R84Tiling.zadd u v = zadd u v := rfl

theorem toR_list_sum (l : List R84Tiling.Z15) : toR l.sum = (l.map toR).sum := by
  induction l with
  | nil => simp [toR]
  | cons a t ih =>
    simp only [List.sum_cons, List.map_cons]
    show toR (a + t.sum) = toR a + (List.map toR t).sum
    rw [show (a + t.sum : R84Tiling.Z15) = R84Tiling.zadd a t.sum from rfl,
      tiling84_zadd_eq_zreal, toR_add, ih]

theorem area_sum_transfer :
    ∑ i : Fin R84Tiling.tiles.length, toR (R84Tiling.area2 (R84Tiling.tiles[i.val]))
      = toR (R84Tiling.zsum (R84Tiling.tiles.map R84Tiling.area2)) := by
  rw [zsum_eq_sum, toR_list_sum, List.map_map,
    ← List.ofFn_getElem_eq_map R84Tiling.tiles (toR ∘ R84Tiling.area2)]
  rfl

/-- **The (C4) area sum, transferred to `ℝ`** — matching `Tiling44`'s own `checkAll` equality. -/
theorem area_sum_eq_target :
    ∑ i : Fin R84Tiling.tiles.length, toR (R84Tiling.area2 (R84Tiling.tiles[i.val]))
      = toR (R84Tiling.area2 R84Tiling.target) := by
  rw [area_sum_transfer]
  apply congrArg toR
  have h := R84Tiling.tiling84_certificate
  simp only [R84Tiling.checkAll, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

/-- **(C4) fully assembled**, with absolute values — every piece is positively oriented
(`all_pieces_pos`) and so is the target (`target_det_pos`), so `|det| = det` throughout. -/
theorem abs_detTri_sum_eq_target :
    ∑ i : Fin R84Tiling.tiles.length, |Erdos634.AreaDet.detTri (pieceAt i)|
      = |Erdos634.AreaDet.detTri targetTri| := by
  have htarget : Erdos634.AreaDet.detTri targetTri = toR (R84Tiling.area2 R84Tiling.target) := by
    unfold targetTri
    rw [Erdos634.CertCoord.detTri_mkTri, det3_eq_toR_cross]
    rfl
  have htpos : (0:ℝ) < Erdos634.AreaDet.detTri targetTri := by
    unfold targetTri; rw [Erdos634.CertCoord.detTri_mkTri]; exact target_det_pos
  rw [htarget, abs_of_pos (htarget ▸ htpos)]
  rw [← area_sum_eq_target]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [detTri_pieceAt]
  exact abs_of_pos (toR_pos (all_pieces_pos _ (List.getElem_mem i.isLt)))

-- R84Tiling's certificate, assembled into a genuine CongruentDissection.
set_option maxRecDepth 4000 in
theorem tiles_getElem_inj : ∀ i j : Fin R84Tiling.tiles.length, i ≠ j →
    R84Tiling.tiles[i.val] ≠ R84Tiling.tiles[j.val] := by decide

noncomputable def dissection : CongruentDissection R84Tiling.tiles.length where
  toDissection := Erdos634.AreaDet.ofDetCertificate targetTri pieceAt
    (fun i => pieceTri_subset_target (List.getElem_mem i.isLt))
    (fun i j hij => pieces_interiors_disjoint (List.getElem_mem i.isLt) (List.getElem_mem j.isLt)
      (tiles_getElem_inj i j hij))
    abs_detTri_sum_eq_target
  model := pieceTri headI_mem_tiles
  tiles_congruent := fun i => pieceTri_congruent (List.getElem_mem i.isLt)

/-! ## Checking `dissection`'s shape against `thm:44`'s exact statement (Rule 5)

`thm:44` (erdos-634.tex): "the isosceles triangle with sides `(16,16,22)` is tiled by 44 congruent
copies of the `(2,3,4)` triangle. Consequently `44m²` is a tile count for every `m ≥ 1`." Two
clauses — only the first is checked here. -/

/-- **`dissection`'s target has sides in ratio `16:16:22`** (squared `256:256:484`, scaled by the
certificate's own `8²`: `16384:16384:30976`). -/
theorem targetTri_pts_eq (k : Fin 3) :
    targetTri.pts k = Erdos634.CertCoord.mkPt
      (toR (zx (toZPt (![R84Tiling.t1 R84Tiling.target, R84Tiling.t2 R84Tiling.target,
        R84Tiling.t3 R84Tiling.target] k))))
      (toR (zy (toZPt (![R84Tiling.t1 R84Tiling.target, R84Tiling.t2 R84Tiling.target,
        R84Tiling.t3 R84Tiling.target] k)))) := by
  fin_cases k <;> rfl

theorem targetTri_dist_sq (i j : Fin 3) :
    dist (targetTri.pts i) (targetTri.pts j) ^ 2
      = toR (R84Tiling.dist2
          (![R84Tiling.t1 R84Tiling.target, R84Tiling.t2 R84Tiling.target, R84Tiling.t3 R84Tiling.target] i)
          (![R84Tiling.t1 R84Tiling.target, R84Tiling.t2 R84Tiling.target, R84Tiling.t3 R84Tiling.target] j)) := by
  rw [targetTri_pts_eq i, targetTri_pts_eq j, Erdos634.CertCoord.dist_sq_mkPt, dist2_eq_zdist2]
  exact toR_zdist2 _ _

theorem targetTri_sides :
    dist (targetTri.pts 0) (targetTri.pts 1) ^ 2 = 112896
    ∧ dist (targetTri.pts 1) (targetTri.pts 2) ^ 2 = 36864
    ∧ dist (targetTri.pts 2) (targetTri.pts 0) ^ 2 = 36864 := by
  have e01 : R84Tiling.dist2 (R84Tiling.t1 R84Tiling.target) (R84Tiling.t2 R84Tiling.target)
      = ((112896:ℤ),(0:ℤ)) := by decide
  have e12 : R84Tiling.dist2 (R84Tiling.t2 R84Tiling.target) (R84Tiling.t3 R84Tiling.target)
      = ((36864:ℤ),(0:ℤ)) := by decide
  have e20 : R84Tiling.dist2 (R84Tiling.t3 R84Tiling.target) (R84Tiling.t1 R84Tiling.target)
      = ((36864:ℤ),(0:ℤ)) := by decide
  refine ⟨?_, ?_, ?_⟩
  · rw [targetTri_dist_sq 0 1]; simp; rw [e01]; simp [toR]
  · rw [targetTri_dist_sq 1 2]; simp; rw [e12]; simp [toR]
  · rw [targetTri_dist_sq 2 0]; simp; rw [e20]; simp [toR]

/-- **The model tile's sides are in ratio `2:3:4`** (squared `4:9:16`, scaled by `8²`:
`256:576:1024`). -/
theorem model_sides :
    (dist ((pieceTri headI_mem_tiles).pts 0) ((pieceTri headI_mem_tiles).pts 1) ^ 2 = 256
      ∨ dist ((pieceTri headI_mem_tiles).pts 0) ((pieceTri headI_mem_tiles).pts 1) ^ 2 = 576
      ∨ dist ((pieceTri headI_mem_tiles).pts 0) ((pieceTri headI_mem_tiles).pts 1) ^ 2 = 1024)
    ∧ (dist ((pieceTri headI_mem_tiles).pts 1) ((pieceTri headI_mem_tiles).pts 2) ^ 2 = 256
      ∨ dist ((pieceTri headI_mem_tiles).pts 1) ((pieceTri headI_mem_tiles).pts 2) ^ 2 = 576
      ∨ dist ((pieceTri headI_mem_tiles).pts 1) ((pieceTri headI_mem_tiles).pts 2) ^ 2 = 1024)
    ∧ (dist ((pieceTri headI_mem_tiles).pts 2) ((pieceTri headI_mem_tiles).pts 0) ^ 2 = 256
      ∨ dist ((pieceTri headI_mem_tiles).pts 2) ((pieceTri headI_mem_tiles).pts 0) ^ 2 = 576
      ∨ dist ((pieceTri headI_mem_tiles).pts 2) ((pieceTri headI_mem_tiles).pts 0) ^ 2 = 1024) := by
  have e01 : R84Tiling.dist2 (vertexOf R84Tiling.tiles.headI 0) (vertexOf R84Tiling.tiles.headI 1)
      = ((576:ℤ),(0:ℤ)) := by decide
  have e12 : R84Tiling.dist2 (vertexOf R84Tiling.tiles.headI 1) (vertexOf R84Tiling.tiles.headI 2)
      = ((256:ℤ),(0:ℤ)) := by decide
  have e20 : R84Tiling.dist2 (vertexOf R84Tiling.tiles.headI 2) (vertexOf R84Tiling.tiles.headI 0)
      = ((1024:ℤ),(0:ℤ)) := by decide
  refine ⟨Or.inr (Or.inl ?_), Or.inl ?_, Or.inr (Or.inr ?_)⟩
  · rw [pieceTri_dist_sq _ headI_mem_tiles 0 1, e01]; norm_num [toR]
  · rw [pieceTri_dist_sq _ headI_mem_tiles 1 2, e12]; norm_num [toR]
  · rw [pieceTri_dist_sq _ headI_mem_tiles 2 0, e20]; norm_num [toR]

/-! ## Clause 2 of `thm:44`: "consequently `44m²` is a tile count for every `m ≥ 1`"

Composing `dissection` with `Ladder.ladder` for arbitrary `m` scales the target by `m` in each
direction, multiplying the piece count by `m²`. -/

theorem targetTri_eq_mkTri :
    targetTri = Erdos634.CertCoord.mkTri
      (toR (zx (toZPt (R84Tiling.t1 R84Tiling.target)))) (toR (zy (toZPt (R84Tiling.t1 R84Tiling.target))))
      (toR (zx (toZPt (R84Tiling.t2 R84Tiling.target)))) (toR (zy (toZPt (R84Tiling.t2 R84Tiling.target))))
      (toR (zx (toZPt (R84Tiling.t3 R84Tiling.target)))) (toR (zy (toZPt (R84Tiling.t3 R84Tiling.target))))
      target_det_pos.ne' := rfl

/-- **Clause 2 of `thm:44`**: for every `m ≥ 1`, there is a `CongruentDissection` with `44 * m * m`
pieces, all congruent to the `(2,3,4)`-shaped model tile, of the `m`-times-enlarged target. This is
`Ladder.ladder` applied to `dissection`. -/
theorem exists_dissection_mul_sq (m : ℕ) (hm : 0 < m) :
    ∃ E : CongruentDissection (m * m * R84Tiling.tiles.length), E.model = pieceTri headI_mem_tiles :=
  ⟨(Erdos634.Ladder.ladder
      (A := Erdos634.CertCoord.mkPt (toR (zx (toZPt (R84Tiling.t1 R84Tiling.target))))
        (toR (zy (toZPt (R84Tiling.t1 R84Tiling.target)))))
      (B := Erdos634.CertCoord.mkPt (toR (zx (toZPt (R84Tiling.t2 R84Tiling.target))))
        (toR (zy (toZPt (R84Tiling.t2 R84Tiling.target)))))
      (C := Erdos634.CertCoord.mkPt (toR (zx (toZPt (R84Tiling.t3 R84Tiling.target))))
        (toR (zy (toZPt (R84Tiling.t3 R84Tiling.target)))))
      targetTri.indep dissection targetTri_eq_mkTri m hm).choose,
    (Erdos634.Ladder.ladder
      (A := Erdos634.CertCoord.mkPt (toR (zx (toZPt (R84Tiling.t1 R84Tiling.target))))
        (toR (zy (toZPt (R84Tiling.t1 R84Tiling.target)))))
      (B := Erdos634.CertCoord.mkPt (toR (zx (toZPt (R84Tiling.t2 R84Tiling.target))))
        (toR (zy (toZPt (R84Tiling.t2 R84Tiling.target)))))
      (C := Erdos634.CertCoord.mkPt (toR (zx (toZPt (R84Tiling.t3 R84Tiling.target))))
        (toR (zy (toZPt (R84Tiling.t3 R84Tiling.target)))))
      targetTri.indep dissection targetTri_eq_mkTri m hm).choose_spec.2⟩

theorem tiles_length_eq_84 : R84Tiling.tiles.length = 84 := by decide

/-- **Clause 2, restated in the paper's own numeral form**: `84 * m ^ 2` is a tile count for every
`m ≥ 1`. -/
theorem exists_dissection_84_mul_sq (m : ℕ) (hm : 0 < m) :
    ∃ E : CongruentDissection (84 * m ^ 2), E.model = pieceTri headI_mem_tiles := by
  obtain ⟨E, hE⟩ := exists_dissection_mul_sq m hm
  have hnum : m * m * R84Tiling.tiles.length = 84 * m ^ 2 := by
    rw [tiles_length_eq_84]; ring
  exact hnum ▸ ⟨E, hE⟩


/-- **`Nonempty (CongruentDissection 84)`**: the triangle (24,24,42) is dissected into 84 triangles
congruent to the (2,3,4) tile. AUDITED 2026-10-07 (statement-match: target sides 192:192:336 =
24:24:42, model sides 16:24:32 = 2:3:4, MATCH; no sorry, no native_decide). -/
theorem r84_nonempty_congruentDissection : Nonempty (CongruentDissection 84) := by
  obtain ⟨E, _⟩ := exists_dissection_84_mul_sq 1 one_pos
  exact ⟨by simpa using E⟩

#print axioms r84_nonempty_congruentDissection

end Erdos634.R84TilingBridge

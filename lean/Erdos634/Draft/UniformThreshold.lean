/-
Draft/UniformThreshold.lean -- the threshold statement for the base-β row: definitions and the cases that are
theorems (light part: no search certificate is imported here).

For coprime `1 ≤ e < f` the base-β target of the tile `(ef, f² − e², f²)` at scale `M` is the isosceles triangle
with legs `M f³` and base `M e (3f² − e²)` (base angles `β`, apex `3α`; `M² (3f² − e²)` tiles).

    def BetaTilable (e f M : ℕ) : Prop      -- that triangle has a dissection into copies of the tile, any number
    def ThresholdAt (e f M : ℕ) : Prop := BetaTilable e f M ↔ f ≤ M
    def UniformThreshold : Prop := ∀ e f M, 1 ≤ e → e < f → Nat.Coprime e f → 1 ≤ M → ThresholdAt e f M

`UniformThreshold` is NOT proved and is not asserted anywhere: it is the statement under test.  Its two halves have
different status.
* Sufficiency (`f ≤ M → BetaTilable e f M`) is ANNOUNCED by D. Paliy (notes of 3 and 9 October 2026, unrefereed;
  seed at scale `f` credited to M. Beeson, collars and residue seeds his).  FORMALIZED HERE ONLY AT THE MULTIPLES
  OF `f`: `betaTilable_self` (scale `f`, every member: the seed, `WSeedG.beta_seed`) and `betaTilable_mul` (scale
  `M` gives every multiple of `M`).  Also `betaTilable_1_2` (every `M ≥ 2`, member `(1,2)`) and the two
  kernel-checked tilings `betaTilable_1_3_three`, `betaTilable_2_3_three` (`234` and `207` tiles), which are now
  instances of `betaTilable_self`.  The scales `M > f` that are not multiples of `f` need the collars and are NOT
  formalized.
* Necessity (`BetaTilable e f M → f ≤ M`) is OPEN for `2 ≤ M < f`.  In this file: `not_betaTilable_one` (scale one,
  every member; this is `BaseBetaFullUnc.basebeta_full_unc`).  The scale-two cases for `f ≤ 4` need search
  certificates and are in `Draft.UniformThresholdCert`.

Proved here: `threshold_one` (`M = 1`, every member), `threshold_mul_self` (`M = k f`, every member),
`threshold_1_2` (the member `(1,2)`, every `M`), and `tileCount_beta_seed` (`f² (3f² − e²)` is a tile count).
Composite-N statements; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.BaseBetaFullUnc
import Erdos634.Draft.HasSidesPerm
import Erdos634.Draft.RWEast
import Erdos634.Draft.N234
import Erdos634.Draft.N207
import Erdos634.Draft.WSeedGAssemble

open scoped Classical

namespace Erdos634.Draft.UniformThreshold

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.BaseBetaTargetCoord Erdos634.Draft.FDBBaseBetaE1

/-- The base-β target of the member `(e, f)` at scale `M` can be cut into congruent copies of the tile
`(ef, f² − e², f²)`, in some number. -/
def BetaTilable (e f M : ℕ) : Prop :=
  ∃ (N : ℕ) (D : CongruentDissection N),
    HasSides D.target ((M : ℝ) * (f : ℝ) ^ 3) ((M : ℝ) * (f : ℝ) ^ 3)
      ((M : ℝ) * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) ∧
    HasSides D.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)

/-- The threshold statement at one member and one scale. -/
def ThresholdAt (e f M : ℕ) : Prop := BetaTilable e f M ↔ f ≤ M

/-- **The statement under test** (NOT proved): the base-β target of every member has a tiling exactly from the
scale `f` on. -/
def UniformThreshold : Prop :=
  ∀ e f M : ℕ, 1 ≤ e → e < f → Nat.Coprime e f → 1 ≤ M → ThresholdAt e f M

theorem hasSides_congr {T : Erdos634.Geometry.Tri} {a b c a' b' c' : ℝ} (h : HasSides T a b c) (ha : a = a') (hb : b = b')
    (hc : c = c') : HasSides T a' b' c' := by
  subst ha; subst hb; subst hc; exact h

/-! ## Scale one: no member has a tiling -/

/-- **Scale one.**  `BaseBetaFullUnc.basebeta_full_unc` in the side-length form. -/
theorem not_betaTilable_one {e f : ℕ} (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f) :
    ¬ BetaTilable e f 1 := by
  rintro ⟨N, D, hT, hM⟩
  have he0 : (0 : ℝ) < e := by exact_mod_cast (show 0 < e by omega)
  have hefR : (e : ℝ) < f := by exact_mod_cast hef
  have hT' : HasSides D.target ((f : ℝ) ^ 3) ((f : ℝ) ^ 3) ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) :=
    hasSides_congr hT (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)
  have htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f he0 hefR) := by
    refine congruent_of_hasSides hT' ?_ ?_ ?_
    · rw [baseBetaTarget_dist_leg₁]
    · rw [dist_comm, baseBetaTarget_dist_leg₀]
    · rw [baseBetaTarget_dist_base]
  obtain ⟨τ, h0, h1, h2⟩ := hM
  have h0' : sideOpp (D.relabelModel τ).model 0 = (e : ℝ) * f := h0
  have h1' : sideOpp (D.relabelModel τ).model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := h1
  have h2' : sideOpp (D.relabelModel τ).model 2 = (f : ℝ) ^ 2 := h2
  exact Erdos634.Draft.BaseBetaFullUnc.basebeta_full_unc (D.relabelModel τ) hco he hef htgt h0' h1' h2'

/-- **The threshold statement holds at scale one, for every member.** -/
theorem threshold_one {e f : ℕ} (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f) : ThresholdAt e f 1 :=
  ⟨fun h => absurd h (not_betaTilable_one hco he hef), fun h => by omega⟩

/-! ## Positive cases -/

/-- the member `(1, 2)`: every scale `M ≥ 2` (`thm:realize12`, the family `11 M²`) -/
theorem betaTilable_1_2 {M : ℕ} (hM : 2 ≤ M) : BetaTilable 1 2 M := by
  obtain ⟨D, hT, hm⟩ := realize12_existence M hM
  exact ⟨_, D, hasSides_congr hT (by push_cast; ring) (by push_cast; ring) (by push_cast; ring),
    hasSides_congr hm (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)⟩

/-- the member `(1, 3)` at scale `3`: the kernel-checked `234`-tiling -/
theorem betaTilable_1_3_three : BetaTilable 1 3 3 := by
  obtain ⟨D, hT, hm⟩ := Erdos634.Draft.N234.basebeta_1_3_scale_three
  exact ⟨_, D, hasSides_congr hT (by push_cast; ring) (by push_cast; ring) (by push_cast; ring),
    hasSides_congr hm (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)⟩

/-- the member `(2, 3)` at scale `3`: the kernel-checked `207`-tiling -/
theorem betaTilable_2_3_three : BetaTilable 2 3 3 := by
  obtain ⟨D, hT, hm⟩ := Erdos634.Draft.N207.basebeta_2_3_scale_three
  exact ⟨_, D, hasSides_congr hT (by push_cast; ring) (by push_cast; ring) (by push_cast; ring),
    hasSides_congr hm (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)⟩

/-- **Multiples.**  A tiling at scale `M` gives one at every multiple `k M` (each tile is cut into `k²` tiles after
scaling by `k`: `Ladder.ladder`). -/
theorem betaTilable_mul {e f M : ℕ} (h : BetaTilable e f M) {k : ℕ} (hk : 0 < k) : BetaTilable e f (k * M) := by
  obtain ⟨N, D, ⟨τ, t0, t1, t2⟩, hM⟩ := h
  obtain ⟨hind, heta⟩ := Erdos634.Draft.RWEast.tri_eta D.target
  obtain ⟨E, hEt, hEm⟩ := Erdos634.Ladder.ladder (D.target.pts 0) (D.target.pts 1) (D.target.pts 2) hind D heta k hk
  have hd := Erdos634.Draft.RWEast.dist_bigTri (D.target.pts 0) (D.target.pts 1) (D.target.pts 2) hind k hk
  have hvec : ∀ i : Fin 3, (![D.target.pts 0, D.target.pts 1, D.target.pts 2] : Fin 3 → Plane) i = D.target.pts i := by
    intro i; fin_cases i <;> rfl
  have hd' : ∀ i j : Fin 3, dist (E.target.pts i) (E.target.pts j) = (k : ℝ) * dist (D.target.pts i) (D.target.pts j) := by
    intro i j
    rw [hEt, hd i j, hvec i, hvec j]
  refine ⟨_, E, ⟨τ, ?_, ?_, ?_⟩, by rw [hEm]; exact hM⟩
  · rw [hd', t0]; push_cast; ring
  · rw [hd', t1]; push_cast; ring
  · rw [hd', t2]; push_cast; ring

/-- **Scale `f`, every member**: the base-β target at scale `f` has a tiling (the seed credited to M. Beeson with
D. Paliy's beta lift; formal proof `WSeedG.beta_seed`). -/
theorem betaTilable_self {e f : ℕ} (he : 1 ≤ e) (hef : e < f) : BetaTilable e f f := by
  obtain ⟨D, hT, hM⟩ := Erdos634.Draft.WSeedG.beta_seed e f he hef
  exact ⟨_, D, hasSides_congr hT (by ring) (by ring) (by ring), hM⟩

/-- every member at every multiple of `f` -/
theorem betaTilable_mul_self {e f : ℕ} (he : 1 ≤ e) (hef : e < f) {k : ℕ} (hk : 0 < k) :
    BetaTilable e f (k * f) :=
  betaTilable_mul (betaTilable_self he hef) hk

/-- **The threshold statement holds at every multiple of `f`, for every member.** -/
theorem threshold_mul_self {e f : ℕ} (he : 1 ≤ e) (hef : e < f) {k : ℕ} (hk : 0 < k) :
    ThresholdAt e f (k * f) :=
  ⟨fun _ => Nat.le_mul_of_pos_left f hk, fun _ => betaTilable_mul_self he hef hk⟩

/-- `f² (3f² − e²)` is a tile count for all `1 ≤ e < f` (and so is every `k² f² (3f² − e²)`). -/
theorem tileCount_beta_seed {e f : ℕ} (he : 1 ≤ e) (hef : e < f) :
    Erdos634.Draft.TileCountFamilies.TileCount (f ^ 2 * (3 * f ^ 2 - e ^ 2)) := by
  obtain ⟨D, -, -⟩ := Erdos634.Draft.WSeedG.beta_seed e f he hef
  exact ⟨D⟩

/-- the members `(1, 3)` and `(2, 3)` at every multiple of `3` -/
theorem betaTilable_f3_mul {e : ℕ} (he : e = 1 ∨ e = 2) {k : ℕ} (hk : 0 < k) : BetaTilable e 3 (k * 3) := by
  rcases he with rfl | rfl
  · exact betaTilable_mul betaTilable_1_3_three hk
  · exact betaTilable_mul betaTilable_2_3_three hk

/-! ## The member `(1, 2)`: the threshold statement at every scale -/

/-- **The member `(1, 2)`**: a tiling exists exactly for `M ≥ 2`. -/
theorem threshold_1_2 {M : ℕ} (hM : 1 ≤ M) : ThresholdAt 1 2 M := by
  constructor
  · intro h
    by_contra hlt
    have h1 : M = 1 := by omega
    subst h1
    exact not_betaTilable_one (by decide) le_rfl (by norm_num) h
  · intro h
    exact betaTilable_1_2 h

end Erdos634.Draft.UniformThreshold

#print axioms Erdos634.Draft.UniformThreshold.not_betaTilable_one
#print axioms Erdos634.Draft.UniformThreshold.threshold_1_2
#print axioms Erdos634.Draft.UniformThreshold.betaTilable_mul
#print axioms Erdos634.Draft.UniformThreshold.betaTilable_f3_mul
#print axioms Erdos634.Draft.UniformThreshold.threshold_mul_self
#print axioms Erdos634.Draft.UniformThreshold.tileCount_beta_seed

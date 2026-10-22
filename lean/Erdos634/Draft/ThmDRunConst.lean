import Mathlib.Tactic

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours. Here: the row induction on a run (their Lemmas 32-34, Theorem 37).
# Theorem D' run port, module 1: the constants of the gamma = 2 alpha tile  (DRAFT, NOT COMPILED, UNAUDITED)

Written 2026-10-18 while the Lean slot was busy; never run through `lake`/`lean`.  Not in `All`.  Mathlib only.

Port target: `Draft/SideRunGFrame.lean` section 1 (`rtG, uuG, hhG, nuG`, their specs), for the tile
`(a, b, c) = (u^2, v^2 - u^2, u v)`, `0 < u < v < 2u`, angles `α` (opposite `a`), `β = π - 3α` (opposite `b`),
`γ = 2α` (opposite `c`).  Here `cos α = v / (2u)`, so for a `c`-tile standing on the x-axis with its `α` end at the origin:

* `uuT u v = c - b cos α = v (3u^2 - v^2) / (2u)`  : abscissa of the apex measured from the `β` end
  (NOT positive in general: it is negative exactly when `v^2 > 3u^2`, i.e. `β` obtuse.  `uuG_pos` has NO analogue;
  every user of `uuG_pos` in `SideRunGChordB` (line 369) must be re-derived);
* `hhT u v = b sin α = (v^2 - u^2) √(4u^2 - v^2) / (2u)` : its height;
* `nuT u v = b / c = (v^2 - u^2) / (u v)`.  `nuG_lt_one` (ν < 1) has NO analogue: ν < 1 iff v/u < φ.  Users:
  `SideRunGChord` lines 439-440 (`m_nextG`, the bound δ(2+ν) < 1 for δ ≤ 1/3).  Here only `0 < ν < 3/2` holds.

Identities proved: `2u·uuT = v(3u²−v²)`, `2u·hhT = b·rt`, `uv·nuT = b`, `hh² = a² − uu²`, `hh² = b² − (c − uu)²`,
`2u (c − uu) = v b` (that is `b cos α = v b / (2u)`).
-/

namespace Erdos634.Draft.ThmDRun

variable {u v : ℝ}

theorem arg_pos (hu : 0 < u) (hv : v < 2 * u) (hv0 : 0 < v) : 0 < 4 * u ^ 2 - v ^ 2 := by
  nlinarith [mul_pos (sub_pos.2 hv) (add_pos hv0 (mul_pos two_pos hu))]

/-- `r = √(4u² − v²)` -/
noncomputable def rtT (u v : ℝ) : ℝ := Real.sqrt (4 * u ^ 2 - v ^ 2)

theorem rtT_sq (hu : 0 < u) (hv : v < 2 * u) (hv0 : 0 < v) : rtT u v ^ 2 = 4 * u ^ 2 - v ^ 2 :=
  Real.sq_sqrt (arg_pos hu hv hv0).le

theorem rtT_pos (hu : 0 < u) (hv : v < 2 * u) (hv0 : 0 < v) : 0 < rtT u v :=
  Real.sqrt_pos.mpr (arg_pos hu hv hv0)

/-- abscissa of the apex of a `c`-tile from its `β` end: `a cos β = c − b cos α` -/
noncomputable def uuT (u v : ℝ) : ℝ := v * (3 * u ^ 2 - v ^ 2) / (2 * u)

/-- height of the apex of a `c`-tile: `b sin α` -/
noncomputable def hhT (u v : ℝ) : ℝ := (v ^ 2 - u ^ 2) * rtT u v / (2 * u)

/-- `ν = b / c` -/
noncomputable def nuT (u v : ℝ) : ℝ := (v ^ 2 - u ^ 2) / (u * v)

theorem b_posT (huv : u < v) (hu : 0 < u) : 0 < v ^ 2 - u ^ 2 := by
  nlinarith [mul_pos (sub_pos.2 huv) (add_pos hu (hu.trans huv))]

theorem uuT_spec (hu : 0 < u) : 2 * u * uuT u v = v * (3 * u ^ 2 - v ^ 2) := by
  have h0 : (2 * u : ℝ) ≠ 0 := by positivity
  have := div_mul_cancel₀ (v * (3 * u ^ 2 - v ^ 2)) h0
  unfold uuT
  linear_combination this

theorem hhT_spec (hu : 0 < u) : 2 * u * hhT u v = (v ^ 2 - u ^ 2) * rtT u v := by
  have h0 : (2 * u : ℝ) ≠ 0 := by positivity
  have := div_mul_cancel₀ ((v ^ 2 - u ^ 2) * rtT u v) h0
  unfold hhT
  linear_combination this

theorem nuT_spec (hu : 0 < u) (hv : 0 < v) : u * v * nuT u v = v ^ 2 - u ^ 2 := by
  have h0 : (u * v : ℝ) ≠ 0 := (mul_pos hu hv).ne'
  have := div_mul_cancel₀ (v ^ 2 - u ^ 2) h0
  unfold nuT
  linear_combination this

theorem hhT_pos (hu : 0 < u) (huv : u < v) (hv : v < 2 * u) : 0 < hhT u v := by
  have hv0 : 0 < v := hu.trans huv
  unfold hhT
  exact div_pos (mul_pos (b_posT huv hu) (rtT_pos hu hv hv0)) (by positivity)

theorem nuT_pos (hu : 0 < u) (huv : u < v) : 0 < nuT u v := by
  have hv0 : 0 < v := hu.trans huv
  unfold nuT
  exact div_pos (b_posT huv hu) (mul_pos hu hv0)

/-- `ν < 3/2` (since `v < 2u`): the replacement of `nuG_lt_one` (`ν < 1` fails for `v/u ≥ φ`). -/
theorem nuT_lt (hu : 0 < u) (huv : u < v) (hv : v < 2 * u) : nuT u v < 3 / 2 := by
  have hv0 : 0 < v := hu.trans huv
  have hs := nuT_spec (v := v) hu hv0
  by_contra hcon
  push_neg at hcon
  nlinarith [mul_pos hu hv0, mul_pos (sub_pos.2 hv) (show (0 : ℝ) < 2 * v + u by positivity),
    mul_le_mul_of_nonneg_left hcon (mul_pos hu hv0).le]

/-- `2u (c − uu) = v b`, i.e. `b cos α = v b / (2u)`, `cos α = v / (2u)` -/
theorem cu_spec (hu : 0 < u) : 2 * u * (u * v - uuT u v) = v * (v ^ 2 - u ^ 2) := by
  have h := uuT_spec (v := v) hu
  linear_combination (-1 : ℝ) * h

/-- the height squared: `h² = a² − uu²` -/
theorem hhT_sq (hu : 0 < u) (hv : v < 2 * u) (hv0 : 0 < v) :
    hhT u v ^ 2 = (u ^ 2) ^ 2 - uuT u v ^ 2 := by
  have h1 := uuT_spec (v := v) hu
  have h2 := hhT_spec (v := v) hu
  have hr := rtT_sq hu hv hv0
  have h0 : (0 : ℝ) < (2 * u) ^ 2 := by positivity
  have key : (2 * u) ^ 2 * (hhT u v ^ 2 - ((u ^ 2) ^ 2 - uuT u v ^ 2)) = 0 := by
    have ee : (2 * u) ^ 2 * (hhT u v ^ 2 - ((u ^ 2) ^ 2 - uuT u v ^ 2))
        = (2 * u * hhT u v) ^ 2 - (2 * u) ^ 2 * (u ^ 2) ^ 2 + (2 * u * uuT u v) ^ 2 := by
      ring
    rw [ee, h1, h2]
    linear_combination ((v ^ 2 - u ^ 2) ^ 2) * hr
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h h0.ne'
  · linarith

/-- the height squared: `h² = b² − (c − uu)²` -/
theorem hhT_sq' (hu : 0 < u) (hv : v < 2 * u) (hv0 : 0 < v) :
    hhT u v ^ 2 = (v ^ 2 - u ^ 2) ^ 2 - (u * v - uuT u v) ^ 2 := by
  have h1 := hhT_sq hu hv hv0
  have hs := uuT_spec (v := v) hu
  -- a² − uu² = b² − (c − uu)²  because  c² − 2 c uu = b² − a²  and  2u·uu = v(3u²−v²)
  have key : (u ^ 2) ^ 2 - uuT u v ^ 2 = (v ^ 2 - u ^ 2) ^ 2 - (u * v - uuT u v) ^ 2 := by
    have e : (u ^ 2) ^ 2 - uuT u v ^ 2 - ((v ^ 2 - u ^ 2) ^ 2 - (u * v - uuT u v) ^ 2)
        = (u ^ 2) ^ 2 - (v ^ 2 - u ^ 2) ^ 2 + (u * v) ^ 2 - 2 * (u * v) * uuT u v := by ring
    have e2 : (u ^ 2) ^ 2 - (v ^ 2 - u ^ 2) ^ 2 + (u * v) ^ 2 - 2 * (u * v) * uuT u v = 0 := by
      have hu2 : u * ((u ^ 2) ^ 2 - (v ^ 2 - u ^ 2) ^ 2 + (u * v) ^ 2 - 2 * (u * v) * uuT u v) = 0 := by
        linear_combination (-(u * v)) * hs
      exact (mul_eq_zero.mp hu2).resolve_left hu.ne'
    linarith
  linarith

end Erdos634.Draft.ThmDRun

#print axioms Erdos634.Draft.ThmDRun.arg_pos
#print axioms Erdos634.Draft.ThmDRun.rtT_sq
#print axioms Erdos634.Draft.ThmDRun.rtT_pos
#print axioms Erdos634.Draft.ThmDRun.b_posT
#print axioms Erdos634.Draft.ThmDRun.uuT_spec
#print axioms Erdos634.Draft.ThmDRun.hhT_spec
#print axioms Erdos634.Draft.ThmDRun.nuT_spec
#print axioms Erdos634.Draft.ThmDRun.hhT_pos
#print axioms Erdos634.Draft.ThmDRun.nuT_pos
#print axioms Erdos634.Draft.ThmDRun.nuT_lt
#print axioms Erdos634.Draft.ThmDRun.cu_spec
#print axioms Erdos634.Draft.ThmDRun.hhT_sq
#print axioms Erdos634.Draft.ThmDRun.hhT_sq'

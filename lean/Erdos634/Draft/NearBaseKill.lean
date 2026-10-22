-- Draft/NearBaseKill.lean — R5 composed: the family `(f+1) ∣ e²` point at distance `δ = e²/(f+1)`
-- along `r` is killed by NB.  `family_point_killed` = `NearBaseVertex.nb_of_fan` (PROVED) ∘
-- `NearBase.family_nb` (PROVED): a statement about a `LocalFan` at that point.  With
-- `NearBaseVertex.localFan_of_tiles` (PROVED) it applies to any finite family of triangles; that
-- composition is `family_point_killed_tiles` (PROVED, no `sorry`).
-- Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- Build: scratch oleans for Draft/NearBase and Draft/NearBaseVertex, then
--   lake env bash -c 'LEAN_PATH=$S:$LEAN_PATH lean Erdos634/Draft/NearBaseKill.lean'
import Erdos634.Draft.NearBase
import Erdos634.Draft.NearBaseVertex

namespace Erdos634.Draft.NearBaseKill

open Real Erdos634.Geometry Erdos634.Draft.NearBase Erdos634.Draft.NearBaseVertex

/-- **The family point is killed (R5, family + NB), modulo nothing but the local fan.**  For a
coprime member `2 ≤ e ≤ f − 2` with `(f+1) ∣ e²`, a point at height `h = (e²/(f+1))·cos(α/2)` that
carries a local fan of base-β tiles (`ℓ = min(ef, f²−e²)`, `L = f²`, `H = (f²−e²)·sin α`,
`c₀ = −cos γ = e/(2f)`) does not exist. -/
theorem family_point_killed {e f : ℕ} (hcop : Nat.Coprime e f) (he : 2 ≤ e) (hef : e + 2 ≤ f)
    (hdvd : (f + 1) ∣ e ^ 2) {x : ℝ} (hs : sin x = e / (2 * f)) (hx0 : 0 < x) (hx1 : x < π / 2)
    (F : LocalFan ((e : ℝ) ^ 2 / (f + 1) * cos x) (min ((e : ℝ) * f) ((f : ℝ) ^ 2 - e ^ 2))
      ((f : ℝ) ^ 2) (((f : ℝ) ^ 2 - e ^ 2) * sin (2 * x)) ((e : ℝ) / (2 * f))) : False := by
  obtain ⟨h1, h2⟩ := family_nb hcop he hef hdvd hs hx0 hx1
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast he
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast hef
  have hfR : (0 : ℝ) < f := by linarith
  have hc : 0 < cos x := cos_pos_of_mem_Ioo ⟨by linarith, hx1⟩
  have hb0 : 0 < (f : ℝ) ^ 2 - e ^ 2 := by nlinarith
  set h : ℝ := (e : ℝ) ^ 2 / (f + 1) * cos x with hhdef
  set ℓ : ℝ := min ((e : ℝ) * f) ((f : ℝ) ^ 2 - e ^ 2) with hℓdef
  have hh : 0 < h := by positivity
  have hℓ0 : 0 < ℓ := lt_min (by positivity) hb0
  have hsin2 : 0 < sin (2 * x) := by
    rw [sin_two_mul]
    have : 0 < sin x := by rw [hs]; positivity
    positivity
  have hH0 : 0 ≤ ((f : ℝ) ^ 2 - e ^ 2) * sin (2 * x) := by positivity
  have hgpos := cos_gamma_half_pos hx0 hx1
  have hg := cos_sq_gamma_half (by positivity : (f : ℝ) ≠ 0) hs
  have hsq1 := (cond1_iff_sq hh.le hℓ0 hgpos).mp h1
  rw [hg] at hsq1
  have h1' : 2 * h ^ 2 < ℓ ^ 2 * (1 - (e : ℝ) / (2 * f)) := by
    have : ℓ ^ 2 * ((2 * f - e) / (4 * f)) = ℓ ^ 2 * (1 - (e : ℝ) / (2 * f)) / 2 := by
      field_simp; ring
    linarith
  have hlt : h < ℓ := by
    have : cos ((π / 2 + x) / 2) ≤ 1 := cos_le_one _
    nlinarith
  have h2' := sq_of_cond2 hh.le hℓ0 (by positivity) hH0 hlt h2
  exact nb_of_fan F hh hℓ0 hH0 (by positivity) (by positivity) h1' h2'

/-- The same for an actual finite family of triangles (through `localFan_of_tiles`, PROVED). -/
theorem family_point_killed_tiles {e f : ℕ} (hcop : Nat.Coprime e f) (he : 2 ≤ e)
    (hef : e + 2 ≤ f) (hdvd : (f + 1) ∣ e ^ 2) {α : ℝ} (hs : sin α = e / (2 * f)) (hx0 : 0 < α)
    (hx1 : α < π / 2) {n : ℕ} (T : Fin n → Tri) (x : Plane) {r : ℝ} (hr : 0 < r)
    (hcov : Metric.ball x r ⊆ ⋃ i, (T i).carrier)
    (hdisj : Pairwise fun i j => Disjoint (interior (T i).carrier) (interior (T j).carrier))
    (hup : ∀ i k, 0 ≤ (T i).pts k 1) (hcorner : ∃ i k, (T i).pts k = x)
    (hx : x 1 = (e : ℝ) ^ 2 / (f + 1) * cos α)
    (hside : ∀ i j k, j ≠ k →
      min ((e : ℝ) * f) ((f : ℝ) ^ 2 - e ^ 2) ≤ dist ((T i).pts j) ((T i).pts k))
    (hlong : ∀ i j k, dist ((T i).pts j) ((T i).pts k) ≤ (f : ℝ) ^ 2)
    (hcos : ∀ i (j : Fin 3), -((e : ℝ) / (2 * f)) * dist ((T i).pts (j + 1)) ((T i).pts j)
        * dist ((T i).pts (j + 2)) ((T i).pts j)
      ≤ ((T i).pts (j + 1) 0 - (T i).pts j 0) * ((T i).pts (j + 2) 0 - (T i).pts j 0)
        + ((T i).pts (j + 1) 1 - (T i).pts j 1) * ((T i).pts (j + 2) 1 - (T i).pts j 1))
    (halt : ∀ i (j : Fin 3), ((f : ℝ) ^ 2 - e ^ 2) * sin (2 * α)
        * dist ((T i).pts (j + 1)) ((T i).pts (j + 2))
      ≤ |cross ((T i).pts (j + 1) - (T i).pts j) ((T i).pts (j + 2) - (T i).pts j)|) : False := by
  obtain ⟨F⟩ := localFan_of_tiles T x hr hcov hdisj hup hcorner hside hlong hcos halt
  rw [hx] at F
  exact family_point_killed hcop he hef hdvd hs hx0 hx1 F

/-- The numeric side of `nb_of_fan` at (4,7) (`h² = 180/49`, `ℓ = 28`, `L = 49`, `c₀ = 2/7`,
`H² = 784080/2401`): (1) `2h² < ℓ²(1 − c₀)`, (2) `h²((ℓ+L)² + H²) < H²ℓ²` — satisfiable. -/
theorem nb_numeric_47 :
    2 * (180 / 49 : ℚ) < 28 ^ 2 * (1 - 4 / (2 * 7)) ∧
    (180 / 49 : ℚ) * ((28 + 49) ^ 2 + 784080 / 2401) < 784080 / 2401 * 28 ^ 2 := by
  norm_num

end Erdos634.Draft.NearBaseKill

#print axioms Erdos634.Draft.NearBaseKill.family_point_killed
#print axioms Erdos634.Draft.NearBaseKill.family_point_killed_tiles
#print axioms Erdos634.Draft.NearBaseKill.nb_numeric_47

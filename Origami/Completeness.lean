import Origami.Geo
import Origami.Alg
import Origami.Lemmas
import Origami.Tactics
import Origami.Analytic

open ComplexConjugate

namespace Origami
open Line

syntax (name := extractAllPoints) "extract_all_points" : tactic

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| extract_all_points) => withMainContext do
    let lctx ← getLCtx
    let mut tacticsToRun : Array Syntax := #[]

    for ldecl in lctx do
      if ldecl.isAuxDecl then continue
      let type ← inferType ldecl.toExpr
      if (← isExprDefEq type (mkConst ``Complex)) then
        let name := ldecl.userName
        let reIdent := mkIdent (Name.mkSimple (name.toString ++ "_re"))
        let imIdent := mkIdent (Name.mkSimple (name.toString ++ "_im"))
        let ptIdent := mkIdent name

        -- create P1.re = P1.re and P1.im = P1.im
        tacticsToRun :=
          tacticsToRun.push (← `(tactic| have $reIdent : ($ptIdent : ℂ).re = ($ptIdent : ℂ).re := rfl))
        tacticsToRun :=
          tacticsToRun.push (← `(tactic| have $imIdent : ($ptIdent : ℂ).im = ($ptIdent : ℂ).im := rfl))

        -- conv changes only the RHS to get a nontrivial equation
        tacticsToRun :=
          tacticsToRun.push (← `(tactic| try conv at $reIdent =>
          rhs
          unfold $ptIdent))
        tacticsToRun :=
          tacticsToRun.push (← `(tactic| try conv at $imIdent =>
          rhs
          unfold $ptIdent))

        -- simplify the RHS
        let simpTacRe ← `(tactic| try conv at $reIdent =>
          rhs
          simp (config := { zeta := true }) only [
            Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
            Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
            Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
            Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im])
        tacticsToRun := tacticsToRun.push simpTacRe

        let simpTacIm ← `(tactic| try conv at $imIdent =>
          rhs
          simp (config := { zeta := true }) only [
            Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
            Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
            Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
            Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im])
        tacticsToRun := tacticsToRun.push simpTacIm

    -- execute all the generated tactics
    for tac in tacticsToRun do
      evalTactic tac

def xAxis : Line := ⟨0, 1, one_ne_zero⟩
def yAxis : Line := ⟨0, Complex.I, Complex.I_ne_zero⟩

#print GeoConstrLine
theorem cline_xAxis : GeoConstrLine xAxis :=
  .o1 .zero .one zero_ne_one ⟨by simp [mem_def, xAxis], by simp [mem_def, xAxis]⟩

theorem cline_yAxis : GeoConstrLine yAxis :=
  .o4 .zero cline_xAxis ⟨by simp [yAxis, Perp, xAxis], by simp [mem_def, yAxis]⟩

def perpThrough (p : ℂ) (l : Line) : Line :=
  ⟨p, Complex.I * l.d, mul_ne_zero Complex.I_ne_zero l.hd⟩

theorem perpThrough_perp (p : ℂ) (l : Line) : (perpThrough p l).Perp l := by
  simp [perpThrough, Perp]
  ring_nf

theorem cline_perpThrough {p : ℂ} {l : Line} (hp : GeoConstrPt p) (hl : GeoConstrLine l) :
    GeoConstrLine (perpThrough p l) := by
  have := perpThrough_perp p l
  set m := perpThrough p l with hm
  exact (.o4 hp hl ⟨this, mem_self m⟩)

def parThrough (p : ℂ) (l : Line) : Line := perpThrough p (perpThrough p l)

theorem cline_parThrough {p : ℂ} {l : Line} (hp : GeoConstrPt p) (hl : GeoConstrLine l) :
    GeoConstrLine (parThrough p l) :=
  cline_perpThrough hp (cline_perpThrough hp hl)

theorem parThrough_par (p : ℂ) (l : Line) : (parThrough p l).Par l := by
  unfold Par parThrough perpThrough
  simp
  ring

theorem mem_parThrough (p : ℂ) (l : Line) : p ∈ parThrough p l :=
  mem_self (parThrough p l)

theorem reflect_eq_iff (f : Line) (p q : ℂ) :
    f.reflect p = q ↔ (q - f.p) * conj f.d = f.d * conj (p - f.p) := by
  have hc : conj f.d ≠ 0 := (map_ne_zero _).2 f.hd
  have key : f.reflect p = q ↔ q - f.p = f.d / conj f.d * conj (p - f.p) := by
    unfold Line.reflect
    constructor <;> intro h <;> linear_combination (-1 : ℂ) * h
  rw [key, div_mul_eq_mul_div, eq_div_iff hc]

noncomputable def bisector (p q : ℂ) (h : p ≠ q) : Line :=
  ⟨(p + q) / 2, Complex.I * (q - p), mul_ne_zero Complex.I_ne_zero (sub_ne_zero.2 h.symm)⟩

theorem reflect_bisector (p q : ℂ) (h : p ≠ q) : (bisector p q h).reflect p = q := by
  rw [reflect_eq_iff, bisector]
  to_re_im
  ring_nf; simp; ring_nf

theorem cline_bisector {p q : ℂ} (hp : GeoConstrPt p) (hq : GeoConstrPt q) (h : p ≠ q) :
    GeoConstrLine (bisector p q h) :=
  .o2 hp hq h (reflect_bisector p q h)

theorem yAxis_reflect_ofReal (x : ℝ) : yAxis.reflect (x : ℂ) = -(x : ℂ) := by
  simp [yAxis, reflect]

theorem cpt_neg {x : ℝ} (h : GeoConstrPt (x : ℂ)) : GeoConstrPt ((-x : ℝ) : ℂ) := by
  have := GeoConstrPt.reflect h cline_yAxis
  simp [yAxis_reflect_ofReal] at this
  simpa using this

theorem bisector_reflect_ofReal (a b : ℝ) (h : (0 : ℂ) ≠ b) :
    (bisector 0 b h).reflect (a : ℂ) = ((b - a : ℝ) : ℂ) := by
  rw [reflect_eq_iff]
  simp [bisector, map_ofNat]
  ring_nf

theorem cpt_sub {a b : ℝ} (ha : GeoConstrPt (a : ℂ)) (hb : GeoConstrPt (b : ℂ)) :
    GeoConstrPt ((b - a : ℝ) : ℂ) := by
  by_cases hb0 : b = 0
  · simp [hb0]
    simpa using cpt_neg ha
  · have hne : (0 : ℂ) ≠ (b : ℂ) := by exact_mod_cast (by grind)
    have h1 := GeoConstrPt.reflect ha (cline_bisector GeoConstrPt.zero hb hne)
    rw [bisector_reflect_ofReal] at h1
    exact h1

theorem cpt_add {a b : ℝ} (ha : GeoConstrPt (a : ℂ)) (hb : GeoConstrPt (b : ℂ)) :
    GeoConstrPt ((a + b : ℝ) : ℂ) := by
  have h := cpt_sub (cpt_neg ha) hb
  have e : a + b = b - -a := by ring
  rw [e]
  exact h

def foldI : Line :=
  ⟨1, Complex.I - 1, sub_ne_zero.2 (fun h => by
    have := congrArg Complex.re h
    simp at this)⟩

theorem foldI_reflect_zero : foldI.reflect 0 = 1 + Complex.I := by
  rw [reflect_eq_iff]
  simp only [foldI, map_sub, Complex.conj_I, map_one, map_zero]
  linear_combination (-1 : ℂ) * Complex.I_sq

theorem cline_foldI : GeoConstrLine foldI :=
  .o5 .zero .one (cline_perpThrough .one cline_xAxis) zero_ne_one
    ⟨by rw [foldI_reflect_zero]; simp [mem_def, perpThrough, xAxis], mem_self _⟩

theorem cpt_I : GeoConstrPt Complex.I :=
  .inter (l := foldI) (m := yAxis)
    cline_foldI
    cline_yAxis
    (by simp [Par, foldI, yAxis])
    (by simp [mem_def, foldI])
    (by simp [mem_def, yAxis])

def lineThrough (p q : ℂ) (h : p ≠ q) : Line :=
  ⟨p, q - p, sub_ne_zero.2 h.symm⟩

theorem cline_lineThrough {p q : ℂ} (hp : GeoConstrPt p) (hq : GeoConstrPt q) (h : p ≠ q) :
    GeoConstrLine (lineThrough p q h) :=
  .o1 hp hq h ⟨mem_self (lineThrough p q h), by simp [mem_def, lineThrough]; linarith⟩

theorem diag_reflect_ofReal (b : ℝ) (h : (1 : ℂ) ≠ Complex.I) :
    (bisector 1 Complex.I h).reflect (b : ℂ) = (b : ℂ) * Complex.I := by
  rw [reflect_eq_iff]
  simp [bisector, map_ofNat]
  linear_combination (b - 1) * Complex.I * Complex.I_sq

theorem one_ne_I : (1 : ℂ) ≠ Complex.I := by
  intro h
  to_re_im at h
  simp [Complex.I_re, Complex.I_im] at *

theorem cpt_toY {b : ℝ} (hb : GeoConstrPt (b : ℂ)) : GeoConstrPt ((b : ℂ) * Complex.I) := by
  have h := GeoConstrPt.reflect hb (cline_bisector GeoConstrPt.one cpt_I one_ne_I)
  rwa [diag_reflect_ofReal b one_ne_I] at h

theorem I_ne_ofReal (a : ℝ) : Complex.I ≠ (a : ℂ) := by
  intro h
  to_re_im at h
  simp [Complex.I_re, Complex.I_im] at *

theorem ofReal_mul_I_ne_one {a : ℝ} : (a : ℂ) * Complex.I ≠ 1 := by
  intro h
  to_re_im at h
  simp [Complex.I_re, Complex.I_im] at *

-- l = line through p,q. parallel to l through r meets the x-axis at x
theorem cpt_similar {p q r : ℂ} {x : ℝ} (hp : GeoConstrPt p) (hq : GeoConstrPt q) (hr : GeoConstrPt r)
    (hpq : p ≠ q)
    (hpar : ¬ (parThrough r (lineThrough p q hpq)).Par xAxis)
    (hmem : (x : ℂ) ∈ parThrough r (lineThrough p q hpq)) : GeoConstrPt (x : ℂ) :=
  GeoConstrPt.inter (cline_parThrough hr (cline_lineThrough hp hq hpq)) cline_xAxis hpar hmem
    (by simp [Line.mem_def, xAxis])

syntax "tri_simp" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| tri_simp) =>
    `(tactic| (simp [Line.Par, Line.mem_def, parThrough, perpThrough, lineThrough, xAxis,
        Complex.mul_im, Complex.mul_re] <;>
        first | ring | (field_simp; try ring) | linarith | nlinarith))
  | `(tactic| tri_simp [$ts,*]) =>
    `(tactic| (simp [Line.Par, Line.mem_def, parThrough, perpThrough, lineThrough, xAxis,
        Complex.mul_im, Complex.mul_re, $ts,*] <;>
        first | ring | (field_simp; try ring) | linarith | nlinarith))

theorem cpt_mul {a b : ℝ} (ha : GeoConstrPt (a : ℂ)) (hb : GeoConstrPt (b : ℂ)) :
    GeoConstrPt ((a * b : ℝ) : ℂ) :=
  cpt_similar (x := a * b) cpt_I ha (cpt_toY hb) (I_ne_ofReal a)
    (by tri_simp) (by tri_simp)

theorem cpt_inv {a : ℝ} (ha : GeoConstrPt (a : ℂ)) : GeoConstrPt ((a⁻¹ : ℝ) : ℂ) := by
  by_cases h0 : a = 0
  · subst h0
    simpa using GeoConstrPt.zero
  · exact cpt_similar (x := a⁻¹) (cpt_toY ha) GeoConstrPt.one cpt_I
      (ofReal_mul_I_ne_one) (by tri_simp [h0]) (by tri_simp [h0])

theorem cpt_nat (n : ℕ) : GeoConstrPt ((n : ℝ) : ℂ) := by
  induction n with
  | zero => simp [GeoConstrPt.zero]
  | succ n ih =>
    have h := cpt_add ih (by simp [GeoConstrPt.one] : GeoConstrPt ((1 : ℝ) : ℂ))
    rw [Nat.cast_succ]
    exact h

-- AI generated
theorem cpt_int (z : ℤ) : GeoConstrPt ((z : ℝ) : ℂ) := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · simpa using cpt_nat n
  · simpa using cpt_neg (cpt_nat n)

theorem cpt_rat (q : ℚ) : GeoConstrPt ((q : ℝ) : ℂ) := by
  have h := cpt_mul (cpt_int q.num) (cpt_inv (cpt_nat q.den))
  have h1 : (q : ℝ) = (q.num : ℝ) * ((q.den : ℝ))⁻¹ := by
    rw [Rat.cast_def, div_eq_mul_inv]
  rw [h1]
  exact h

theorem ofReal_mul_I_re (b : ℝ) : ((b : ℂ) * Complex.I).re = 0 := by simp
theorem ofReal_mul_I_im (b : ℝ) : ((b : ℂ) * Complex.I).im = b := by simp

theorem mem_horiz (w z : ℂ) : z ∈ parThrough w xAxis ↔ z.im = w.im := by
  rw [mem_def]
  simp [parThrough, perpThrough, xAxis]
  constructor <;> intros <;> linarith

theorem mem_vert (w z : ℂ) : z ∈ perpThrough w xAxis ↔ z.re = w.re := by
  rw [mem_def]
  simp [perpThrough, xAxis]
  constructor <;> intros <;> linarith

theorem not_par_horiz_vert (w w' : ℂ) :
    ¬ (parThrough w xAxis).Par (perpThrough w' xAxis) := by
  intro h
  simp [Par, parThrough, perpThrough, xAxis] at h

theorem not_par_vert_horiz (w w' : ℂ) :
    ¬ (perpThrough w xAxis).Par (parThrough w' xAxis) := by
  intro h
  simp [Par, parThrough, perpThrough, xAxis] at h

theorem cpt_mk {u v : ℝ} (hu : GeoConstrPt (u : ℂ)) (hv : GeoConstrPt (v : ℂ)) : GeoConstrPt (⟨u, v⟩ : ℂ) := by
  have hV := cline_perpThrough hu cline_xAxis
  have hH := cline_parThrough (cpt_toY hv) cline_xAxis -- strange-ish definition so it's easier to use stated theorems.
  exact GeoConstrPt.inter hV hH (not_par_vert_horiz _ _)
    (by rw [mem_vert]; simp) (by rw [mem_horiz]; simp)

def RC (x : ℝ) : Prop := GeoConstrPt (x : ℂ)

theorem RC.zero : RC 0 := by unfold RC; simpa using GeoConstrPt.zero
theorem RC.one : RC 1 := by unfold RC; simpa using GeoConstrPt.one
theorem RC.add {x y : ℝ} (hx : RC x) (hy : RC y) : RC (x + y) := cpt_add hx hy
theorem RC.mul {x y : ℝ} (hx : RC x) (hy : RC y) : RC (x * y) := cpt_mul hx hy
theorem RC.neg {x : ℝ} (hx : RC x) : RC (-x) := cpt_neg hx
theorem RC.inv {x : ℝ} (hx : RC x) : RC x⁻¹ := cpt_inv hx
theorem RC.sub {x y : ℝ} (hx : RC x) (hy : RC y) : RC (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg
theorem RC.div {x y : ℝ} (hx : RC x) (hy : RC y) : RC (x / y) := by
  rw [div_eq_mul_inv]; exact hx.mul hy.inv
theorem RC.pow {x : ℝ} (hx : RC x) : ∀ n : ℕ, RC (x ^ n)
  | 0 => by simpa using RC.one
  | n + 1 => by rw [pow_succ]; exact (RC.pow hx n).mul hx
theorem RC.ofNat (n : ℕ) [n.AtLeastTwo] : RC (OfNat.ofNat n : ℝ) := by
  have := cpt_nat n
  unfold RC
  exact_mod_cast this

syntax "rc_core" : tactic
macro_rules
  | `(tactic| rc_core) => `(tactic| first
    | assumption
    | exact RC.zero
    | exact RC.one
    | exact RC.ofNat _
    | (apply RC.sub <;> rc_core)
    | (apply RC.div <;> rc_core)
    | (apply RC.add <;> rc_core)
    | (apply RC.mul <;> rc_core)
    | (apply RC.neg; rc_core)
    | (apply RC.inv; rc_core)
    | (apply RC.pow; rc_core))

macro "rc" : tactic => `(tactic| rc_core)

theorem cpt_half : GeoConstrPt ((1 / 2 : ℝ) : ℂ) := by
  have h : RC (1 / 2) := by rc -- fsr `exact_mod_cast AlgConstrNum.rat (1/2)` does not work
  exact h

theorem cpt_div2 {x : ℝ} (hx : GeoConstrPt (x : ℂ)) : GeoConstrPt ((x / 2 : ℝ) : ℂ) := by
  have h := cpt_mul hx cpt_half
  rw [show x * (1 / 2) = x / 2 by ring] at h
  assumption

theorem diag_reflect_Y (b : ℝ) :
    (bisector 1 Complex.I one_ne_I).reflect ((b : ℂ) * Complex.I) = (b : ℂ) := by
  rw [reflect_eq_iff]
  simp [bisector, map_ofNat]
  linear_combination ((b : ℂ) - 1) * Complex.I * Complex.I_sq

theorem cpt_fromY {b : ℝ} (hb : GeoConstrPt ((b : ℂ) * Complex.I)) : GeoConstrPt (b : ℂ) := by
  have h := GeoConstrPt.reflect hb (cline_bisector GeoConstrPt.one cpt_I one_ne_I)
  rwa [diag_reflect_Y] at h

noncomputable def bfold (t : ℝ) : Line :=
  ⟨1 - (t : ℂ) * Complex.I, (t : ℂ) + Complex.I, by by_contra; to_re_im at this; obtain ⟨h1, h2⟩ := this; simp [Complex.I_im] at h2⟩

theorem mem_bfold (t : ℝ) (z : ℂ) :
    z ∈ bfold t ↔ 1 * z.re + (-t) * z.im + (-(1 + t ^ 2)) = 0 := by
  simp [mem_def, bfold]
  constructor <;> intros <;> linarith

theorem bfold_reflect (t : ℝ) (P : ℂ) :
    ((bfold t).reflect P).re = P.re - 2 * (P.re - t * P.im - (1 + t ^ 2)) / (1 + t ^ 2) ∧
    ((bfold t).reflect P).im = P.im + 2 * t * (P.re - t * P.im - (1 + t ^ 2)) / (1 + t ^ 2) := by
  obtain ⟨e1, e2⟩ := reflect_formula (f := bfold t) (a := 1) (b := -t)
    (c := -(1 + t ^ 2)) (Or.inl one_ne_zero) (mem_bfold t) P
  have hden : (1 : ℝ) ^ 2 + (-t) ^ 2 = 1 + t ^ 2 := by ring
  have hN : (1 + t ^ 2) ≠ 0 := by positivity
  constructor
  · rw [e1, hden]; ring
  · rw [e2, hden]; ring

-- the crease through (1, -t) perpendicular to O(1, -t)
-- sends O to the line x = 2, and sends T to the line y = a + c iff t is a root.
theorem beloch_fold {t a b c : ℝ} (h : t ^ 3 + a * t ^ 2 + b * t + c = 0)
    (T : ℂ) (hTre : T.re = 1 - b) (hTim : T.im = a - c) :
    ((bfold t).reflect 0).re = 2 ∧ ((bfold t).reflect T).im = a + c := by
  have hN : (1 + t ^ 2) ≠ 0 := by positivity
  obtain ⟨r0, _⟩ := bfold_reflect t 0
  obtain ⟨_, rT⟩ := bfold_reflect t T
  constructor
  · have h1 : 2 * (1 + t ^ 2) / (1 + t ^ 2) = 2 := by field_simp
    rw [r0, Complex.zero_re, Complex.zero_im]
    ring_nf at *
    assumption
  · have h1 : 2 * t * (1 - b - t * (a - c) - (1 + t ^ 2)) / (1 + t ^ 2) = 2 * c := by
      rw [div_eq_iff hN]
      linear_combination (-2 : ℝ) * h
    rw [rT, hTre, hTim]
    linear_combination h1

theorem cpt_proj_im {z : ℂ} (hz : GeoConstrPt z) : RC z.im := by
  have hH := cline_parThrough hz cline_xAxis
  have hY : GeoConstrPt ((z.im : ℂ) * Complex.I) :=
    GeoConstrPt.inter hH cline_yAxis
      (by
        intro h
        simp [Par, parThrough, perpThrough, xAxis, yAxis] at h)
      (by rw [mem_horiz, ofReal_mul_I_im])
      (by simp [mem_def, yAxis])
  exact cpt_fromY hY

#print GeoConstrLine
#print RC
theorem cpt_cubic {a b c r : ℝ} (ha : RC a) (hb : RC b) (hc : RC c)
    (h : r ^ 3 + a * r ^ 2 + b * r + c = 0) : GeoConstrPt r := by
  by_cases hr : r = 0
  · rw [hr]; rc
  obtain ⟨h1b, hac, hs, h2⟩ : RC (1 - b) ∧ RC (a - c) ∧ RC (a + c) ∧ RC 2 :=
    ⟨by rc, by rc, by rc, by rc⟩
  obtain ⟨T, hTre, hTim, hT⟩ : ∃ T : ℂ, T.re = 1 - b ∧ T.im = a - c ∧ GeoConstrPt T :=
    ⟨⟨1 - b, a - c⟩, rfl, rfl, cpt_mk h1b hac⟩
  obtain ⟨hO1, hO2⟩ := beloch_fold h T hTre hTim
  have hl : GeoConstrLine (perpThrough ((2 : ℝ) : ℂ) xAxis) :=
    cline_perpThrough h2 cline_xAxis
  have hm : GeoConstrLine (parThrough ((a + c : ℝ) * Complex.I) xAxis) :=
    cline_parThrough (cpt_toY hs) cline_xAxis
  have hf : GeoConstrLine (bfold r) :=
    GeoConstrLine.o6 GeoConstrPt.zero hT hl hm
      (by intro hh; rw [mem_vert] at hh; norm_num at hh)
      (not_par_vert_horiz _ _)
      ⟨by rw [mem_vert]; exact hO1,
        by rw [mem_horiz, ofReal_mul_I_im]; exact hO2⟩
  have hV : GeoConstrLine (perpThrough (1 : ℂ) xAxis) := cline_perpThrough GeoConstrPt.one cline_xAxis
  have hXim : (bfold r).p.im = -r := by simp [bfold, Complex.mul_im]
  have h3 := cpt_proj_im (.inter hf hV
      (fun e => hr (by
        simp [Line.Par, bfold, perpThrough, xAxis] at e; linarith))
      (mem_self _)
      (by rw [mem_vert]; simp [bfold, Complex.mul_re]))
  rw [hXim] at h3
  have h4 := h3.neg
  rwa [neg_neg] at h4

theorem sqrt_root (x : ℝ) :
    Real.sqrt x ^ 3 + 0 * Real.sqrt x ^ 2 + (-x) * Real.sqrt x + 0 = 0 := by
  rcases le_or_gt 0 x with h0 | h0
  · have h1 := Real.sq_sqrt h0
    linear_combination Real.sqrt x * h1
  · rw [Real.sqrt_eq_zero_of_nonpos h0.le]
    ring

theorem cpt_sqrt {a : ℝ} (ha : RC a) : RC (Real.sqrt a) := by
  have : Real.sqrt a ^ 3 + 0 * Real.sqrt a ^ 2 + (-a) * Real.sqrt a + 0 = 0 := by
    exact sqrt_root a
  exact cpt_cubic RC.zero ha.neg RC.zero this
#print GeoConstrPt

end Origami

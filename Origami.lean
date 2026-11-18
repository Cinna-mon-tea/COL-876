import Origami.Soundness
import Origami.Completeness

namespace Origami
open Line

mutual
theorem sound_pt : ∀ {z : ℂ}, GeoConstrPt z → AlgConstrNum z.re ∧ AlgConstrNum z.im
  | _, .zero => by simp [AlgConstrNum.zero]
  | _, .one => by simp [AlgConstrNum.one, AlgConstrNum.zero]
  | _, .inter hl hm hn hzl hzm => inter_aux (sound_line hl) (sound_line hm) hn hzl hzm
  | _, .reflect hp hf => reflect_aux (sound_pt hp) (sound_line hf)

theorem sound_line : ∀ {f : Line}, GeoConstrLine f → AlgConstrLine f
  | _, .o1 hp hq hne h => o1_aux (sound_pt hp) (sound_pt hq) hne h
  | _, .o2 hp hq hne h => o2_aux (sound_pt hp) (sound_pt hq) hne h
  | _, .o3 hl hm hn h => o3_aux (sound_line hl) (sound_line hm) hn h
  | _, .o4 hp hl h => o4_aux (sound_pt hp) (sound_line hl) h
  | _, .o5 hp hq hl hne h => o5_aux (sound_pt hp) (sound_pt hq) (sound_line hl) hne h
  | _, .o6 hp hq hl hm hpl hlm h =>
    o6_aux (sound_pt hp) (sound_pt hq) (sound_line hl) (sound_line hm) hpl hlm h
  | _, .o7 hp hl hm hlm h => o7_aux (sound_pt hp) (sound_line hl) (sound_line hm) hlm h
  | _, .same hf he => by
    obtain ⟨a, b, c, ha, hb, hc, hab, h⟩ := sound_line hf
    exact ⟨a, b, c, ha, hb, hc, hab, fun z => (mem_congr he z).symm.trans (h z)⟩
end

theorem complete_real {x : ℝ} (h : AlgConstrNum x) : GeoConstrPt (x : ℂ) := by
  induction h with
  | rat q => exact cpt_rat q
  | add hx hy ihx ihy => exact cpt_add ihx ihy
  | mul hx hy ihx ihy => exact cpt_mul ihx ihy
  | neg hx ihx => exact cpt_neg ihx
  | inv hx ihx => exact cpt_inv ihx
  | sqrt hx ihx => exact cpt_sqrt ihx
  | cubic ha hb hc hr iha ihb ihc => exact cpt_cubic iha ihb ihc hr

#print GeoConstrPt
theorem complete_pt {z : ℂ} (h : AlgConstrNum z.re ∧ AlgConstrNum z.im) : GeoConstrPt z :=
  cpt_mk (complete_real h.1) (complete_real h.2)

theorem cross_zero_of_normal {a b u1 u2 v1 v2 : ℝ} (hab : a ≠ 0 ∨ b ≠ 0)
    (hu : a * u1 + b * u2 = 0) (hv : a * v1 + b * v2 = 0) :
    u1 * v2 - u2 * v1 = 0 := by
  rcases hab with h | h
  · apply mul_left_cancel₀ h
    linear_combination v2 * hu - u2 * hv
  · apply mul_left_cancel₀ h
    linear_combination u1 * hv - v1 * hu

theorem complete_line_of_points {f : Line} {a b c : ℝ} (hab : a ≠ 0 ∨ b ≠ 0)
    (hf : ∀ z : ℂ, z ∈ f ↔ a * z.re + b * z.im + c = 0)
    {P Q : ℂ} (hP : GeoConstrPt P) (hQ : GeoConstrPt Q) (hPnQ : P ≠ Q)
    (hPf : a * P.re + b * P.im + c = 0) (hQf : a * Q.re + b * Q.im + c = 0) :
    GeoConstrLine f := by
  have hg := cline_lineThrough hP hQ hPnQ
  have hn := normal_of_mem f a b c hf
  have hcross : (Q.re - P.re) * f.d.im - (Q.im - P.im) * f.d.re = 0 :=
    cross_zero_of_normal hab (by linear_combination hQf - hPf) hn
  have hpar : Line.Par (lineThrough P Q hPnQ) f := by
    simp [Par, lineThrough]
    linear_combination (-1 : ℝ) * hcross
  exact GeoConstrLine.same hg ⟨hpar, (hf P).2 hPf⟩

theorem complete_line {f : Line} (h : AlgConstrLine f) : GeoConstrLine f := by
  obtain ⟨a, b, c, ha, hb, hc, hab, hf⟩ := h
  by_cases hb0 : b = 0
  · have ha0 : a ≠ 0 := by
      intro h1
      cases hab <;> contradiction
    refine complete_line_of_points (P := ⟨-c / a, 0⟩) (Q := ⟨-c / a, 1⟩) hab hf
      (complete_pt ⟨by show AlgConstrNum (-c / a); is_oc, by show AlgConstrNum 0; exact AlgConstrNum.zero⟩)
      (complete_pt ⟨by show AlgConstrNum (-c / a); is_oc, by show AlgConstrNum 1; exact AlgConstrNum.one⟩)
      (by intro h; have := congrArg Complex.im h; simp at this)
      ?_ ?_
      <;> {to_re_im; rw [hb0]; field_simp; ring}
  · refine complete_line_of_points (P := ⟨0, -c / b⟩) (Q := ⟨1, -(a + c) / b⟩) hab hf
      (complete_pt ⟨by show AlgConstrNum 0; exact AlgConstrNum.zero, by show AlgConstrNum (-c / b); is_oc⟩)
      (complete_pt ⟨by show AlgConstrNum 1; exact AlgConstrNum.one, by show AlgConstrNum (-(a + c) / b); is_oc⟩)
      (fun h => by have := congrArg Complex.re h; simp at this)
      ?_ ?_
      <;> {to_re_im; field_simp; ring}

theorem GeoConstrPt_iff (z : ℂ) : GeoConstrPt z ↔ AlgConstrNum z.re ∧ AlgConstrNum z.im :=
  ⟨sound_pt, complete_pt⟩

theorem GeoConstrLine_iff (f : Line) : GeoConstrLine f ↔ AlgConstrLine f :=
  ⟨sound_line, complete_line⟩

theorem trisect_cos {θ : ℝ} (h : AlgConstrNum (Real.cos θ)) : AlgConstrNum (Real.cos (θ / 3)) := by
  have h3 := Real.cos_three_mul (θ / 3)
  have : 3 * (θ / 3) = θ := by linarith
  rw [this] at h3
  refine AlgConstrNum.cubic (a := 0) (b := -3 / 4) (c := -Real.cos θ / 4)
    AlgConstrNum.zero (by is_oc) (by is_oc) ?_
  linear_combination (-1 / 4) * h3

end Origami

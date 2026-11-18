import Origami.Basic

section
open Lean Elab Tactic

elab "line_facts" : tactic => withMainContext do
  for ldecl in (← getLCtx) do
    if ldecl.isImplementationDetail then continue
    let ty ← Lean.instantiateMVars ldecl.type
    if ty.isConstOf ``Origami.Line then
      let x := mkIdent ldecl.userName
      let n1 := mkIdent (ldecl.userName.appendAfter "_hd")
      let n2 := mkIdent (ldecl.userName.appendAfter "_hc")
      let n3 := mkIdent (ldecl.userName.appendAfter "_pos")
      let n4 := mkIdent (ldecl.userName.appendAfter "_nsq")
      let n5 := mkIdent (ldecl.userName.appendAfter "_ri")
      evalTactic (← `(tactic| have $n1 : ($x).d ≠ 0 := ($x).hd))
      evalTactic (← `(tactic| have $n2 : (starRingEnd ℂ) ($x).d ≠ 0 :=
        (map_ne_zero _).2 ($x).hd))
      evalTactic (← `(tactic| have $n3 : 0 < Complex.normSq ($x).d :=
        Complex.normSq_pos.2 ($x).hd))
      evalTactic (← `(tactic| have $n4 : ($x).d.re * ($x).d.re + ($x).d.im * ($x).d.im ≠ 0 := by
        have h := Complex.normSq_pos.2 ($x).hd
        rw [Complex.normSq_apply] at h
        exact h.ne'))
      evalTactic (← `(tactic| have $n5 := Origami.Line.d_re_or_im $x))
end

syntax "conj_simp" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| conj_simp $[$loc:location]?) =>
    `(tactic| simp only [map_mul, map_div₀, map_add, map_sub, map_neg, map_one, map_zero,
      Complex.conj_conj]
      $[$loc:location]?)

syntax "line_unfold" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| line_unfold $[$loc:location]?) =>
    `(tactic| simp only [Origami.Line.mem_def, Origami.Line.Par, Origami.Line.Perp,
      Origami.Line.Same, Origami.Line.reflect, Origami.Line.reflectLine]
      $[$loc:location]?)

syntax "to_re_im" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| to_re_im $[$loc:location]?) =>
    `(tactic| simp only [Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.div_re, Complex.div_im,
      Complex.normSq_apply, Complex.one_re, Complex.one_im, Complex.zero_re,
      Complex.zero_im]
      $[$loc:location]?)

syntax "line_arith" (" [" term,* "]")? : tactic
macro_rules
  | `(tactic| line_arith) =>
    `(tactic| first | ring | ring_nf | linarith | nlinarith)
  | `(tactic| line_arith [$ts,*]) =>
    `(tactic| first | ring | ring_nf | linarith | nlinarith [$ts,*])

macro "line_auto" : tactic =>
  `(tactic| first
    | (line_facts; line_unfold; conj_simp; field_simp; ring)
    | (line_facts; line_unfold; to_re_im; field_simp; line_arith)
    | (line_facts; line_unfold; to_re_im; constructor <;> intros <;> field_simp <;> line_arith))

syntax "cancel_comp " term : tactic
macro_rules
  | `(tactic| cancel_comp $h) =>
    `(tactic| (have hc := $h; rcases hc with h' | h' <;> (apply mul_left_cancel₀ h' <;> first | grind | nlinarith)))

macro "cancel_dir " l:ident : tactic =>
  `(tactic| cancel_comp (Origami.Line.d_re_or_im $l))

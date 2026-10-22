import mathLib

inductive Arith : Type where
  | add : Arith → Arith → Arith -- e + f
  | mul : Arith → Arith → Arith -- e * f
  | nat : Nat → Arith           -- constant
  | var : String → Arith        -- variable

declare_syntax_cat arith
syntax num                        : arith -- nat for Arith.nat
syntax str                        : arith -- strings for Arith.var
syntax:50 arith:50 " + " arith:51 : arith -- Arith.add
syntax:60 arith:60 " * " arith:61 : arith -- Arith.mul
syntax " ( " arith " ) "          : arith -- bracketed expressions

-- Auxiliary notation for translating `arith` into `term`
syntax " ⟪ " arith " ⟫ " : term

-- Our macro rules perform the "obvious" translation:
macro_rules
  | `(⟪ $s:str ⟫)              => `(Arith.var $s)
  | `(⟪ $num:num ⟫)            => `(Arith.nat $num)
  | `(⟪ $x:arith + $y:arith ⟫) => `(Arith.add ⟪ $x ⟫ ⟪ $y ⟫)
  | `(⟪ $x:arith * $y:arith ⟫) => `(Arith.mul ⟪ $x ⟫ ⟪ $y ⟫)
  | `(⟪ ( $x ) ⟫)              => `( ⟪ $x ⟫ )

set_option pp.fieldNotation false

/- info: Arith.mul (Arith.var "x") (Arith.var "y") : Arith -/
#check ⟪ "x" * "y" ⟫

/- info: Arith.add (Arith.var "x") (Arith.var "y") : Arith -/
#check ⟪ "x" + "y" ⟫

/- info: Arith.add (Arith.var "x") (Arith.nat 20) : Arith -/
#check ⟪ "x" + 20 ⟫

/- info: Arith.add (Arith.var "x") (Arith.mul (Arith.var "y") (Arith.var "z")) : Arith -/
#check ⟪ "x" + "y" * "z" ⟫ -- precedence

/- info: Arith.add (Arith.mul (Arith.var "x") (Arith.var "y")) (Arith.var "z") : Arith -/
#check ⟪ "x" * "y" + "z" ⟫ -- precedence

/- info: Arith.mul (Arith.add (Arith.var "x") (Arith.var "y")) (Arith.var "z") : Arith -/
#check ⟪ ("x" + "y") * "z" ⟫ -- brackets

#check []

open Lean Elab Command

syntax (name := xxx) "red" : command
syntax (name := yyy) "green" : command
syntax (name := zzz) "blue" : command

@[macro xxx] def redMacro : Macro := λ stx =>
  match stx with
  | _ => `(green)

@[macro yyy] def greenMacro : Macro := λ stx =>
  match stx with
  | _ => `(blue)

@[command_elab zzz] def blueElab : CommandElab := λ _stx =>
  Lean.logInfo "finally, blue!"

/- info: finally, blue! -/
red

open Lean Meta Elab Tactic Term in
elab "suppose " n:ident " : " t:term : tactic => do
  let n : Name := n.getId
  let mvarId ← getMainGoal
  mvarId.withContext do
    let t ← elabType t
    let p ← mkFreshExprMVar t MetavarKind.syntheticOpaque n
    let (_, mvarIdNew) ← MVarId.intro1P $ ← mvarId.assert n t p
    replaceMainGoal [p.mvarId!, mvarIdNew]
  evalTactic $ ← `(tactic|rotate_left)

example : 0 + a = a := by
  suppose add_comm : 0 + a = a + 0
  focus
    -- closes the initial main goal
    rw [add_comm]; rfl
  case add_comm =>
    -- proves `add_comm`
    rw [Nat.zero_add]; rfl

#check Lean.Parser.Category.term
#check Lean.Parser.ident
#check Expr.app (Expr.bvar 2)
#check Expr.bindingName!
#check Expr
#check Expr.app1?
#check Expr.app2?
#check Expr.app3?
#check List.map

def one : Expr := mkNatLit 1
def two : Expr := mkNatLit 2

-- Exercise 1: nested Expr.app
def onePlusTwo₁ : Expr :=
  Expr.app (Expr.app (Expr.const ``Nat.add []) one) two

-- Exercise 2: mkAppN
def onePlusTwo₂ : Expr :=
  mkAppN (Expr.const ``Nat.add []) #[one, two]

def onePlusTwo₃ : Expr :=
  mkNatAdd one two

#eval onePlusTwo₁ == onePlusTwo₂  -- true
#eval onePlusTwo₁

#check Expr.const ``Nat.add
#check `abc.xyz
#check Expr.const `Nat.add
#eval onePlusTwo₂
#eval onePlusTwo₃
#check Name

open Lean Meta Elab Tactic Term

structure Point where
  x : Nat
  y : Nat

#print Point

instance : ToMessageData Point where
  toMessageData p :=
    m!"Point ({p.x}, {p.y})"

def showPoint : MetaM Unit := do
  let p : Point := {x := 3, y := 5}
  logInfo m!"Current Point: {p}"

#check MetaM Unit

elab "#requireProp" t:term : command => do
  Command.liftTermElabM do
    let tExpr ← Term.elabTerm t none
    unless ← isProp tExpr do
      throwError m!"Goal must be a proposition: {tExpr}"
    logInfo m!"The expression of the term: {tExpr}"

def egCommand : Lean.CoreM Lean.Syntax.Command := do
  `(command| example := "Hello World")

def egCommand' : Lean.CoreM Lean.Syntax:= do
  `(command| example := "Hello World")

def egCommand'' : Lean.CoreM (Lean.TSyntax `command) := do
  `(command| example := "Hello World")

#check egCommand
#check egCommand'
#check egCommand''

def sumTerm (a b : Nat) : CoreM Syntax.Term := do
  let aLit := Syntax.mkNatLit a
  let bLit := Syntax.mkNatLit b
  `($aLit + $bLit)

-- dollar is needed to call literals.

#print sumTerm
#check CoreM Term
#check sumTerm 3 4
def a := Syntax.mkNatLit 3
def b := Syntax.mkNatLit 4
#check `($a + $b)

def flipSum : Lean.Syntax.Term → CoreM Lean.Syntax.Term
| `($a +  $b) => `($b + $a)
| stx => return stx

def test : CoreM Syntax.Term := do
  let stx ← sumTerm 1 2
  flipSum stx

#eval (sumTerm 1 2) >>= flipSum
#eval sumTerm 1 2

def checkFlipSum (a b : Nat) : CoreM Format := do
  let stx ← flipSum (← (sumTerm a b))
  PrettyPrinter.ppTerm stx

#check flipSum

#print Syntax
#check Syntax.node
#check Syntax.atom
#check Syntax.ident

def mySyntax : Syntax :=
  Syntax.node SourceInfo.none `a #[Syntax.atom SourceInfo.none "+"]

#print Syntax.Term  -- @[reducible] def Lean.Syntax.Term : Type :=
                    -- TSyntax `term

#print TSyntax
/-
structure Lean.TSyntax (ks : SyntaxNodeKinds) : Type where
  Lean.TSyntax.raw : Syntax

constructor: Lean.TSyntax.mk {ks : SyntaxNodeKinds} (raw : Syntax) : TSyntax ks
-/

-- writing SyntaxNodeKind is definitionally equivalent to writing Name
#print SyntaxNodeKind
-- @[reducible] def Lean.SyntaxNodeKind : Type := Name

#print Name
/-
inductive Lean.Name : Type where
  | Lean.Name.anonymous : Name
  | Lean.Name.str : Name → String → Name
  | Lean.Name.num : Name → ℕ → Name
-/

#eval Name.str `a "hi"

#print CoreM
-- @[reducible] def Lean.Core.CoreM : Type → Type :=
-- ReaderT Core.Context (StateRefT' IO.RealWorld Core.State (EIO Exception))

#print ReaderT
-- @[implicit_reducible] def ReaderT.{u, v} :
--      Type u → (Type u → Type v) → Type u → Type (max u v) :=
--    fun ρ m α => ρ → m α

def nth {α : Type} : List α → Nat → Option α
  | [], _           => Option.none
  | x :: _, 0       => Option.some x
  | _ :: xs, n + 1  => nth xs n

def connect {α : Type} {β : Type} :
  Option α → (α → Option β) → Option β
  | Option.none, _    => Option.none
  | Option.some a, f  => f a

def sum257Connect (ns : List Nat) : Option Nat :=
  connect (nth ns 1)
  (fun n2 => connect (nth ns 4)
    (fun n5 => connect (nth ns 6)
      (fun n7 => Option.some (n2 + n5 + n7))
    )
  )

#eval Option.some 6


def double (n : Nat) : Nat :=
  2 * n

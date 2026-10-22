import Mathlib

inductive BinTree : Type where
| null
| node (l r : BinTree)

def size (T : BinTree) :=
match T with
| .null => 0
| .node l r => 1 + size l + size r

def depth (T : BinTree) :=
match T with
| .null => 0
| .node l r => 1 + max (depth l) (depth r)

inductive isFull : BinTree ->  Prop where
| empty : isFull BinTree.null
| Nonempty (hl : isFull l) (hr : isFull r) : isFull (.node l r)

def my_flip (T : BinTree) :=
match T with
| .null => BinTree.null
| .node l r => .node (my_flip r) (my_flip l)

theorem flip_eq {T : BinTree}:
  my_flip (my_flip T) = T := by

  induction T with
  | null => rfl
  | node l r lh rh => simp [my_flip]
                      exact ⟨lh, rh⟩

theorem flip_size {T : BinTree}:
  size (my_flip T) = size T := by
  induction T with
  | null => rfl
  | node l r lih rih =>
    unfold my_flip size
    rw [lih, rih]
    ac_rfl

def leaf_count [BEq BinTree] (T : BinTree) : Nat :=
match T with
| .null => 0
| .node l r => if (l == .null ∧ r == .null) then 1 else (leaf_count l + leaf_count r)

def is_perfect (T : BinTree) : Bool :=
match T with
| .null => True
| .node l r => is_perfect l ∧ is_perfect r ∧ (depth l == depth r)

theorem perfect_size {T : BinTree}:
  is_perfect T → size T = 2^depth T - 1 := by
  intro h
  induction T with
  | null => simp [size, depth]
  | node l r lih rih =>
    obtain ⟨hl, hr, hd⟩ := of_decide_eq_true h
    simp [hl, hr] at lih rih hd
    rw [size, depth, lih, rih, hd];
    grind

inductive BinTree' (α : Type) : Type where
| leaf (v : α)
| sing (v : α) (c : BinTree' α)
| node (l : BinTree' α) (v : α) (r : BinTree' α)

def val_root (T : BinTree' Nat) : Nat :=
match T with
| .leaf v => v
| .sing v _ => v
| .node _ v _ => v

def max_val (T : BinTree' Nat) : Nat :=
match T with
| .leaf v => v
| .sing v c => max v (max_val c)
| .node l v r => max (max (max_val l) v) (max_val r)

def min_val (T : BinTree' Nat) : Nat :=
match T with
| .leaf v => v
| .sing v c => min v (min_val c)
| .node l v r => min (min (min_val l) v) (min_val r)

def is_BST (T : BinTree' Nat) : Bool :=
match T with
| .leaf _ => True
| .sing _ _ => True
| .node l v r => is_BST l ∧ is_BST r ∧ max_val l < v ∧ v < min_val r

def count_nodes_with_height (h : Nat) (T : BinTree) :=
match T with
| .null => 0
| .node l r => count_nodes_with_height h l + count_nodes_with_height h r + (if depth T = h then 1 else 0)

-- theorem nodes_at_height {T : BinTree} {hgt : Nat}:
--   is_perfect T → count_nodes_with_height

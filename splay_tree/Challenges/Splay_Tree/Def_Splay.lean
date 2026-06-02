import Mathlib.Data.Real.Basic

inductive BinaryTree where
| empty
| node (left : BinaryTree) (key : ℕ) (right : BinaryTree)
deriving Repr, BEq

def BinaryTree.num_nodes : BinaryTree → ℕ
| .empty => 0
| .node left _ right => 1 + (num_nodes left) + (num_nodes right)


def rotateRight : BinaryTree → BinaryTree
  | .node (.node a x b) y c => .node a x (.node b y c)
  | t => t

def rotateLeft : BinaryTree → BinaryTree
  | .node a x (.node b y c) => .node (.node a x b) y c
  | t => t

inductive Rot
  | zigZig | zigZag | zagZag | zagZig | zig | zag

def rotate (s : BinaryTree) (rt : Rot) : BinaryTree :=
  match rt with
  | .zigZig => rotateRight (rotateRight s) -- Explicitly two steps
  | .zigZag =>
      match s with
      | .node l k r => rotateRight (.node (rotateLeft l) k r)
      | _ => s
  | .zagZag => rotateLeft (rotateLeft s)   -- Explicitly two steps
  | .zagZig =>
      match s with
      | .node l k r => rotateLeft (.node l k (rotateRight r))
      | _ => s
  | .zig => rotateRight s
  | .zag => rotateLeft s

-- 3. SPLAY IMPLEMENTATION
-- Note the checks for .empty on grandchildren to decide between ZigZig vs Zig.

def BinaryTree.search_path_len (t : BinaryTree) (q : ℕ) : ℕ :=
  match t with
  | .empty => 0
  | .node left key right =>
    if q < key then
      1 + left.search_path_len q
    else if key < q then
      1 + right.search_path_len q
    else
      1

def splay (t : BinaryTree) (q : ℕ) : BinaryTree :=
  match t with
  | .empty => .empty
  | .node l k r =>
    if q = k then
      t
    else if q < k then
      match l with
      | .empty => t -- q not found, current root is closest
      | .node ll lk lr =>
        if q < lk then
          match ll with
          | .empty => rotate (.node l k r) .zig -- Grandchild empty? Just Zig.
          | _ =>
              -- Zig-Zig: Recurse, then double rotate
              let t' := .node (splay ll q) lk lr
              rotate (.node t' k r) .zigZig
        else if lk < q then
          match lr with
          | .empty => rotate (.node l k r) .zig -- Grandchild empty? Just Zig.
          | _ =>
              -- Zig-Zag: Recurse, then double rotate
              let t' := .node ll lk (splay lr q)
              rotate (.node t' k r) .zigZag
        else
          -- Target found at child (lk == q)
          rotate t .zig
    else -- q > k (Symmetric case)
      match r with
      | .empty => t
      | .node rl rk rr =>
        if q < rk then
          match rl with
          | .empty => rotate (.node l k r) .zag -- Grandchild empty? Just Zag.
          | _ =>
              -- Zag-Zig
              let t' := .node (splay rl q) rk rr
              rotate (.node l k t') .zagZig
        else if rk < q then
          match rr with
          | .empty => rotate (.node l k r) .zag -- Grandchild empty? Just Zag.
          | _ =>
              -- Zag-Zag
              let t' := .node rl rk (splay rr q)
              rotate (.node l k t') .zagZag
        else
          -- Target found at child (rk == q)
          rotate t .zag

def splay.cost (t : BinaryTree) (q : ℕ) : ℝ :=
  match t with
  | .empty => 0
  | .node l k r =>
    if q = k then 0
    else if q < k then
      match l with
      | .empty => 0
      | .node ll lk lr =>
        if q < lk then
          match ll with
          | .empty => 1                 -- Zig (Grandchild empty)
          | _ => (splay.cost ll q) + 2  -- Zig-Zig
        else if lk < q then
          match lr with
          | .empty => 1                 -- Zig (Grandchild empty)
          | _ => (splay.cost lr q) + 2  -- Zig-Zag
        else 1                          -- Zig (Found at child)
    else -- q > k
      match r with
      | .empty => 0
      | .node rl rk rr =>
        if q < rk then
          match rl with
          | .empty => 1                 -- Zag (Grandchild empty)
          | _ => (splay.cost rl q) + 2  -- Zag-Zig
        else if rk < q then
          match rr with
          | .empty => 1                 -- Zag (Grandchild empty)
          | _ => (splay.cost rr q) + 2  -- Zag-Zag
        else 1                          -- Zag (Found at child)

inductive ForallTree (p : Nat → Prop) : BinaryTree → Prop
  | left : ForallTree p .empty
  | node left key right :
     ForallTree p left →
     p key  →
     ForallTree p right →
     ForallTree p (.node left key  right)

inductive IsBST : BinaryTree → Prop
  | left : IsBST .empty
  | node key left right:
     ForallTree (fun k  => k < key) left →
     ForallTree (fun k  => key < k) right →
     IsBST left → IsBST right →
     IsBST (.node left key right)

def splay.sequence_cost {n : ℕ}
  (init : BinaryTree) (X : Fin n → ℕ) : ℝ :=
  ((List.finRange n).foldl (fun (acc : BinaryTree × ℝ) i =>
    let (t, c) := acc
    (splay t (X i), c + splay.cost t (X i)))
  (init, 0)).2

def BinaryTree.toKeyList (t : BinaryTree) : List Nat :=
  match t with
  | .empty => []
  | .node left key right => left.toKeyList ++ [key] ++ right.toKeyList

### Compilation Command
```
dafny BinarySearchTree.dfy
dafny run BinarySearchTree.dfy
dafny test BinarySearchTree.dfy
```
- I am using Dafny version 4.3.0

### Data Type Definition:
```
datatype Tree = Empty | Node(key: int, left: Tree, right: Tree, exist: bool)
```
- Defines a binary tree data type with two constructors: `Empty` for an empty tree and `Node` for a node with an integer key, left and right subtrees, and a boolean flag `exist` indicating whether the node has been "deleted."

### Function: max
```
function max(x: int, y: int): (r: int)
  ensures r >= x && r >= y
  ensures x > y ==> r == x
  ensures y > x ==> r == y
  ensures x == y ==> r == x == y
{
  if x > y then x else y
}
```
- Returns the maximum value between two integers (`x` and `y`).
- Specifies postconditions ensuring that the result is greater than or equal to both input values.
- Only done for testing and learning purpose

### Function: size
```
function size(t: Tree): (s: nat)
{
  match t
  case Empty => 0
  case Node(_, l, r, _) => size(l) + size(r) + 1
}
```
- Calculates the size (number of nodes) of a tree, including nodes marked as deleted (`exist: false`).

### Function: real_size
```
function real_size(t: Tree) : (s: nat)
  ensures s >= 0
{
  match t
  case Empty => 0
  case Node(_, l, r, e) =>
    if e then real_size(l) + real_size(r) + 1
    else real_size(l) + real_size(r)
}
```
- Calculates the real size of a tree, excluding nodes marked as deleted.

### Function: tree_elements
```
function tree_elements(t: Tree): (s: set<int>)
  ensures t == Empty <==> s == {}
  ensures t != Empty ==> ...
{
  match t
  case Empty => {}
  case Node(k, l, r, _) => tree_elements(l) + {k} + tree_elements(r)
}
```
- Collects all keys in a tree, including keys of nodes marked as deleted.
- Specifies postconditions ensuring correctness and ordering of keys.

### Function: real_tree_elements
```
function real_tree_elements(t: Tree): (s: set<int>)
  ensures t == Empty ==> s == {}
  ensures t != Empty ==> ...
  ensures s <= tree_elements(t)
{
  match t
  case Empty => {}
  case Node(k, l, r, e) => ...
}
```
- Collects all keys in a tree without lazy-deleted keys.
- Specifies postconditions ensuring correctness, ordering, and subset relationships.

### Function: tree_nodes
```dafny
function tree_nodes(t: Tree): (s: set<Tree>)
  ensures BST(t) ==> forall n :: n in s ==> BST(n)
  ensures Empty !in s
{
  match t
  case Empty => {}
  case Node(_, l, r, _) => tree_nodes(l) + {t} + tree_nodes(r)
}
```
- Collects all nodes in a tree.
- Specifies postconditions ensuring that nodes form a valid binary search tree.

### Predicate: BST
```dafny
predicate BST(t: Tree)
{
  match t
  case Empty => true
  case Node(k, l, r, _) => BST(l) && BST(r) && ...
}
```
- A predicate specifying the binary search tree property.
- Specifies postconditions ensuring that left subtree keys are less than the node's key, and right subtree keys are greater.
### Predicate: search
```dafny
predicate search(t: Tree, x: int)
  requires BST(t)
  ensures search(t, x) == true <==> x in real_tree_elements(t)
{
  match t
  case Empty => false
  case Node(k, l, r, e) => ...
}
```
- A predicate representing a search operation in a binary search tree.
- Specifies postconditions ensuring correctness of the search result.

### Function: insert_key
```dafny
ghost function insert_key(t: Tree, x: int) : (t': Tree)
  requires BST(t)
  ensures BST(t')
  ensures tree_elements(t') == tree_elements(t) + {x}
  ensures real_tree_elements(t') == real_tree_elements(t) + {x}
{
  match t
  case Empty => ...
  case Node(k, l, r, e) => ...
}
```
- A ghost function representing the recursive insertion of a key into a binary search tree.
- Specifies postconditions ensuring the resulting tree is a valid BST and element sets are correctly updated.

### Function: delete_key
```dafny
function delete_key(t: Tree, x: int) : (t': Tree)
  requires BST(t)
  ensures BST(t')
  ensures tree_elements(t) == tree_elements(t')
  ensures search(t, x) <==> real_tree_elements(t) == real_tree_elements(t') + {x}
  ensures real_tree_elements(t) - {x} == real_tree_elements(t')
  ensures x !in real_tree_elements(t')
{
  match t
  case Empty => Empty
  case Node(k, l, r, e) => ...
}
```
- Function representing the lazy-deletion of key `x` in a binary search tree.
- Specifies postconditions ensuring the resulting tree is a valid BST and element sets are correctly updated.

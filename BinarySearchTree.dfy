//Defining the Tree Structure
datatype Tree = Empty | Node(key: int, left: Tree, right: Tree, exist: bool)


//  Return the maximal value between two integer values x and y
// Only addec while testing and learning
function max(x: int, y: int): (r: int)
  ensures r >= x && r >= y
  ensures x > y ==> r == x
  ensures y > x ==> r == y
  ensures x == y ==> r == x == y
{
  if x > y then x else y
}


// Counting the size of the tree, this also includes the lazy-deleted nodes
function size(t: Tree): (s: nat)
{
  match t
  case Empty => 0
  case Node(_, l, r, _) => size(l) + size(r) + 1
}


//Count the real size of a tree, not including lazy-deleted nodes
function real_size(t: Tree) : (s: nat)
  ensures s >= 0
{
  match t
  case Empty => 0
  case Node(_, l, r, e) =>
    if e then real_size(l) + real_size(r) + 1
    else real_size(l) + real_size(r)
}


// Stores all the elements present in the tree in a new set, these elements also include the lazy-deleted nodes
function tree_elements(t: Tree): (s: set<int>)
  ensures t == Empty <==> s == {}
  ensures t != Empty ==> (forall k :: (k in tree_elements(t.left) ==> k in s) &&
                                      (k in tree_elements(t.right) ==> k in s)
                                      && t.key in s)
  ensures t != Empty ==> ( forall k :: k in s ==> (k in tree_elements(t.left))
                                                  || (k in tree_elements(t.right))
                                                  || t.key == k)
  ensures t != Empty ==>  tree_elements(t.left) <= s
                          && tree_elements(t.right) <= s
{
  match t
  case Empty => {}
  case Node(k, l, r, _) => tree_elements(l) + {k} + tree_elements(r)
}

// Stores all the elements present in the tree in a new set, these elements do not include the lazy-deleted nodes
function real_tree_elements(t: Tree): (s: set<int>)
  ensures t == Empty ==> s == {}
  ensures t != Empty ==> (forall k :: (k in real_tree_elements(t.left) ==> k in s) &&
                                      (k in real_tree_elements(t.right) ==> k in s)
                                      && (t.exist ==> t.key in s))
  ensures t != Empty ==> ( forall k :: k in s ==> (k in real_tree_elements(t.left))
                                                  || (k in real_tree_elements(t.right))
                                                  || (t.exist && t.key == k))
  ensures t != Empty ==>  real_tree_elements(t.left) <= s
                          && real_tree_elements(t.right) <= s
  ensures s <= tree_elements(t)
{
  match t
  case Empty => {}
  case Node(k, l, r, e) =>
    assert real_tree_elements(l) <= tree_elements(l);
    assert real_tree_elements(r) <= tree_elements(r);
    if e then real_tree_elements(l) + {k} + real_tree_elements(r)
    else real_tree_elements(l) + real_tree_elements(r)
}


// Collect all the nodes in a tree
function tree_nodes(t: Tree): (s: set<Tree>)
  ensures BST(t) ==> forall n :: n in s ==> BST(n)
  ensures Empty !in s
{
  match t
  case Empty => {}
  case Node(_, l, r, _) => tree_nodes(l) + {t} + tree_nodes(r)
}

// The definition of BST which will be checked everywhere
predicate BST(t: Tree)
{
  match t
  case Empty => true
  case Node(k, l, r, _) => BST(l) && BST(r) && (forall e :: e in tree_elements(l) ==> e < k) && (forall e :: e in tree_elements(r) ==> e > k)
}


// Searches for a node in the tree
predicate search(t: Tree, x: int)
  requires BST(t)
  ensures search(t, x) == true <==> x in real_tree_elements(t)
{
  match t
  case Empty => false
  case Node(k, l, r, e) =>
    if k == x then e
    else if x < k then search(l, x)
    else search(r, x)
}

// Inserts a new key in the tree
function insert_key(t: Tree, x: int) : (t': Tree)
  requires BST(t)
  ensures BST(t')
  ensures tree_elements(t') == tree_elements(t) + {x}
  ensures real_tree_elements(t') == real_tree_elements(t) + {x}
{
  match t
  case Empty =>
    assert BST(Node(x, Empty, Empty, true));
    assert tree_elements(t) == {};
    assert tree_elements(Node(x, Empty, Empty, true)) == tree_elements(t) + {x};
    assert real_tree_elements(t) == {};
    assert real_tree_elements(Node(x, Empty, Empty, true)) == real_tree_elements(t) + {x};
    Node(x, Empty, Empty, true)
  case Node(k, l, r, e) =>
    if x < k then
      assert BST(l);
      assert BST(insert_key(l, x));
      assert BST(Node(k, insert_key(l, x), r, e));
      Node(k, insert_key(l, x), r, e)
    else if x > k then
      assert BST(r);
      assert BST(insert_key(r, x));
      assert BST(Node(k, l, insert_key(r, x), e));
      Node(k, l, insert_key(r, x), e)
    else
      assert BST(t);
      assert BST(Node(k, l, r, true));
      assert tree_elements(t) == tree_elements(t) + {x};
      assert e ==> real_tree_elements(t) == real_tree_elements(t) + {x};
      assert !e ==> real_tree_elements(Node(k, l, r, true)) == real_tree_elements(t) + {x};
      if e then t
      else
        Node(k, l, r, true)
}


// Deletes the key from the tree, performs lazy deletion in such a case
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
  case Node(k, l, r, e) =>
    if k == x then Node(k, l, r, false)
    else if x < k then Node(k, delete_key(l, x), r, e)
    else Node(k, l, delete_key(r, x), e)
}

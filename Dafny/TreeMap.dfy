module Util {

  datatype Option<T> = Some(v:T) | None

  function unionMap<U(!new), V>(m: map<U,V>, m': map<U,V>): map<U,V>
    requires m !! m'; // disjoint
    ensures forall i :: i in unionMap(m, m') <==> i in m || i in m';
    ensures forall i :: i in m ==> unionMap(m, m')[i] == m[i];
    ensures forall i :: i in m' ==> unionMap(m, m')[i] == m'[i];
  {
    map i | i in (domainMap(m) + domainMap(m')) :: if i in m then m[i] else m'[i]
  }

  function domainMap<U(!new),V>(m: map<U,V>) : set<U>
    ensures domainMap(m) == set u : U | u in m :: u;
    ensures forall u :: u in domainMap(m) <==> u in m;
    ensures (map i | i in domainMap(m) :: m[i]) == m;
  {
    set u : U | u in m :: u
  }

  function removeMap<U,V>(m: map<U, V>, e: U) : map<U, V>
    ensures e !in removeMap(m, e);
    ensures domainMap(m) - {e} == domainMap(removeMap(m, e));
    ensures removeMap(m, e) == map i | i in m && i != e :: m[i];
    ensures e in m ==> |domainMap(m)| == |domainMap(removeMap(m, e))| + 1;
    ensures e !in m ==> |domainMap(m)| == |domainMap(removeMap(m, e))|;
    ensures forall u :: u in m && u != e ==> u in removeMap(m, e);
  {
    map i | i in m && i != e :: m[i]
  }

  function removeMapSet<U,V>(m: map<U, V>, s: set<U>) : map<U, V>
    ensures forall e :: e in s ==> e !in removeMapSet(m, s);
    ensures domainMap(m) - s == domainMap(removeMapSet(m, s));
    ensures removeMapSet(m, s) == map i | i in m && i !in s :: m[i];
    ensures forall u :: u in m && u !in s ==> u in removeMapSet(m, s);
  {
    map i | i in m && i !in s :: m[i]
  }

  lemma non_empty_map_has_elements<S,T>(m:map<S,T>)
    requires |m| > 0;
    ensures exists x :: x in m;
  {
    var dom := domainMap(m);
    assert m !! map [];
    assert m != map [];
    assert |dom| > 0;
  }

  lemma mapSizeIsDomainSize<S,T>(dom:set<S>, m:map<S,T>)
    requires dom == domainMap(m);
    ensures |m| == |dom|;
  {
    if |m| == 0 {
        assert |dom| == 0;
    } else {
        non_empty_map_has_elements(m);
        var x :| x in m;
        assert x in m;
        assert x in dom;
        var m' := map y | y in m && y != x :: m[y];
        var dom' := dom - { x };
        mapSizeIsDomainSize(dom', m');
        assert |dom'| == |m'|;
        assert |dom| == |dom'| + 1;
        assert m == m'[x := m[x]];
        assert |m| == |m'| + 1;
    }
  }

  lemma disjointUnionDomainMapSize<U,V>(m:map<U,V>, m':map<U,V>)
    requires m !! m';
    ensures |domainMap(unionMap(m, m'))| == |domainMap(m)| + |domainMap(m')|;
  {
    if |m| == 0 {
      assert unionMap(m, m') == m';
    } else {
      non_empty_map_has_elements(m);
      var x :| x in m;
      assert x in m;
      assert x !in m';
      assert x in domainMap(m);
      assert x !in domainMap(m');
      var m0 := removeMap(m, x);
      assert domainMap(m0) == domainMap(m) - {x};
      assert domainMap(unionMap(m0, m')) == domainMap(unionMap(m, m')) - {x};
      disjointUnionDomainMapSize(m0, m');
    }
  }

  lemma disjointUnionMapSize<U,V>(m:map<U,V>, m':map<U,V>)
    requires m !! m';
    ensures |unionMap(m, m')| == |m| + |m'|;
  {
    disjointUnionDomainMapSize(m, m');
    mapSizeIsDomainSize(domainMap(unionMap(m, m')), unionMap(m, m'));
    mapSizeIsDomainSize(domainMap(m), m);
    mapSizeIsDomainSize(domainMap(m'), m');
  }

}

abstract module TotalOrder {
  type T(!new, ==)

  predicate method Leq(a: T, b: T)

  lemma Antisymmetry(a: T, b: T)
    requires Leq(a, b) && Leq(b, a)
    ensures a == b

  lemma Transitivity(a: T, b: T, c: T)
    requires Leq(a, b) && Leq(b, c)
    ensures Leq(a, c)

  lemma Totality(a: T, b: T)
    ensures Leq(a, b) || Leq(b, a)
}

abstract module Map {
  import opened Util
  import O : TotalOrder

  class TreeNode<V> {

    var key: O.T;
    var value: V;
    var left: TreeNode?<V>;
    var right: TreeNode?<V>;

    ghost var kvmap: map<O.T, V>;
    ghost var Repr: set<object>;

    predicate Valid()
      reads this, Repr;
    {
      this in Repr &&
        (left != null ==> left in Repr && left.Repr <= Repr && this !in left.Repr && left.Valid() &&
        forall y :: y in left.kvmap ==> y != key && O.Leq(y, key)) &&
        (right != null ==> right in Repr && right.Repr <= Repr && this !in right.Repr && right.Valid() &&
        forall y :: y in right.kvmap ==> y != key && O.Leq(key, y)) &&
        (left == null && right == null ==> kvmap == map[key := value]) &&
        (left != null && right == null ==> kvmap == left.kvmap[key := value]) &&
        (left == null && right != null ==> kvmap == right.kvmap[key := value]) &&
        (left != null && right != null ==> left.Repr !! right.Repr && right.kvmap !! left.kvmap &&
        kvmap == unionMap(left.kvmap, right.kvmap)[key := value])
    }

    constructor(k: O.T, v: V)
      ensures Valid() && fresh(Repr);
      ensures kvmap == map[k := v];
    {
      key := k;
      value := v;
      left := null;
      right := null;
      kvmap := map[key := value];
      Repr := {this};
    }

    static method GetValue(node: TreeNode<V>, k: O.T) returns (value: V)
      requires node.Valid();
      requires k in node.kvmap;
      ensures value == node.kvmap[k];
      decreases node.Repr;
    {
      if (k == node.key) {
        value := node.value;
      } else if node.left != null && O.Leq(k, node.key) && node.right == null {
        value := GetValue(node.left, k);
      } else if node.left != null && O.Leq(k, node.key) {
        forall y | y in node.right.kvmap
          ensures k != y;
        {
          if k == y {
            O.Transitivity(k, node.key, y);
            O.Antisymmetry(k, node.key);
          }
        }
        value := GetValue(node.left, k);
      } else if node.right != null && O.Leq(node.key, k) {
        value := GetValue(node.right, k);
      }
    }

    static method TryGetValue(node: TreeNode?<V>, k: O.T) returns (vo:Option<V>)
      requires node != null ==> node.Valid();
      ensures node != null ==> (vo != None <==> k in node.kvmap);
      ensures node == null ==> vo == None;
      ensures vo != None ==> node != null && vo == Some(node.kvmap[k]);
      decreases if node != null then node.Repr else {};
    {
      if node != null && k == node.key {
        vo := Some(node.value);
      } else if node != null && node.left != null && O.Leq(k, node.key) && node.right == null {
        vo := TryGetValue(node.left, k);
      } else if node != null && node.left != null && O.Leq(k, node.key) {
        forall y | y in node.right.kvmap
          ensures k != y;
        {
          if k == y {
            O.Transitivity(k, node.key, y);
            O.Antisymmetry(k, node.key);
          }
        }
        vo := TryGetValue(node.left, k);
      } else if node != null && node.right != null && O.Leq(node.key, k) {
        vo := TryGetValue(node.right, k);
      } else {
        vo := None;
      }
    }

    static method ContainsKey(node: TreeNode<V>, k: O.T) returns (contains: bool)
      requires node.Valid();
      ensures contains <==> k in node.kvmap;
      decreases node.Repr;
    {
      contains := false;
      if (k == node.key) {
        contains := true;
      } else if node.left != null && O.Leq(k, node.key) && node.right == null {
        contains := ContainsKey(node.left, k);
      } else if node.left != null && O.Leq(k, node.key) {
        forall y | y in node.right.kvmap
          ensures k != y;
        {
          if k == y {
            O.Transitivity(k, node.key, y);
            O.Antisymmetry(k, node.key);
          }
        }
        contains := ContainsKey(node.left, k);
      } else if node.right != null && O.Leq(node.key, k) {
        contains := ContainsKey(node.right, k);
      } else {
        contains := false;
      }
    }

    static method Add(k: O.T, v: V, root: TreeNode?<V>) returns (node: TreeNode<V>)
      modifies if root != null then root.Repr else {};
      requires root != null ==> root.Valid();
      ensures node.Valid();
      ensures root == null ==> fresh(node.Repr) && node.kvmap == map[k := v];
      ensures root != null ==> fresh(node.Repr - old(root.Repr)) && node == old(root) && node.kvmap == old(root.kvmap)[k := v];
      decreases if root != null then root.Repr else {};
    {
      if (root == null) {
        node := new TreeNode(k, v);
      } else if k == root.key {
        root.value := v;
        root.kvmap := root.kvmap[k := v];
        node := root;
      } else if O.Leq(k, root.key) && root.right == null {
        var leftNode := Add(k, v, root.left);
        root.left := leftNode;
        root.Repr := root.Repr + root.left.Repr;
        root.kvmap := root.kvmap[k := v];
        node := root;
      } else if O.Leq(k, root.key) {
        forall y | y in root.right.kvmap
          ensures k != y;
        {
          if k == y {
            O.Transitivity(k, root.key, y);
            O.Antisymmetry(k, root.key);
          }
        }
        var updatedLeftNode := Add(k, v, root.left);
        root.left := updatedLeftNode;
        root.Repr := root.Repr + root.left.Repr;
        root.kvmap := root.kvmap[k := v];
        node := root;
      } else {
        O.Totality(k, root.key);
        var updatedRightNode := Add(k, v, root.right);
        root.right := updatedRightNode;
        root.Repr := root.Repr + root.right.Repr;
        root.kvmap := root.kvmap[k := v];
        node := root;
      }
    }

    static method RemoveMin(root: TreeNode<V>) returns (minKey: O.T, minValue: V, node: TreeNode?<V>)
      modifies root.Repr;
      requires root.Valid();
      ensures node == null ==> old(root.kvmap) == map[minKey := minValue];
      ensures node != null ==> node.Valid() && node.Repr <= old(root.Repr) && node.kvmap == removeMap(old(root.kvmap), minKey);
      ensures minKey in old(root.kvmap) && (forall x :: x in old(root.kvmap) ==> O.Leq(minKey, x)) && old(root.kvmap)[minKey] == minValue;
      decreases root.Repr;
    {
      if (root.left == null) {
        O.Totality(root.key, root.key);
        minKey := root.key;
        minValue := root.value;
        node := root.right;
      } else {
        var newMinNode;
        minKey, minValue, newMinNode := RemoveMin(root.left);
        O.Totality(root.key, root.key);
        if root.right != null {
          forall x | x in root.right.kvmap
            ensures O.Leq(minKey, x);
          {
            O.Transitivity(minKey, root.key, x);
          }
        }
        root.left := newMinNode;
        root.kvmap := removeMap(root.kvmap, minKey);
        if (root.left != null) {
          root.Repr := root.Repr + root.left.Repr;
        }
        node := root;
      }
    }

    static method Remove(k: O.T, root: TreeNode<V>) returns (node: TreeNode?<V>)
      modifies root.Repr;
      requires root.Valid();
      requires k in root.kvmap;
      ensures node == null ==> old(root.kvmap) == map[k := old(root.kvmap)[k]];
      ensures node != null ==> node.Valid() && node.Repr <= old(root.Repr) && node.kvmap == removeMap(old(root.kvmap), k);
      decreases root.Repr;
    {
      if (k == root.key) {
        if (root.left == null && root.right == null) {
          node := null;
        } else if (root.left == null) {
          node := root.right;
        } else if (root.right == null) {
          node := root.left;
        } else {
          var minKey, minValue, rightNode := RemoveMin(root.right);
          forall y | y in root.left.kvmap
            ensures minKey != y && O.Leq(y, minKey);
          {
            O.Transitivity(y, root.key, minKey);
            if minKey == y {
              O.Antisymmetry(root.key, minKey);
            }
          }
          root.key := minKey;
          root.value := minValue;
          root.right := rightNode;
          root.kvmap := removeMap(root.kvmap, k);
          if (root.right != null) {
            root.Repr := root.Repr + root.right.Repr;
          }
          node := root;
        }
      } else if root.left != null && O.Leq(k, root.key) && root.right == null {
        var leftNode := Remove(k, root.left);
        root.left := leftNode;
        root.kvmap := removeMap(root.kvmap, k);
        if (root.left != null) {
          root.Repr := root.Repr + root.left.Repr;
        }
        node := root;
      } else if root.left != null && O.Leq(k, root.key) {
        forall y | y in root.right.kvmap
          ensures k != y;
      {
        if k == y {
          O.Transitivity(k, root.key, y);
          O.Antisymmetry(k, root.key);
        }
      }
      var leftNode := Remove(k, root.left);
      root.left := leftNode;
      root.kvmap := removeMap(root.kvmap, k);
      if (root.left != null) {
        root.Repr := root.Repr + root.left.Repr;
      }
      node := root;
      } else {
        var rightNode := Remove(k, root.right);
        root.right := rightNode;
        root.kvmap := removeMap(root.kvmap, k);
        if (root.right != null) {
          root.Repr := root.Repr + root.right.Repr;
        }
        node := root;
      }
    }

    static method Size(root: TreeNode?<V>) returns (s : int)
      requires root != null ==> root.Valid();
      ensures root == null ==> s == 0;
      ensures root != null ==> s == |root.kvmap|;
      decreases if root != null then root.Repr else {};
    {
      if root == null {
        s := 0;
      } else if root.left == null && root.right == null {
        s := 1;
      } else if root.right == null {
        var ls := Size(root.left);
        s := ls + 1;
      } else if root.left == null {
        var lr := Size(root.right);
        s := lr + 1;
      } else {
        disjointUnionMapSize(root.left.kvmap, root.right.kvmap);
        var ls := Size(root.left);
        var rs := Size(root.right);
        s := ls + rs + 1;
      }
    }

    static method KeySet(root: TreeNode?<V>) returns (keys: set<O.T>)
      requires root != null ==> root.Valid();
      ensures root == null ==> keys == {};
      ensures root != null ==> keys == domainMap(root.kvmap);
      decreases if root != null then root.Repr else {};
    {
      if root == null {
        keys := {};
      } else if root.left == null && root.right == null {
        keys := {root.key};
      } else if root.right == null {
        var lkeys := KeySet(root.left);
        keys := lkeys + {root.key};
      } else if root.left == null {
        var rkeys := KeySet(root.right);
        keys := rkeys + {root.key};
      } else {
        var lkeys := KeySet(root.left);
        var rkeys := KeySet(root.right);
        keys := lkeys + rkeys + {root.key};
      }
    }

  }

  class TreeMap<V> {

    var root: TreeNode?<V>;

    ghost var kvmap: map<O.T, V>;
    ghost var Repr: set<object>;

    predicate Valid()
      reads this, Repr;
    {
      this in Repr &&
      (root == null ==> kvmap == map[]) &&
      (root != null ==> root in Repr && root.Repr <= Repr && this !in root.Repr && root.Valid() && kvmap == root.kvmap)
    }

    constructor()
      ensures Valid() && fresh(Repr);
      ensures kvmap == map[];
    {
      root := null;
      Repr := {this};
      kvmap := map[];
    }

    constructor Copy(t : TreeMap<V>)
      requires t.Valid();
      ensures Valid() && fresh(Repr);
      ensures kvmap == t.kvmap;
    {
      var r : TreeNode?<V> := null;
      var ks := t.KeySet();
      while ks != {}
        invariant (if r == null then map[] else r.kvmap) == removeMapSet(t.kvmap, ks);
        invariant r != null ==> r.Valid() && fresh(r.Repr);
        invariant ks <= domainMap(t.kvmap);
        decreases |ks|;
      {
        var x :| x in ks;
        var v := t.GetValue(x);
        r := TreeNode.Add(x, v, r);
        ks := ks - {x};
      }
      if r != null {
        Repr := {this} + r.Repr;
        kvmap := r.kvmap;
      } else {
        Repr := {this};
        kvmap := map[];
      }
      root := r;
    }

    method Size() returns (s : int)
      requires Valid();
      ensures s == |kvmap|;
    {
      s := TreeNode.Size(root);
    }

    method KeySet() returns (keys : set<O.T>)
      requires Valid();
      ensures keys == domainMap(kvmap);
    {
      keys := TreeNode.KeySet(root);
    }

    method IsEmpty() returns (e: bool)
      requires Valid();
      ensures e <==> kvmap == map[] && |kvmap| == 0;
    {
      e := root == null;
    }

    method ContainsKey(k: O.T) returns (contains: bool)
      requires Valid();
      ensures contains <==> k in kvmap;
    {
      if root == null {
        contains := false;
      } else {
        contains := TreeNode.ContainsKey(root, k);
      }
    }

    method GetValue(k: O.T) returns (value: V)
      requires k in kvmap;
      requires Valid();
      ensures value == kvmap[k];
    {
      value := TreeNode.GetValue(root, k);
    }

    method Add(k: O.T, v: V)
      modifies Repr;
      requires Valid();
      ensures Valid() && fresh(Repr - old(Repr));
      ensures kvmap == old(kvmap)[k := v];
    {
      var updatedRoot := TreeNode.Add(k, v, root);
      root := updatedRoot;
      kvmap := root.kvmap;
      Repr := root.Repr + {this};
    }

    method Remove(k: O.T)
      modifies Repr;
      requires Valid();
      requires k in kvmap;
      ensures Valid() && Repr <= old(Repr);
      ensures kvmap == removeMap(old(kvmap), k);
    {
      root := TreeNode.Remove(k, root);
      if (root == null) {
        Repr := {this};
        kvmap := map[];
      } else {
        kvmap := root.kvmap;
        Repr := root.Repr + {this};
      }
    }

    method TryGetValue(k:O.T) returns (vo:Option<V>)
      requires Valid();
      ensures vo != None <==> k in kvmap;
      ensures vo != None ==> vo == Some(kvmap[k]);
    {
      vo := TreeNode.TryGetValue(root, k);
    }

    static method From(t : TreeMap<V>) returns (t' : TreeMap<V>)
      requires t.Valid();
      ensures t'.Valid() && fresh(t'.Repr);
      ensures t'.kvmap == t.kvmap;
    {
      var ct := new TreeMap<V>();
      var ks := t.KeySet();
      while ks != {}
        invariant ct.kvmap == removeMapSet(t.kvmap, ks);
        invariant ct.Valid();
        invariant ks <= domainMap(t.kvmap);
        invariant fresh(ct.Repr);
        decreases |ks|;
      {
        var x :| x in ks;
        var v := t.GetValue(x);
        ct.Add(x, v);
        ks := ks - {x};
      }
      t' := ct;
    }

  }

}

module TotalOrderInt refines TotalOrder {
  type T = int

  predicate method Leq(a:T, b:T) {
    a <= b
  }

  lemma Antisymmetry ... { }
  lemma Transitivity ... { }
  lemma Totality ... { }
}

module MapInt refines Map {
  import O = TotalOrderInt
}

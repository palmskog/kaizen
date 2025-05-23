include "SeqUtil.dfy"
include "TotalOrder.dfy"

abstract module OrderedSeqUtil {
  import O : TotalOrder
  import opened SeqUtil
  import opened SeqUtilLemmas

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
        (left != null ==> left in Repr && left.Repr <= this.Repr && this !in left.Repr && left.Valid() &&
        forall y :: y in left.kvmap ==> y != key && O.Leq(y, key)) &&
        (right != null ==> right in Repr && right.Repr <= Repr && this !in right.Repr && right.Valid() &&
        forall y :: y in right.kvmap ==> y != key && O.Leq(key, y)) &&
        (left == null && right == null ==> kvmap == map[key := value]) &&
        (left != null && right == null ==> kvmap == left.kvmap[key := value]) &&
        (left == null && right != null ==> kvmap == right.kvmap[key := value]) &&
        (left != null && right != null ==> left.Repr !! right.Repr && right.kvmap !! left.kvmap &&
        kvmap == union(left.kvmap, right.kvmap)[key := value])
    }

    constructor(k: O.T, v: V)
      ensures Valid() && fresh(Repr - {this});
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

    static method Put(k: O.T, v: V, root: TreeNode?<V>) returns (node: TreeNode<V>)
      modifies if root != null then root.Repr else {};
      requires root != null ==> root.Valid();
      ensures node.Valid();
      ensures root == null ==> fresh(node.Repr) && node.kvmap == map[k := v];
      ensures root != null ==> fresh(node.Repr - old(root.Repr)) && node == old(root) && node.kvmap == old(root.kvmap)[k := v];
      decreases if root != null then root.Repr else {};
    {
      if (root == null) {
        node := new TreeNode(k, v);
        assert node.Valid();
      } else if k == root.key {
        root.value := v;
        root.kvmap := root.kvmap[k := v];
        node := root;
        assert node.Valid();
      } else if O.Leq(k, root.key) && root.right == null {
        var leftNode := Put(k, v, root.left);
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
        var updatedLeftNode := Put(k, v, root.left);
        root.left := updatedLeftNode;
        root.Repr := root.Repr + root.left.Repr;
        root.kvmap := root.kvmap[k := v];
        node := root;
      } else {
        O.Totality(k, root.key);
        var updatedRightNode := Put(k, v, root.right);
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
      ensures node != null ==> node.Valid() && node.Repr <= old(root.Repr) && node.kvmap == remove_map(old(root.kvmap), minKey);
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
        root.kvmap := remove_map(root.kvmap, minKey);
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
      ensures node != null ==> node.Valid() && node.Repr <= old(root.Repr) && node.kvmap == remove_map(old(root.kvmap), k);
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
          root.kvmap := remove_map(root.kvmap, k);
          if (root.right != null) {
            root.Repr := root.Repr + root.right.Repr;
          }
          node := root;
        }
      } else if root.left != null && O.Leq(k, root.key) && root.right == null {
        var leftNode := Remove(k, root.left);
        root.left := leftNode;
        root.kvmap := remove_map(root.kvmap, k);
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
      root.kvmap := remove_map(root.kvmap, k);
      if (root.left != null) {
        root.Repr := root.Repr + root.left.Repr;
      }
      node := root;
      } else {
        var rightNode := Remove(k, root.right);
        root.right := rightNode;
        root.kvmap := remove_map(root.kvmap, k);
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
      ensures root != null ==> keys == domain(root.kvmap);
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
      ensures Valid() && fresh(Repr - {this});
      ensures kvmap == map[];
    {
      root := null;
      Repr := {this};
      kvmap := map[];
    }

    static method From(t : TreeMap<V>) returns (t' : TreeMap<V>)
      requires t.Valid();
      ensures t'.Valid() && fresh(t'.Repr);
      ensures t'.kvmap == t.kvmap;
    {
      var ct := new TreeMap<V>();
      var ks := t.KeySet();
      while ks != {}
        invariant ct.kvmap == remove_map_set(t.kvmap, ks);
        invariant ct.Valid();
        invariant ks <= domain(t.kvmap);
        invariant fresh(ct.Repr);
        decreases |ks|;
      {
        var x :| x in ks;
        var v := t.Get(x);
        ct.Put(x, v);
        ks := ks - {x};
      }
      t' := ct;
    }

    /*
    constructor Copy(t : TreeMap<V>)
      requires t.Valid();
      ensures Valid() && fresh(Repr - {this});
      ensures kvmap == t.kvmap;
    {
      var r : TreeNode?<V> := null;
      var ks := t.KeySet();
      while ks != {}
        invariant (if r == null then map[] else r.kvmap) == remove_map_set(t.kvmap, ks);
        invariant r != null ==> r.Valid() && fresh(r.Repr);
        invariant ks <= domain(t.kvmap);
        decreases |ks|;
      {
        var x :| x in ks;
        var v := t.Get(x);
        r := TreeNode.Put(x, v, r);
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
    */

    method Size() returns (s : int)
      requires Valid();
      ensures s == |kvmap|;
    {
      s := TreeNode.Size(root);
    }

    method KeySet() returns (keys : set<O.T>)
      requires Valid();
      ensures keys == domain(kvmap);
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

    method Get(k: O.T) returns (value: V)
      requires k in kvmap;
      requires Valid();
      ensures value == kvmap[k];
    {
      value := TreeNode.GetValue(root, k);
    }

    method Put(k: O.T, v: V)
      modifies Repr;
      requires Valid();
      ensures Valid() && fresh(Repr - old(Repr));
      ensures kvmap == old(kvmap)[k := v];
    {
      var updatedRoot := TreeNode.Put(k, v, root);
      root := updatedRoot;
      kvmap := root.kvmap;
      Repr := root.Repr + {this};
    }

    method Remove(k: O.T)
      modifies Repr;
      requires Valid();
      requires k in kvmap;
      ensures Valid() && Repr <= old(Repr);
      ensures kvmap == remove_map(old(kvmap), k);
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

  }

  predicate ordered_seq_sorted(s:seq<O.T>) {
    forall i,j :: 0 <= i < j < |s| ==> O.Leq(s[i], s[j])
  }

  lemma ordered_set_has_least_member(s:set<O.T>)
    requires s != {};
    ensures exists min :: min in s && forall x :: x in s ==> O.Leq(min, x);
  {
    var x :| x in s;
    var xs := s - {x};
    var ys := {x};
    assert xs + ys == s;
    O.Totality(x, x);
    while (xs != {})
      decreases |xs|;
      invariant forall z :: z in ys ==> O.Leq(x, z);
      invariant xs + ys == s;
      invariant x in s;
    {
      var y :| y in xs;
      if O.Leq(y, x) {
        forall z | z in ys {
          O.Transitivity(y, x, z);
        }
        assert forall z :: z in ys ==> O.Leq(y, z);
        assert O.Leq(y, x);
        O.Totality(y, y);
        x := y;
        assert O.Leq(x, y);
      } else {
        O.Totality(x, y);
        assert O.Leq(x, y);
        assert forall z :: z in ys ==> O.Leq(x, z);
      }
      assert O.Leq(x, y);
      xs := xs - {y};
      ys := ys + {y};
    }
  }

  function ordered_set_to_seq(s:set<O.T>) : seq<O.T>
    ensures forall i :: i in ordered_set_to_seq(s) <==> i in s;
    ensures nodup(ordered_set_to_seq(s));
    ensures ordered_seq_sorted(ordered_set_to_seq(s))
    ensures |s| == |ordered_set_to_seq(s)|;
  {
    if s == {} then
      []
    else
      ordered_set_has_least_member(s);
      var x :| x in s && forall y :: y in s ==> O.Leq(x, y);
      var xs := s - {x};
      [x] + ordered_set_to_seq(xs)
  }

  function ordered_keys_of<V>(m:map<O.T,V>) : seq<O.T>
    ensures forall i :: i in m <==> i in ordered_keys_of(m);
    ensures nodup(ordered_keys_of(m));
    ensures ordered_seq_sorted(ordered_keys_of(m));
    ensures |domain(m)| == |ordered_keys_of(m)|;
  {
    ordered_set_to_seq(domain(m))
  }

  lemma ordered_sorted_eq(s:set<O.T>, sq:seq<O.T>)
    requires ordered_seq_sorted(sq);
    requires nodup(sq);
    requires forall i :: i in sq <==> i in s;
    ensures ordered_set_to_seq(s) == sq;
  {
    if |sq| == 0 { } else {
      var x := sq[0];
      assert x in s;
      assert x in ordered_set_to_seq(s);
      var xs := s - {x};
      ordered_sorted_eq(xs, sq[1..]);
      O.Antisymmetry(ordered_set_to_seq(s)[0], x);
    }
  }

  method InsertionSortAux(i:O.T, sq:seq<O.T>) returns (sqs:seq<O.T>)
    requires ordered_seq_sorted(sq);
    ensures multiset([i] + sq) == multiset(sqs);
    ensures ordered_seq_sorted(sqs);
  {
    if |sq| == 0 {
      sqs := [i];
    } else if O.Leq(i, sq[0]) {
      sqs := [i] + sq;
      O.Totality(sq[0], sq[0]);
      forall x | x in sq {
        O.Transitivity(i, sq[0], x);
      }
    } else {
      O.Totality(i, sq[0]);
      assert O.Leq(sq[0], i) && i != sq[0];
      assert forall x :: x in sq[1..] ==> O.Leq(sq[0], x);
      var sqs' := InsertionSortAux(i, sq[1..]);
      assert ordered_seq_sorted(sqs');
      ghost var isqs := [i] + sq[1..];
      assert multiset(isqs) == multiset(sqs');
      assert forall x :: x in multiset(sqs') ==> x in sqs';
      assert forall x :: x in multiset(isqs) ==> x in isqs;
      assert forall x :: x in sqs' <==> x in isqs;
      assert forall x :: x in sqs' ==> O.Leq(sq[0], x);
      sqs := [sq[0]] + sqs';
      O.Totality(sqs[0], sqs[0]);
      assert forall x :: x in sqs ==> O.Leq(sqs[0], x);
      assert forall j :: 0 <= j < |sqs| ==> sqs[j] in sqs;
      assert multiset(sqs) == multiset([sq[0]] + [i] + sq[1..]);
      assert sq == [sq[0]] + sq[1..];
      assert multiset(sq) == multiset([sq[0]] + sq[1..]);
    }
  }

  method OrderedSeqSortImpl(sq:seq<O.T>) returns (sqs:seq<O.T>)
    ensures ordered_seq_sorted(sqs);
    ensures multiset(sq) == multiset(sqs)
  {
    if |sq| == 0 {
      sqs := [];
    } else {
      var sqs' := OrderedSeqSortImpl(sq[1..]);
      assert multiset(sqs') == multiset(sq[1..]);
      sqs := InsertionSortAux(sq[0], sqs');
      assert multiset(sqs) == multiset([sq[0]] + sqs');
      assert multiset(sqs) == multiset([sq[0]] + sq[1..]);
      assert [sq[0]] + sq[1..] == sq;
    }
  }

  method OrderedSetToSeqImpl(s:set<O.T>) returns (sq:seq<O.T>)
    ensures sq == ordered_set_to_seq(s);
  {
    var q := [];
    var xs := s;
    while |xs| > 0
      invariant forall y :: y in xs ==> y in s;
      invariant nodup(q);
      invariant forall y :: y in q <==> y in s - xs;
    {
      var x :| x in xs;
      assert x in s;
      assert x !in q;
      q := q + [x];
      xs := xs - {x};
    }
    assert nodup(q);
    assert forall y :: y in q <==> y in s;
    sq := OrderedSeqSortImpl(q);
    assert multiset(q) == multiset(sq);
    assert forall y :: y in q <==> y in multiset(q);
    assert forall y :: y in multiset(q) <==> y in multiset(sq);
    assert forall y :: y in multiset(sq) <==> y in sq;
    assert forall y :: y in q <==> y in sq;
    multisetNodup(q, sq);
    ordered_sorted_eq(s, sq);
  }
  
}

module OrderedSeqUtilSeqInt refines OrderedSeqUtil {
  import O = TotalOrderSeqInt
}

module OrderedSeqUtilSeqByte refines OrderedSeqUtil {
  import O = TotalOrderSeqByte
}

module OrderedSeqUtilSeqByte32AsInt refines OrderedSeqUtil {
  import O = TotalOrderSeqByte32AsInt
}

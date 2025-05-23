module {:extern "Collections"} Collections {

  class LinkedList<T(==)> {

    var head : Node?<T>;
    var size : int;

    ghost var list : seq<T>;
    ghost var Repr : set<object>;

    predicate Valid()
      reads this, Repr, head;
      reads if head != null then head.Repr else {};
    {
      |list| == size &&
      (head == null ==> list == [] && Repr == {this}) &&
      (head != null ==> head.Valid() && list == head.list && Repr == {this} + head.Repr)
    }

    constructor()
      ensures Valid() && fresh(Repr);
      ensures size == 0;
      ensures list == [];
    {
      head := null;
      size := 0;
      list := [];
      Repr := {this};
    }

    method Size() returns (lSize: int)
      requires Valid();
      ensures lSize == |list|;
    {
      lSize := size;
    }

    method IsEmpty() returns (lEmpty: bool)
      requires Valid();
      ensures Valid();
      ensures lEmpty <==> |list| == 0;
    {
      lEmpty := size == 0;
    }

    method Get(index: int) returns (element: T)
      requires Valid();
      requires 0 <= index < size;
      ensures element == list[index];
    {
      element := Node.Get(head, index);
    }

    method AddFirst(element: T)
      modifies Repr;
      requires Valid();
      ensures Valid();
      ensures size == old(size) + 1;
      ensures list == [element] + old(list);
      ensures forall k :: 1 <= k < size ==> list[k] == old(list[k-1]);
      ensures fresh(Repr - old(Repr));
    {
      if head != null {
        head := new Node<T>.Insert(element, head);
      } else {
        head := new Node<T>.Singleton(element);
      }
      Repr := {this} + head.Repr;
      list := head.list;
      size := head.size;
    }

    method Add(element: T) returns (index: int)
      modifies Repr;
      requires Valid();
      ensures Valid();
      ensures size == old(size) + 1;
      ensures index == old(size);
      ensures list[index] == element;
      ensures list == old(list) + [element];
      ensures forall k :: 0 <= k < index ==> list[k] == old(list[k]);
      ensures fresh(Repr - old(Repr));
    {
      var tail := new Node<T>.Singleton(element);
      if head != null {
        head := Node.Append(head, tail);
      } else {
        head := tail;
      }
      Repr := {this} + head.Repr;
      list := head.list;
      index := size;
      size := head.size;
    }

    method Append(l:LinkedList<T>)
      modifies Repr;
      requires Valid();
      requires l.Valid();
      requires Repr !! l.Repr;
      ensures Valid();
      ensures size == old(size) + l.size;
      ensures list == old(list) + l.list;
      ensures forall k :: 0 <= k < old(size) ==> list[k] == old(list[k]);
      ensures forall k :: 0 <= k < l.size ==> list[old(size) + k] == l.list[k];
    {
      if head != null && l.head != null {
        head := Node.Append(head, l.head);
        Repr := {this} + head.Repr;
        list := head.list;
        size := head.size;
      } else if head == null && l.head != null {
        head := l.head;
        Repr := {this} + head.Repr;
        list := head.list;
        size := head.size;
      }
    }

  }

  class Node<T(==)> {

    ghost var list : seq<T>;
    ghost var Repr : set<Node<T>>;

    var elem : T;
    var next : Node?<T>;
    var size : int;

    predicate Valid()
      reads this, Repr;
    {
      this in Repr &&
      (next == null ==> Repr == {this} && list == [elem]) &&
      (next != null ==> next in Repr && Repr == {this} + next.Repr && this !in next.Repr && list == [elem] + next.list && next.Valid()) &&
      size == |list|
    }

    constructor Singleton(e: T)
      ensures Valid() && fresh(Repr);
      ensures list == [e];
    {
      elem := e;
      next := null;
      size := 1;

      list := [e];
      Repr := {this};
    }

    constructor Insert(e: T, n: Node<T>)
      requires n.Valid();
      ensures Valid() && fresh(Repr - n.Repr);
      ensures list == [e] + n.list;
      ensures Repr == {this} + n.Repr;
    {
      elem := e;
      next := n;
      size := 1 + n.size;

      list := [e] + n.list;
      Repr := {this} + n.Repr;
    }

    static method Size(n:Node<T>) returns (lSize: int)
      requires n.Valid();
      ensures lSize == |n.list|;
    {
      lSize := n.size;
    }

    static method Contains(n:Node<T>, e: T) returns (contains:bool)
      requires n.Valid();
      ensures contains <==> e in n.list;
    {
      contains := false;
      var curr := n;
      ghost var rem := n.list;
      ghost var elts := [];
      assert elts + rem == NodeSeq(n);
      while (curr != null)
        invariant curr != null ==> curr.Valid();
        invariant rem == NodeSeq(curr);
        invariant elts + rem == n.list;
        invariant contains <==> e in elts;
        decreases |rem|;
      {
        if e == curr.elem {
          contains := true;
          break;
        } else {
          elts := elts + [curr.elem];
          curr := curr.next;
          rem := NodeSeq(curr);
        }
      }
    }

    static method Elements(n:Node<T>) returns (xs:seq<T>)
      requires n.Valid();
      ensures xs == n.list;
    {
      xs := [];
      ghost var rem := n.list;
      var current := n;
      while (current != null)
        invariant current != null ==> current.Valid();
        invariant xs + rem == n.list;
        invariant rem == NodeSeq(current);
        decreases |rem|;
      {
        xs := xs + [current.elem];
        current := current.next;
        rem := NodeSeq(current);
      }
    }

    static method Get(n:Node<T>, index: int) returns (element: T)
      requires n.Valid();
      requires 0 <= index < n.size;
      ensures element == n.list[index];
    {
      var curr := n;
      var i := 0;
      ghost var rem := n.list;
      ghost var elts := [];
      assert elts + rem == NodeSeq(n);
      while i < index
        invariant 0 <= i <= index;
        invariant curr != null ==> curr.Valid();
        invariant rem == NodeSeq(curr);
        invariant elts + rem == n.list;
        invariant elts == n.list[..i];
        decreases |rem|;
      {
        elts := elts + [curr.elem];
        curr := curr.next;
        i := i + 1;
        rem := NodeSeq(curr);
      }
      element := curr.elem;
    }

    static method Append'<T>(pre: Node<T>, post: Node<T>) returns (prepost: Node<T>)
      modifies pre.Repr;
      requires pre.Valid();
      requires post.Valid();
      requires pre.Repr !! post.Repr;
      ensures prepost.Valid();
      ensures prepost.list == old(pre.list) + post.list;
      ensures prepost.Repr == old(pre.Repr) + post.Repr;
      ensures prepost.size == old(pre.size) + post.size;
      ensures post.Repr == old(post.Repr);
      ensures post.list == old(post.list);
      ensures post.size == old(post.size);
      decreases pre.Repr;
    {
      if (pre.next == null) {
        pre.Repr := pre.Repr + post.Repr;
        pre.list := pre.list + post.list;
        pre.size := pre.size + post.size;
        pre.next := post;
        prepost := pre;
      } else {
        var prepost1 := Append'(pre.next, post);
        pre.Repr := {pre} + prepost1.Repr;
        pre.list := [pre.elem] + prepost1.list;
        pre.size := 1 + prepost1.size;
        pre.next := prepost1;
        prepost := pre;
      }
    }

    static method Append(pre:Node<T>, post:Node<T>) returns (prepost:Node<T>)
      modifies pre.Repr;
      requires pre.Valid();
      requires post.Valid();
      requires pre.Repr !! post.Repr;
      ensures prepost.Valid();
      ensures prepost.Repr <= old(pre.Repr) + old(post.Repr);
      ensures prepost.list == old(pre.list) + old(post.list);
    {
      var rev := Reverse(pre);
      ghost var revlist := rev.list;
      assert |revlist| == |old(pre.list)|;
      assert forall i :: 0 <= i < |revlist| ==> revlist[i] == old(pre.list)[|old(pre.list)|-1-i];
      var current := rev;
      prepost := post;
      ghost var elts := [];
      ghost var revelts := [];
      ghost var rem := revlist;
      assert elts + rem == revlist;
      while (current != null)
        invariant |revelts| == |elts|;
        invariant current != null ==>
          current.Valid() &&
          current in old(pre.Repr) &&
          current.Repr <= old(pre.Repr) &&
          current.Repr !! prepost.Repr;
          invariant prepost.list == revelts + post.list;
          invariant prepost.Valid();
          invariant prepost.Repr <= old(pre.Repr) + old(post.Repr);
          invariant elts + rem == revlist;
          invariant elts == revlist[..|elts|];
          invariant forall i :: 0 <= i < |elts| ==> elts[i] == old(pre.list)[|old(pre.list)|-1-i] && elts[i] == revelts[|elts|-1-i];
          invariant rem == NodeSeq(current);
          decreases if current != null then |current.list| else -1;
      {
        elts := elts + [current.elem];
        revelts := [current.elem] + revelts;
        var nx := current.next;
        current.next := prepost;
        current.size := 1 + prepost.size;
        current.list := [current.elem] + prepost.list;
        current.Repr := {current} + prepost.Repr;
        prepost := current;
        current := nx;
        rem := NodeSeq(current);
      }
      assert |elts| == |revelts|;
      assert |revlist| == |old(pre.list)|;
      assert elts == revlist;
      RevEqAll(revlist, old(pre.list), revelts);
      assert prepost.list == old(pre.list) + post.list;
    }

    static method Reverse<T>(n:Node<T>) returns (reverse:Node<T>)
      modifies n.Repr;
      requires n.Valid();
      ensures reverse.Valid();
      ensures reverse.Repr <= old(n.Repr);
      ensures |reverse.list| == |old(n.list)|;
      ensures forall i :: 0 <= i < |reverse.list| ==> reverse.list[i] == old(n.list)[|old(n.list)|-1-i];
    {
      var current := n.next;
      reverse := n;
      reverse.next := null;
      reverse.size := 1;
      reverse.Repr := {reverse};
      reverse.list := [n.elem];
      while (current != null)
        invariant reverse.Valid() && reverse.Repr <= old(n.Repr);
        invariant current == null ==> |old(n.list)| == |reverse.list|;
        invariant current != null ==>
          current.Valid() &&
          current in old(n.Repr) && current.Repr <= old(n.Repr) &&
          current.Repr !! reverse.Repr;
          invariant current != null ==>
            |old(n.list)| == |reverse.list| + |current.list| &&
            current.list == old(n.list)[|reverse.list|..];
            invariant forall i :: 0 <= i < |reverse.list| ==> reverse.list[i] == old(n.list)[|reverse.list|-1-i];
            decreases if current != null then |current.list| else -1;
      {
        var nx := current.next;
        current.next := reverse;
        current.size := 1 + reverse.size;
        current.Repr := {current} + reverse.Repr;
        current.list := [current.elem] + reverse.list;
        reverse := current;
        current := nx;
      }
    }

    static method FromSet(s:set<T>) returns (n:Node?<T>)
      ensures s == {} ==> n == null;
      ensures s != {} ==> n != null;
      ensures n != null ==> n.Valid() && fresh(n.Repr);
      ensures forall i :: i in s <==> i in NodeSeq(n);
      ensures |NodeSeq(n)| == |s|;
    {
      if s == {} {
        n := null;
      } else {
        var x :| x in s;
        var n0 := FromSet(s - {x});
        if n0 != null {
          n := new Node.Insert(x, n0);
        } else {
          n := new Node.Singleton(x);
        }
      }
    }

    static method FromSeq(xs:seq<T>) returns (n:Node?<T>)
      ensures |xs| == 0 ==> n == null;
      ensures |xs| != 0 ==> n != null;
      ensures xs == NodeSeq(n);
      ensures n != null ==> n.Valid() && fresh(n.Repr);
    {
      if |xs| == 0 {
        n := null;
      } else if |xs| == 1 {
        n := new Node.Singleton(xs[0]);
      } else {
        var n' := FromSeq(xs[1..]);
        n := new Node.Insert(xs[0], n');
      }
    }

  }

  iterator ListIterator<T>(l: LinkedList<T>) yields (x: T)
    requires l.Valid();
    reads l.Repr;
    yield ensures |xs| <= |l.list|;
    yield ensures xs == l.list[..|xs|];
    yield ensures x == l.list[|xs|-1];
    ensures Valid();
    ensures xs == l.list;
  {
    var current := l.head;
    ghost var rem := l.list;
    while current != null
      invariant current != null ==> current.Valid();
      invariant xs + rem == l.list;
      invariant xs == l.list[..|xs|];
      invariant rem == if current != null then current.list else [];
      decreases if current != null then current.Repr else {};
    {
      yield current.elem;
      current := current.next;
      rem := if current != null then current.list else [];
    }
  }

  function NodeSeq<T>(n:Node?<T>) : seq<T>
    reads n;
    ensures n != null ==> NodeSeq(n) == n.list;
    ensures n == null ==> NodeSeq(n) == [];
  {
    if n != null then n.list else []
  }

  function NodeRepr<T>(n:Node?<T>) : set<Node<T>>
    reads n;
    ensures n != null ==> NodeRepr(n) == n.Repr;
    ensures n == null ==> NodeRepr(n) == {};
  {
    if n != null then n.Repr else {}
  }

  lemma RevEqAll<T>(s0:seq<T>, s1:seq<T>, s2:seq<T>)
    requires |s0| == |s1|;
    requires |s0| == |s2|;
    requires forall i :: 0 <= i < |s0| ==> s0[i] == s1[|s0|-1-i] && s0[i] == s2[|s0|-1-i];
    ensures s1 == s2;
  {
    forall i | 0 <= i < |s0|
      ensures s1[i] == s2[i];
      {
        if s1[i] != s2[i] {
          var j := |s0|-1-i;
          assert |s0|-1-(|s0|-1-i) == i;
          assert s0[j] == s1[i];
          assert s0[j] == s2[i];
        }
      }
  }

}

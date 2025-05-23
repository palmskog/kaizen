include "LinkedList.dfy"

method Iterate(l : Collections.LinkedList<int>) returns (s: seq<int>)
  requires l.Valid();
  ensures s == l.list;
{
  var iter := new Collections.ListIterator(l);
  var s' := [];
  while true
    invariant iter.Valid() && fresh(iter._new);
    invariant |iter.xs| <= l.size;
    invariant iter.xs == l.list[..|iter.xs|];
    invariant s' == iter.xs;
    decreases |l.list| - |iter.xs|;
  {
    var hasMore := iter.MoveNext();
    if !hasMore { break; }
    s' := s' + [iter.x];
  }
  s := s';
}

method Main()
{
  print "creating singleton list\n";
  var l1 := new Collections.Node.Singleton(3);
  assert l1.list == [3];

  print "inserting into singleton list\n";
  var l2 := new Collections.Node.Insert(4, l1);
  assert l2.list == [4,3];
  print l2.next.elem;
  print "\n";
}

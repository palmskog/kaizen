include "ArrayList.dfy"

module UseArrayList {
	import opened Collections

	method Iterate(l : ArrayList<int>)
		requires l.Valid();
	{
		var iter := new ListIterator(l);
		var s := [];
		while true
			invariant iter.Valid() && fresh(iter._new);
			invariant |iter.xs| <= l.size;
			invariant iter.xs == l.list[..|iter.xs|];
			invariant s == iter.xs;
			decreases |l.list| - |iter.xs|;
		{
			var hasMore := iter.MoveNext();
			if !hasMore { break; }
			s := s + [iter.x];
		}		
	}

	method Main() {
		print "creating ArrayList\n";
		var al := new ArrayList.InitialCapacity(1, 0);
		//assert fresh(al.Repr);
		assert al.list == [];
		var i1 := al.Add(1);
		assert al.list == [1];
		//assert al.arr.Length == 10;
		ghost var al' := al;
		var i2 := al.Add(2);
		var i3 := al.Add(3);
		assert al.list == [1, 2, 3];
		al.Remove(0);
		assert al.list == [2, 3];
		al.Remove(1);
		assert al.list == [2];
		assert al.size == 1;
		var bla := al.Get(0);
		print bla;
	}

}

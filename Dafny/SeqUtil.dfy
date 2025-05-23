module SeqUtil {

  function union<K(!new), V>(m: map<K,V>, m': map<K,V>): map<K,V>
    requires m !! m';
    ensures forall i :: i in union(m, m') <==> i in m || i in m';
    ensures forall i :: i in m ==> union(m, m')[i] == m[i];
    ensures forall i :: i in m' ==> union(m, m')[i] == m'[i];
  {
    map i | i in (domain(m) + domain(m')) :: if i in m then m[i] else m'[i]
  }

  function domain<K(!new),V>(m:map<K,V>) : set<K>
    ensures domain(m) == set k : K | k in m :: k;
    ensures forall i :: i in domain(m) <==> i in m;
    ensures (map i | i in domain(m) :: m[i]) == m;
  {
    set k | k in m :: k
  }

  predicate nodup<T>(s:seq<T>) {
    forall i, j :: 0 <= i < |s| && 0 <= j < |s| && i != j ==> s[i] != s[j]
  }

  function seq_to_set<T(!new)>(s:seq<T>) : set<T>
    ensures forall i :: i in s <==> i in seq_to_set(s);
  {
    set x | x in s
  }

  function set_to_seq<T(!new)>(s:set<T>) : seq<T>
    ensures forall i :: i in set_to_seq(s) <==> i in s;
    ensures nodup(set_to_seq(s));
    ensures |s| == |set_to_seq(s)|;
  {
    if s == {} then
      []
    else
      var x :| x in s;
      [x] + set_to_seq(s - {x})
  }

  function keys_of<K(!new),V>(m:map<K,V>) : seq<K>
    ensures forall i :: i in m <==> i in keys_of(m);
    ensures nodup(keys_of(m));
    ensures |domain(m)| == |keys_of(m)|;
  {
    set_to_seq(domain(m))
  }

  function undup<T>(s:seq<T>) : seq<T> {
    if |s| == 0 then
      []
    else
      if s[0] in s[1..] then
        undup(s[1..])
      else
        [s[0]] + undup(s[1..])
  }

  function remove_map<K,V>(m:map<K,V>, k:K) : map<K,V>
    ensures k !in remove_map(m, k);
    ensures domain(m) - {k} == domain(remove_map(m, k));
    ensures remove_map(m, k) == map i | i in m && i != k :: m[i];
    ensures k in m ==> |domain(m)| == |domain(remove_map(m, k))| + 1;
    ensures k !in m ==> |domain(m)| == |domain(remove_map(m, k))|;
    ensures forall u :: u in m && u != k ==> u in remove_map(m, k);
  {
    map ki | ki in m && ki != k :: m[ki]
  }

  function remove_map_set<U,V>(m: map<U, V>, s: set<U>) : map<U, V>
    ensures forall e :: e in s ==> e !in remove_map_set(m, s);
    ensures domain(m) - s == domain(remove_map_set(m, s));
    ensures remove_map_set(m, s) == map i | i in m && i !in s :: m[i];
    ensures forall u :: u in m && u !in s ==> u in remove_map_set(m, s);
  {
    map i | i in m && i !in s :: m[i]
  }

  function remove<T>(x:T, xs:seq<T>) : seq<T>
   requires x in xs;
   ensures multiset(remove(x,xs)) == multiset(xs)[x := multiset(xs)[x] - 1];
   ensures |remove(x,xs)|+1 == |xs|;
  {
     removeFromSequenceReducesMultiSet(xs);
     if xs[0]==x
     then xs[1..]
     else [xs[0]] + remove(x,xs[1..])
  }

  function seq_exclude<T(!new)>(s:seq<T>, exclude:seq<T>) : seq<T>
    ensures forall t :: t in seq_exclude(s, exclude) <==> t in s && t !in exclude;
  {
    if |s| == 0 then
      []
    else
      if s[0] in exclude then
        seq_exclude(s[1..], exclude)
      else
        [s[0]] + seq_exclude(s[1..], exclude)
  }

  function last<T>(default: T, s:seq<T>) : T {
    if |s| == 0 then
      default
    else
      s[|s|-1]
  }

  lemma seq_excludeMultisetEq<T>(s:seq<T>, exclude:seq<T>, exclude':seq<T>)
    requires multiset(exclude) == multiset(exclude');
    ensures seq_exclude(s, exclude) == seq_exclude(s, exclude');
  {
    if |s| == 0 { } else {
      if s[0] in exclude {
        assert s[0] in multiset(exclude);
        assert s[0] in multiset(exclude');
        assert s[0] in exclude';
      } else {
        assert s[0] !in multiset(exclude);
        assert s[0] !in multiset(exclude');
        assert s[0] !in exclude';
        seq_excludeMultisetEq(s[1..], exclude, exclude');
      }
    }
  }

  function map_seq<T1(!new),T2>(f:T1 -> T2, s:seq<T1>) : seq<T2>
    reads f.reads;
    requires forall i :: f.reads(i) == {};
    requires forall i :: 0 <= i < |s| ==> f.requires(s[i]);
    ensures |map_seq(f, s)| == |s|;
    ensures forall i :: 0 <= i < |s| ==> f(s[i]) == map_seq(f, s)[i];
  {
    if |s| == 0 then []
    else [f(s[0])] + map_seq(f, s[1..])
  }

  function foldr_seq<T,R(!new)>(f: (T,R) -> R, unit:R, s:seq<T>) : R
    reads f.reads;
    requires forall i, v :: 0 <= i < |s| ==> f.requires(s[i], v);
  {
    if |s| == 0 then unit
    else f(s[0], foldr_seq(f, unit, s[1..]))
  }

  function foldl_seq<T,R(!new)>(f: (R,T) -> R, u:R, s:seq<T>) : R
    reads f.reads;
    requires forall v, i :: 0 <= i < |s| ==> f.requires(v, s[i]);
  {
    if |s| == 0 then u
    else foldl_seq(f, f(u, s[0]), s[1..])
  }

  function filter_seq<T>(f: T -> bool, s:seq<T>) : seq<T>
    reads f.reads;
    requires forall i :: 0 <= i < |s| ==> f.requires(s[i]);
  {
    if |s| == 0 then []
    else if f(s[0]) then [s[0]] + filter_seq(f, s[1..]) else filter_seq(f, s[1..])
  }

  predicate all_seq<T>(f: T -> bool, s:seq<T>)
    reads f.reads;
    requires forall i :: 0 <= i < |s| ==> f.requires(s[i]);
  {
    if |s| == 0 then true
    else f(s[0]) && all_seq(f, s[1..])
  }

  lemma map_seq_cat<T1,T2>(f:T1 -> T2, s1:seq<T1>, s2:seq<T1>)
    ensures map_seq(f, s1 + s2) == map_seq(f, s1) + map_seq(f, s2);
  { }

  lemma foldl_seq_cat<T,R>(f:(R,T) -> R, u:R, s1:seq<T>, s2:seq<T>)
    ensures foldl_seq(f, u, s1 + s2) == foldl_seq(f, foldl_seq(f, u, s1), s2);
  {
    if |s1| == 0 {
      assert s1 + s2 == s2;
    } else {
      assert (s1 + s2)[1..] == s1[1..] + s2;
      foldl_seq_cat(f, f(u, s1[0]), s1[1..], s2);
    }
  }

  lemma foldr_seq_cat<T,R>(f:(T,R) -> R, unit:R, s1:seq<T>, s2:seq<T>)
    ensures foldr_seq(f, unit, s1 + s2) == foldr_seq(f, foldr_seq(f, unit, s2), s1);
  {
    if |s1| == 0 {
      assert s1 + s2 == s2;
    } else {
      assert (s1 + s2)[1..] == s1[1..] + s2;
    }
  }

  lemma filter_seq_cat<T>(f: T -> bool, s1:seq<T>, s2:seq<T>)
    ensures filter_seq(f, s1 + s2) == filter_seq(f, s1) + filter_seq(f, s2);
  {
    if |s1| == 0 {
      assert s1 + s2 == s2;
    } else {
      assert (s1 + s2)[1..] == s1[1..] + s2;
    }
  }

  lemma removeFromSequenceReducesMultiSet<T>(xs:seq<T>)
   requires xs != [];
   ensures multiset(xs[1..]) == multiset(xs)[xs[0] := multiset(xs)[xs[0]] - 1];
  {
    assert [xs[0]]+xs[1..] == xs;
    assert multiset([xs[0]]+xs[1..]) == multiset(xs);
  }

}

module SeqUtilLemmas {
  import opened SeqUtil

  lemma non_empty_map_has_elements<S,T>(m:map<S,T>)
    requires |m| > 0;
    ensures exists x :: x in m;
  {
    var dom := domain(m);
    assert m !! map [];
    assert m != map [];
    assert |dom| > 0;
  }

  lemma mapSizeIsDomainSize<S,T>(dom:set<S>, m:map<S,T>)
    requires dom == domain(m);
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
    ensures |domain(union(m, m'))| == |domain(m)| + |domain(m')|;
  {
    if |m| == 0 {
      assert union(m, m') == m';
    } else {
      non_empty_map_has_elements(m);
      var x :| x in m;
      assert x in m;
      assert x !in m';
      assert x in domain(m);
      assert x !in domain(m');
      var m0 := remove_map(m, x);
      assert domain(m0) == domain(m) - {x};
      assert domain(union(m0, m')) == domain(union(m, m')) - {x};
      disjointUnionDomainMapSize(m0, m');
    }
  }

  lemma disjointUnionMapSize<U,V>(m:map<U,V>, m':map<U,V>)
    requires m !! m';
    ensures |union(m, m')| == |m| + |m'|;
  {
    disjointUnionDomainMapSize(m, m');
    mapSizeIsDomainSize(domain(union(m, m')), union(m, m'));
    mapSizeIsDomainSize(domain(m), m);
    mapSizeIsDomainSize(domain(m'), m');
  }

  lemma nodupInv<T>(s:seq<T>)
    requires nodup(s);
    ensures forall i, j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == s[j] ==> i == j;
  { }

  lemma undupIn<T>(s:seq<T>, t:T)
    ensures t in s ==> t in undup(s)
  { }

  lemma undupInAll<T>(s:seq<T>)
    ensures forall t :: t in s ==> t in undup(s);
  { }

  lemma inUndup<T>(s:seq<T>, t:T)
    ensures t in undup(s) ==> t in s
  {
    if |s| == 0 { } else {
      if s[0] in s[1..] {
        inUndup(s[1..], s[0]);
      } else {
        assert s[0] in [s[0]] + undup(s[1..]);
      }
    }
  }

  lemma inUndupAll<T>(s:seq<T>)
    ensures forall t :: t in undup(s) ==> t in s
  { }

  lemma inUndupMultiplicityOne<T>(s:seq<T>, t:T)
    ensures t in undup(s) ==> multiset(undup(s))[t] == 1;
  {
    if |s| == 0 { } else {
      if s[0] == t {
        if t in s[1..] {  } else {
          assert t !in s[1..];
          if t !in undup(s[1..]) { } else {
            inUndup(s[1..], t);
          }
        }
      } else { }
    }
  }

  lemma MultisetSpec<T>(s:seq<T>)
    ensures forall e :: e in s ==> e in multiset(s) && multiset(s)[e] > 0;
  { }

  lemma MultisetSpecInv<T>(s:seq<T>)
    ensures forall e :: multiset(s)[e] > 0 ==> exists i :: 0 <= i < |s| && s[i] == e;
  { }

  predicate Subpermutation<T>(xs:seq<T>, ys:seq<T>)
    ensures Subpermutation(xs,ys) ==> forall x :: x in xs ==> x in ys;
  {
    assert forall x :: x in xs ==> x in multiset(xs);
    multiset(xs) <= multiset(ys)
  }

  lemma SubpermutationIsSmaller<T>(xs:seq<T>, ys:seq<T>)
    requires Subpermutation(xs,ys);
    ensures |xs| <= |ys|;
  {
    var xs',ys' := xs,ys;
    var XS',YS' := multiset(xs),multiset(ys);
    var XS'',YS'' := multiset{},multiset{};
    while(|XS'|>0)
      invariant Subpermutation(xs',ys');
      invariant XS' == multiset(xs');
      invariant YS' == multiset(ys');
      invariant XS' + XS'' == multiset(xs);
      invariant YS' + YS'' == multiset(ys);
      invariant XS'' == YS'';
      invariant XS' <= YS';
    {
      var x := xs'[0];
      xs' := remove(x,xs');
      ys' := remove(x,ys');
      XS' := XS'[x := XS'[x] - 1];
      XS'' := XS''[x := XS''[x] + 1];
      YS' := YS'[x := YS'[x] - 1];
      YS'' := YS''[x := YS''[x] + 1];    
    }
  }

  lemma nodupMultiplicityOne<T>(xs:seq<T>, x:T)
    requires nodup(xs);
    requires x in xs;
    ensures multiset(xs)[x] == 1;
  {
    if multiset(xs)[x] == 0 {
      assert x !in xs;
    } else if multiset(xs)[x] == 1 {
    } else {
      assert multiset(xs)[x] > 1;
      var xs' := xs;
      var XS' := multiset(xs);
      var XS'' := multiset{};
      assert x in xs';
      while(|XS'|>0)
        invariant XS' == multiset(xs');
        invariant XS' + XS'' == multiset(xs);
        invariant x in xs';
        invariant nodup(xs');
        invariant multiset(xs')[x] > 1;
      {
        if xs'[0] == x {
          assert multiset(xs'[1..]) == multiset(remove(x, xs'));
          assert multiset(xs'[1..])[x] >= 1;
        } else {
          var y := xs'[0];
          xs' := remove(y,xs');
          XS' := XS'[y := XS'[y] - 1];
          XS'' := XS''[y := XS''[y] + 1];
        }
      }
    }
  }

  lemma twoSeqOccMultiplicityGt<T>(xs:seq<T>, x:T, i:int, j:int)
    requires 0 <= i < |xs|;
    requires 0 <= j < |xs|;
    requires xs[i] == x;
    requires xs[j] == x;
    requires i != j;
    ensures multiset(xs)[x] > 1;
  {
    assert multiset(xs)[x] != 0;
    if multiset(xs)[x] == 1 {
      var (min, max) := if i < j then (i, j) else (j, i);
      var k := 0;
      var min' := min;
      var max' := max;
      var xs' := xs;
      var XS' := multiset(xs);
      while (k < min)
        decreases min - k;
        invariant 0 <= min' < |xs'|;
        invariant 0 <= max' < |xs'|;
        invariant xs'[min'] == x;
        invariant xs'[max'] == x;
        invariant min' != max';
        invariant XS' == multiset(xs');
        invariant XS'[x] == 1;
        invariant min' == min - k;
      {
        var y := xs'[0];
        if y == x {
          removeFromSequenceReducesMultiSet(xs');
          assert xs'[min'] == x;
        } else {
          xs' := remove(y,xs');
          min' := min' - 1;
          max' := max' - 1;
          k := k + 1;
          XS' := XS'[y := XS'[y] - 1];
        }
      }
      assert xs'[0] == x;
      removeFromSequenceReducesMultiSet(xs');
      assert xs'[max'] == x;
    } else { }
  }

  lemma undupNodup<T>(s:seq<T>)
    ensures nodup(undup(s));
  {
    forall i, j | 0 <= i < |undup(s)| && 0 <= j < |undup(s)| && i != j
      ensures undup(s)[i] != undup(s)[j];
      {
      if undup(s)[i] != undup(s)[j] { } else {
        var t := undup(s)[i];
        inUndupMultiplicityOne(s, t);
        twoSeqOccMultiplicityGt(undup(s), t, i, j);
      }
    }
  }

  lemma undupNodupEq<T>(s:seq<T>)
    requires nodup(s);
    ensures undup(s) == s;
  { }

  lemma undupAddNotIn<T>(t:T, s:seq<T>)
    requires t !in s;
    requires nodup(s);
    ensures undup([t] + s) == [t] + s;
  {
    undupNodupEq([t] + s);
  }

  lemma undupAddIn<T>(t:T, s:seq<T>)
    requires t in s;
    requires nodup(s);
    ensures undup([t] + s) == s;
  {
    if |s| == 0 { } else {
      undupNodupEq(s);
    }
  }

  lemma undupAppend<T>(xs:seq<T>, ys:seq<T>)
    ensures undup(xs + undup(ys)) == undup(xs + ys);
  {
    if |xs| == 0 {
      assert xs == [];
      assert xs + ys == ys;
      assert undup(xs + ys) == undup(ys);
      assert xs + undup(ys) == undup(ys);
      assert undup(xs + undup(ys)) == undup(undup(ys));
      undupNodup(ys);
      undupNodupEq(undup(ys));
      assert undup(undup(ys)) == undup(ys);
    } else {
      assert xs + undup(ys) == [xs[0]] + (xs[1..] + undup(ys));
      assert (xs + undup(ys))[1..] == xs[1..] + undup(ys);
      assert xs + ys == [xs[0]] + (xs[1..] + ys);
      if xs[0] in (xs + undup(ys))[1..] {
        assert undup(xs + undup(ys)) == undup((xs + undup(ys))[1..]);
        assert undup((xs + undup(ys))[1..]) == undup(xs[1..] + undup(ys));
        if xs[0] in xs[1..] {
          assert xs[0] in (xs + ys)[1..];
          assert (xs + ys)[1..] == xs[1..] + ys;
          assert undup(xs + ys) == undup(xs[1..] + ys);
        } else {
          assert xs[0] in undup(ys);
          inUndup(ys, xs[0]);
          assert xs[0] in ys;
          assert xs[0] in (xs + ys)[1..];
        }
      } else {
        assert xs[0] !in (xs + undup(ys))[1..];
        assert xs[0] !in xs[1..];
        assert xs[0] !in undup(ys);
        if xs[0] in ys {
          undupIn(ys, xs[0]);
        } else {
          assert xs[0] !in ys;
        }
      }
    }
  }

  lemma nodupRemove<T>(xs:seq<T>, x:T)
    requires nodup(xs);
    requires x in xs;
    ensures nodup(remove(x, xs))
  {
    nodupMultiplicityOne(xs, x);
    var xs' := remove(x, xs);
    assert multiset(xs')[x] == 0;
    assert multiset(xs') == multiset(xs)[x := multiset(xs)[x] - 1];
    assert x !in xs';
    if |xs'| <= 1 {
      
    } else {
      forall i, j | 0 <= i < |xs'| && 0 <= j < |xs'| && i != j
        ensures xs'[i] != xs'[j];
        {
          if xs'[i] == xs'[j] {
            var y := xs'[i];
            assert y in multiset(xs)[x := multiset(xs)[x] - 1];
            assert y in multiset(xs);
            assert multiset(xs')[y] == multiset(xs)[y];
            twoSeqOccMultiplicityGt(xs', y, i, j);
            nodupMultiplicityOne(xs, y);
          } else { }
        }
    }
  }
  
  lemma nodupEq<T>(xs:seq<T>, ys:seq<T>)
    requires nodup(xs);
    requires nodup(ys);
    requires forall x :: x in xs ==> x in ys;
    requires forall x :: x in ys ==> x in xs;
    ensures multiset(xs) == multiset(ys)
  {
    var xs',ys' := xs,ys;
    
    var XS',YS' := multiset(xs), multiset(ys);
    var XS'',YS'' := multiset{}, multiset{};

    assert forall y :: y in xs' ==> y in ys' && y in multiset(xs');
    assert forall y :: y in ys' ==> y in xs' && y in multiset(ys');    
    while(|XS'|>0)
      invariant XS' == multiset(xs');
      invariant YS' == multiset(ys');
      invariant XS' + XS'' == multiset(xs);
      invariant YS' + YS'' == multiset(ys);
      invariant XS'' == YS'';
      invariant nodup(xs');
      invariant nodup(ys');
      invariant forall y :: y in XS' ==> y in YS';
      invariant forall y :: y in YS' ==> y in XS';
    {
      var x := xs'[0];
      
      assert x in XS';
      nodupMultiplicityOne(xs', x);
      assert XS'[x] == 1;

      assert x in YS';
      nodupMultiplicityOne(ys', x);
      assert YS'[x] == 1;

      nodupRemove(xs', x);
      nodupRemove(ys', x);
      
      xs' := remove(x,xs');      
      ys' := remove(x,ys');
      
      XS' := XS'[x := XS'[x] - 1];
      XS'' := XS''[x := XS''[x] + 1];
      
      YS' := YS'[x := YS'[x] - 1];
      YS'' := YS''[x := YS''[x] + 1];    
    }
  }

  lemma multisetToSeqPlus<T>(x:T, s:set<T>)
    requires x !in s;
    ensures multiset(set_to_seq({x} + s)) == multiset([x] + set_to_seq(s));
  {
    assert nodup(set_to_seq({x} + s));
    assert nodup([x] + set_to_seq(s));
    nodupEq(set_to_seq({x} + s), [x] + set_to_seq(s));
  }

  lemma undupAppendNotIn<T>(xs:seq<T>, ys:seq<T>)
    requires nodup(xs);
    requires nodup(ys);
    requires forall x :: x in xs ==> x !in ys;
    requires forall y :: y in ys ==> y !in xs;
    ensures nodup(xs + ys);
  {
    forall i, j | 0 <= i < |xs + ys| && 0 <= j < |xs + ys| && i != j // FIXME: trigger warning
      ensures (xs + ys)[i] != (xs + ys)[j];
      {
        if (xs + ys)[i] in xs && (xs + ys)[j] in xs {

        } else if (xs + ys)[i] in ys && (xs + ys)[j] in ys {

        } else if (xs + ys)[i] in xs && (xs + ys)[j] in ys {

        } else {

        }
      }
  }

  lemma multisetNodup<T>(sq1:seq<T>, sq2:seq<T>)
    requires nodup(sq1);
    requires multiset(sq1) == multiset(sq2);
    ensures nodup(sq2);
  {
    forall i, j | 0 <= i < |sq2| && 0 <= j < |sq2| && i != j
      ensures sq2[i] != sq2[j]
      {
        if sq2[i] != sq2[j] { } else {
          var x := sq2[i];
          twoSeqOccMultiplicityGt(sq2, x, i, j);
          assert multiset(sq2)[x] > 1;
          assert multiset(sq1)[x] > 1;
          nodupMultiplicityOne(sq1, x);
        }
      }
  }
}

module SeqUtilImpl {
  import opened SeqUtil

  method DomainImpl<K,V>(m:map<K,V>) returns (s:set<K>)
    ensures s == domain(m);
  {
    s := set k | k in m :: k;
  }

  method UndupImpl<T(==)>(s:seq<T>) returns (us:seq<T>)
    ensures us == undup(s);
  {
    if |s| == 0 {
      us := [];
    } else {
      if s[0] in s[1..] {
        us := UndupImpl(s[1..]);
      } else {
        var us' := UndupImpl(s[1..]);
        us := [s[0]] + us';
      }
    }
  }

  // FIXME: rewrite assuming array semantics of seq
  method SeqExcludeImpl<T(==)>(s:seq<T>, exclude:seq<T>) returns (xs:seq<T>)
    ensures xs == seq_exclude(s, exclude);
  {
    if |s| == 0 {
      xs := [];
    } else {
      if s[0] in exclude {
        xs := SeqExcludeImpl(s[1..], exclude);
      } else {
        var xs' := SeqExcludeImpl(s[1..], exclude);
        xs := [s[0]] + xs';
      }
    }
  }

  method LastImpl<T>(default: T, s:seq<T>) returns (t:T)
    ensures t == last(default, s);
  {
    if |s| == 0 {
      t := default;
    } else {
      t := s[|s|-1];
    }
  }

  method RemoveMapImpl<K,V>(m:map<K,V>, k:K) returns (rm: map<K,V>)
    ensures rm == remove_map(m, k);
  {
    rm := map ki | ki in m && ki != k :: m[ki];
  }

  method RemoveImpl<T(==)>(x:T, xs:seq<T>) returns (rs:seq<T>)
    requires x in xs;
    ensures rs == remove(x, xs);
  {
    if xs[0] == x {
      rs := xs[1..];
    } else {
      var rs' := RemoveImpl(x,xs[1..]);
      rs := [xs[0]] + rs';
    }
  }

}

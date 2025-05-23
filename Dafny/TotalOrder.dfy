include "NativeTypes.dfy"
include "NativeTypesUtil.dfy"

abstract module TotalOrder {
  type T(!new, ==) // the type to be compared

  predicate method Leq(a: T, b: T) // Leq(a,b) iff a <= b

  lemma Antisymmetry(a: T, b: T)
    requires Leq(a, b) && Leq(b, a)
    ensures a == b

  lemma Transitivity(a: T, b: T, c: T)
    requires Leq(a, b) && Leq(b, c)
    ensures Leq(a, c)

  lemma Totality(a: T, b: T)
    ensures Leq(a, b) || Leq(b, a)
}

module TotalOrderSeqInt refines TotalOrder {
  type T = seq<int>

  predicate method Leq(a:T, b:T) {
    if |a| == 0 then true
    else
      if |b| == 0 then false
      else
        if a[0] == b[0] then Leq(a[1..], b[1..])
        else a[0] < b[0]
  }

  lemma Antisymmetry ... { }
  lemma Transitivity ... { }
  lemma Totality ... { }
}

module TotalOrderSeqByte refines TotalOrder {
  import opened NativeTypes

  type T = seq<byte>

  predicate method Leq(a:T, b:T) {
    if |a| == 0 then true
    else
      if |b| == 0 then false
      else
        if a[0] == b[0] then Leq(a[1..], b[1..])
        else a[0] < b[0]
  }

  lemma Antisymmetry ... { }
  lemma Transitivity ... { }
  lemma Totality ... { }
}

module TotalOrderSeqByte32AsInt refines TotalOrder {
  import opened NativeTypes
  import opened NativeTypesUtil

  type T = seqbyte32

  predicate method Leq(a:T, b:T) {
    BEByteSeqToInt(a) <= BEByteSeqToInt(b)
  }

  lemma Antisymmetry ...
  {
    lemma_BEByteSeqToInt_bound(a);
    lemma_BEByteSeqToInt_bound(b);
    lemma_BEByteSeqToInt_invertability(a, BEByteSeqToInt(a), |a|);
    lemma_BEByteSeqToInt_invertability(b, BEByteSeqToInt(b), |b|);
  }
  lemma Transitivity ... { }
  lemma Totality ... { }
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

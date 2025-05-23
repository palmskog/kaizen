include "MathUtil.dfy"

module MathUtilImpl
{
  import opened MathUtil

  method DivnImpl(m: nat, d:nat) returns (md:nat)
    ensures md == divn(m, d);
  {
    if 0 < d {
      md := m / d;
    } else {
      md := 0;
    }
  }
  
  method PowerImpl(b:int, exp: nat) returns (p:int)
    ensures p == power(b, exp);
  {
    reveal_power();
    var p' := 1;
    var exp' := 0;
    while (exp' < exp)
      invariant p' == power(b, exp');
      invariant exp' <= exp;
    {
      p' := b * p';
      exp' := exp' + 1;
    }
    p := p';
  }

  method Power2Impl(exp: nat) returns (p:nat)
    ensures p == power2(exp);
  {
    reveal_power2();
    var p' := 1;
    var exp' := 0;
    while (exp' < exp)
      invariant p' == power2(exp');
      invariant exp' <= exp;
    {
      p' := 2 * p';
      exp' := exp' + 1;
    }
    p := p';
  }

  method CeilLog2Impl(n: nat) returns (c:nat)
    ensures c == ceil_log2(n);
  {
    var lg := TruncLogImpl(2, n);
    var p := Power2Impl(lg);
    if n == p {
      c := lg;
    } else {
      c := lg + 1;
    }
  }

  method TruncLogLoopImpl(p:nat, n0:nat, k:nat) returns (t:nat)
    ensures t == trunc_log_loop(p, n0, k);
    decreases k;
  {
    if k == 0 {
      t := 0;
    } else if p <= n0 {
      var d := DivnImpl(n0, p);
      var t' := TruncLogLoopImpl(p, d, k-1);
      t := t' + 1;
    } else {
      t := 0;
    }
  }

  method TruncLogImpl(p:nat, n:nat) returns (l:nat)
    ensures l == trunc_log(p, n);
  {
    l := TruncLogLoopImpl(p, n, n);
  }

}

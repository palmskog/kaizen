module MathUtil
{

  function divn(m:nat, d:nat) : nat {
    if 0 < d then m / d else 0
  }

  function trunc_log_loop(p:nat, n0:nat, k:nat) : nat
    decreases k;
  {
    if k == 0 then 0
    else if p <= n0 then trunc_log_loop(p, divn(n0, p), k - 1) + 1 else 0
  }

  function trunc_log(p: nat, n : nat) : nat {
    trunc_log_loop(p, n, n)
  }

  function {:opaque} power(b:int, exp: nat) : int {
    if exp == 0 then
      1
    else
      b * power(b, exp - 1)
  }

  function {:opaque} power2(exp: nat) : nat
    ensures power2(exp) > 0;
  {
    if exp == 0 then
      1
    else
      2 * power2(exp - 1)
  }

  function ceil_log2(n: nat) : nat {
    var lg := trunc_log(2, n);
    if n == power2(lg) then lg else lg + 1
  }

  lemma lemma_power2_32()
    ensures power2(8) == 0x100;
    ensures power2(16) == 0x10000;
    ensures power2(24) == 0x1000000;
    ensures power2(32) == 0x100000000;
  {
    reveal_power2();
    assert power2(0) == 0x1;
    assert power2(2) == 0x4;
    assert power2(4) == 0x10;
    assert power2(6) == 0x40;
    assert power2(8) == 0x100;
    assert power2(10) == 0x400;
    assert power2(12) == 0x1000;
    assert power2(14) == 0x4000;
    assert power2(16) == 0x10000;
    assert power2(18) == 0x40000;
    assert power2(20) == 0x100000;
    assert power2(22) == 0x400000;
    assert power2(24) == 0x1000000;
    assert power2(26) == 0x4000000;
    assert power2(28) == 0x10000000;
    assert power2(30) == 0x40000000;
  }

  lemma lemma_power2_add8(n:int)
    requires n >= 0;
    ensures power2(n + 1) == 2 * power2(n);
    ensures power2(n + 2) == 4 * power2(n);
    ensures power2(n + 3) == 8 * power2(n);
    ensures power2(n + 4) == 16 * power2(n);
    ensures power2(n + 5) == 32 * power2(n);
    ensures power2(n + 6) == 64 * power2(n);
    ensures power2(n + 7) == 128 * power2(n);
    ensures power2(n + 8) == 256 * power2(n);
  {
    reveal_power2();
  }

  lemma lemma_2to32()
    ensures power2(32) == 4294967296;
    ensures power2(24) == 16777216;
    ensures power2(19) == 524288;
    ensures power2(16) == 65536;
    ensures power2(8)  == 256;
    ensures power2(0) == 1;
  {
    lemma_2toX32();
  }

  lemma lemma_2to64()
    ensures power2(64) == 18446744073709551616;
    ensures power2(60) == 1152921504606846976;
  {
    lemma_2to32();
    lemma_power2_add8(32);
    lemma_power2_add8(40);
    lemma_power2_add8(48);
    lemma_power2_add8(56);
  }

  lemma lemma_2toX32()
    ensures power2(0) == 0x1;
    ensures power2(1) == 0x2;
    ensures power2(2) == 0x4;
    ensures power2(3) == 0x8;
    ensures power2(4) == 0x10;
    ensures power2(5) == 0x20;
    ensures power2(6) == 0x40;
    ensures power2(7) == 0x80;
    ensures power2(8) == 0x100;
    ensures power2(9) == 0x200;
    ensures power2(10) == 0x400;
    ensures power2(11) == 0x800;
    ensures power2(12) == 0x1000;
    ensures power2(13) == 0x2000;
    ensures power2(14) == 0x4000;
    ensures power2(15) == 0x8000;
    ensures power2(16) == 0x10000;
    ensures power2(17) == 0x20000;
    ensures power2(18) == 0x40000;
    ensures power2(19) == 0x80000;
    ensures power2(20) == 0x100000;
    ensures power2(21) == 0x200000;
    ensures power2(22) == 0x400000;
    ensures power2(23) == 0x800000;
    ensures power2(24) == 0x1000000;
    ensures power2(25) == 0x2000000;
    ensures power2(26) == 0x4000000;
    ensures power2(27) == 0x8000000;
    ensures power2(28) == 0x10000000;
    ensures power2(29) == 0x20000000;
    ensures power2(30) == 0x40000000;
    ensures power2(31) == 0x80000000;
    ensures power2(32) == 0x100000000;
  {
    reveal_power2();
  }

  lemma lemma_2toX()
    ensures power2(64) == 18446744073709551616;
    ensures power2(60) == 1152921504606846976;
    ensures power2(32) == 4294967296;
    ensures power2(24) == 16777216;
    ensures power2(19) == 524288;
    ensures power2(16) == 65536;
    ensures power2(8) ==  256;
  {
    lemma_2to32();
    lemma_2to64();
  }

  lemma lemma_power2_is_power_2(x:nat)
    ensures power2(x) == power(2, x);
  {
    reveal_power();
    reveal_power2();
    if (x != 0) {
      lemma_power2_is_power_2(x - 1);
    }
  }

  // ADMITTED
  lemma lemma_power2_adds(e1:nat, e2:nat)
    decreases e2;
    ensures power2(e1 + e2) == power2(e1) * power2(e2);

}

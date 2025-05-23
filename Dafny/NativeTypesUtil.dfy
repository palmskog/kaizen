include "NativeTypes.dfy"
include "MathUtil.dfy"

module NativeTypesUtil {
  import opened NativeTypes
  import opened MathUtil

  function method BEByteSeqToInt(bytes:seq<byte>) : int
    decreases |bytes|;
  {
    if bytes == [] then 0
    else BEByteSeqToInt(bytes[..|bytes|-1]) * 256 + (bytes[|bytes|-1] as int)
  }

  lemma lemma_BEByteSeqToInt_bound(bytes:seq<byte>)
    ensures 0 <= BEByteSeqToInt(bytes);
    ensures BEByteSeqToInt(bytes) < power2(8*|bytes|);
{
    lemma_2toX();
    if bytes == [] {
    } else {
        calc {
            BEByteSeqToInt(bytes[..|bytes|-1]) + 1;
            <=
            power2(8*(|bytes|-1));
        }

        calc {
            BEByteSeqToInt(bytes);
            BEByteSeqToInt(bytes[..|bytes|-1]) * 256 + bytes[|bytes|-1] as int;
            <
            BEByteSeqToInt(bytes[..|bytes|-1]) * 256 + 256;
            BEByteSeqToInt(bytes[..|bytes|-1]) * 256 + 1 * 256;
            (BEByteSeqToInt(bytes[..|bytes|-1]) + 1) * 256;
            <=
            power2(8*(|bytes|-1)) * 256;
            power2(8*(|bytes|-1)) * power2(8);
                { lemma_power2_adds(8*(|bytes|-1), 8); }
            power2(8*|bytes|);
        }
    }
  }

  // ADMITTED
  lemma lemma_BEByteSeqToInt_invertability(bytes:seq<byte>, val:int, width:nat)
    requires BEByteSeqToInt(bytes) == val;
    requires 0 <= val < power2(8*width);
    requires |bytes| == width;
    ensures  bytes == BEUintToSeqByte(val, width);

  lemma lemma_BEByteSeqToUint32_properties(bs:seq<byte>)
    requires |bs| == Uint32Size() as int;
    ensures  var ret := bs[0] as uint32 * 256*256*256 + bs[1] as uint32 * 256*256 + bs[2] as uint32 * 256 + bs[3] as uint32;
             ret as int == BEByteSeqToInt(bs);
  {

    lemma_2toX();
    var ret := bs[0] as uint64 * 256*256*256 + bs[1] as uint64 * 256*256 + bs[2] as uint64 * 256 + bs[3] as uint64;
    var byteSeq := bs;

    calc {
        BEByteSeqToInt(bs);
        BEByteSeqToInt(bs[..|bs|-1]) * 256 + bs[|bs|-1] as int;
            { assert bs[..|bs|-1][..|bs[..|bs|-1]|-1] == bs[..|bs|-2]; }
        (BEByteSeqToInt(bs[..|bs|-2]) * 256 + bs[|bs|-2] as int) * 256 + bs[|bs|-1] as int;
            { assert bs[..|bs|-2][..|bs[..|bs|-2]|-1] == bs[..|bs|-3]; }
        ((BEByteSeqToInt(bs[..|bs|-3]) * 256 + bs[|bs|-3] as int) * 256 + bs[|bs|-2] as int) * 256 + bs[|bs|-1] as int;
            { assert bs[..|bs|-3][..|bs[..|bs|-3]|-1] == bs[..|bs|-4]; }
        (((((((BEByteSeqToInt(bs[..|bs|-4]) * 256 + bs[|bs|-4] as int) * 256 + bs[|bs|-3] as int) * 256 + bs[|bs|-2] as int) * 256 + bs[|bs|-1] as int))));
        ret as int;
    }

  }

  lemma lemma_BEByteSeqToUint64_properties(bs:seq<byte>)
    requires |bs| == Uint64Size() as int;
    ensures var ret := bs[0] as uint64 * 256*256*256*0x100000000 + bs[1] as uint64 * 256*256*0x100000000 + bs[2] as uint64 * 256*0x100000000 + bs[3] as uint64 * 0x100000000 +
                       bs[4] as uint64 * 256*256*256 + bs[5] as uint64 * 256*256 + bs[6] as uint64 * 256 + bs[7] as uint64; ret as int == BEByteSeqToInt(bs);
{
    lemma_2toX();
    var ret := bs[0] as uint64 * 256*256*256*0x100000000 + bs[1] as uint64 * 256*256*0x100000000 + bs[2] as uint64 * 256*0x100000000 + bs[3] as uint64 * 0x100000000 +
      bs[4] as uint64 * 256*256*256 + bs[5] as uint64 * 256*256 + bs[6] as uint64 * 256 + bs[7] as uint64;

    var byteSeq := bs;

    calc {
        BEByteSeqToInt(bs);
        BEByteSeqToInt(bs[..|bs|-1]) * 256 + bs[|bs|-1] as int;
            { assert bs[..|bs|-1][..|bs[..|bs|-1]|-1] == bs[..|bs|-2]; }
        (BEByteSeqToInt(bs[..|bs|-2]) * 256 + bs[|bs|-2] as int) * 256 + bs[|bs|-1] as int;
            { assert bs[..|bs|-2][..|bs[..|bs|-2]|-1] == bs[..|bs|-3]; }
        ((BEByteSeqToInt(bs[..|bs|-3]) * 256 + bs[|bs|-3] as int) * 256 + bs[|bs|-2] as int) * 256 + bs[|bs|-1] as int;
            { assert bs[..|bs|-3][..|bs[..|bs|-3]|-1] == bs[..|bs|-4]; }
        (((BEByteSeqToInt(bs[..|bs|-4]) * 256 + bs[|bs|-4] as int) * 256 + bs[|bs|-3] as int) * 256 + bs[|bs|-2] as int) * 256 + bs[|bs|-1] as int;
            { assert bs[..|bs|-4][..|bs[..|bs|-4]|-1] == bs[..|bs|-5]; }
        ((((BEByteSeqToInt(bs[..|bs|-5]) * 256 + bs[|bs|-5] as int) * 256 + bs[|bs|-4] as int) * 256 + bs[|bs|-3] as int) * 256 + bs[|bs|-2] as int) * 256 + bs[|bs|-1] as int;
            { assert bs[..|bs|-5][..|bs[..|bs|-5]|-1] == bs[..|bs|-6]; }
        (((((BEByteSeqToInt(bs[..|bs|-6]) * 256 + bs[|bs|-6] as int) * 256 + bs[|bs|-5] as int) * 256 + bs[|bs|-4] as int) * 256 + bs[|bs|-3] as int) * 256 + bs[|bs|-2] as int) * 256 + bs[|bs|-1] as int;
            { assert bs[..|bs|-6][..|bs[..|bs|-6]|-1] == bs[..|bs|-7]; }
        ((((((BEByteSeqToInt(bs[..|bs|-7]) * 256 + bs[|bs|-7] as int) * 256 + bs[|bs|-6] as int) * 256 + bs[|bs|-5] as int) * 256 + bs[|bs|-4] as int) * 256 + bs[|bs|-3] as int) * 256 + bs[|bs|-2] as int) * 256 + bs[|bs|-1] as int;
        (((((((BEByteSeqToInt(bs[..|bs|-8]) * 256 + bs[|bs|-8] as int) * 256 + bs[|bs|-7] as int) * 256 + bs[|bs|-6] as int) * 256 + bs[|bs|-5] as int) * 256 + bs[|bs|-4] as int) * 256 + bs[|bs|-3] as int) * 256 + bs[|bs|-2] as int) * 256 + bs[|bs|-1] as int;
        ret as int;
    }
}

  function method BEByteSeqToUint64(bs:seq<byte>) : uint64
    requires |bs| == Uint64Size() as int;
    ensures 0 <= BEByteSeqToInt(bs) < 0x10000000000000000;    // Need for the cast on the next line
    ensures BEByteSeqToUint64(bs) == BEByteSeqToInt(bs) as uint64;
  {
    lemma_2toX();
    lemma_BEByteSeqToUint64_properties(bs);
    bs[0 as uint64] as uint64 * 256*256*256*0x100000000 + bs[1 as uint64] as uint64 * 256*256*0x100000000 + bs[2 as uint64] as uint64 * 256*0x100000000 + bs[3 as uint64] as uint64 * 0x100000000 +
    bs[4 as uint64] as uint64 * 256*256*256 + bs[5 as uint64] as uint64 * 256*256 + bs[6 as uint64] as uint64 * 256 + bs[7 as uint64] as uint64
  }

  function method BEByteSeqToUint32(bs:seq<byte>) : uint32
    requires |bs| == Uint32Size() as int;
    ensures 0 <= BEByteSeqToInt(bs) < 0x100000000;    // Need for the cast on the next line
    ensures BEByteSeqToUint32(bs) == BEByteSeqToInt(bs) as uint32;
  {
    lemma_2toX();
    lemma_BEByteSeqToUint32_properties(bs);
    bs[0 as uint32] as uint32 * 256*256*256 + bs[1 as uint32] as uint32 * 256*256 + bs[2 as uint32] as uint32 * 256 + bs[3 as uint32] as uint32
  }

  function method BEUintToSeqByte(v:int, width:int) : seq<byte>
    ensures width >= 0 && v >= 0 ==> |BEUintToSeqByte(v, width)| == width;
  {
    if width > 0 && v >= 0 then
      BEUintToSeqByte(v/0x100, width - 1) + [ (v % 0x100) as byte ]
    else
      []
  }


}

include "NativeTypes.dfy"
include "Bitcoin.dfy"
include "NativeTypesUtil.dfy"

module BitcoinDatatypes {
  import opened BlockchainTypes
  import opened Bitcoin
  import opened NativeTypes
	import opened NativeTypesUtil

  class BitcoinTxInImpl {

    var prevouthash : array<byte>;
    var prevoutn : uint32;
    var scriptSig : array<byte>;
    var nSequence : uint32;
    
    ghost var txIn : BitcoinTxIn;
    ghost var Repr : set<object>;

    predicate Valid()
      reads this, Repr;
    {
      this in Repr &&
      prevouthash in Repr &&
      scriptSig in Repr &&
      match txIn case BitcoinTxIn(prevout_hash, prevout_n, scriptsig, sequence) =>
      prevout_hash == prevouthash[..] &&
      |prevout_n| == Uint32Size() as int && BEByteSeqToUint32(prevout_n) == prevoutn &&
      scriptsig == scriptSig[..] &&
      |sequence| == Uint32Size() as int && BEByteSeqToUint32(sequence) == nSequence
    }
  }

  class BitcoinTxOutImpl {

    var nValue : uint64;
    var scriptPubKey : array<byte>;

    ghost var txOut : BitcoinTxOut;
    ghost var Repr : set<object>;

    predicate Valid()
      reads this, Repr;
    {
      this in Repr &&
      scriptPubKey in Repr &&
      match txOut case BitcoinTxOut(value, scriptpubkey) =>
      |value| == Uint64Size() as int && BEByteSeqToUint64(value) == nValue &&
      scriptpubkey == scriptPubKey[..]
    }
  }

  class BitcoinTransactionImpl {

    var nVersion : uint32;
    var vin : array<BitcoinTxInImpl>;
    var vout : array<BitcoinTxOutImpl>;
    var nLockTime : uint32;

    ghost var tx : BitcoinTransaction;
    ghost var Repr : set<object>;

    predicate Valid()
      reads this, Repr;
    {
      this in Repr &&
      vin in Repr && vout in Repr &&
      match tx case BitcoinTransaction(version, ins, outs, locktime) =>
      |version| == Uint32Size() as int && BEByteSeqToUint32(version) == nVersion &&
      vin.Length == |ins| && (forall i :: 0 <= i < vin.Length ==> vin[i] in Repr && vin[i].Repr <= Repr && vin[i].Valid() && vin[i].txIn == ins[i]) &&
      vout.Length == |outs| && (forall i :: 0 <= i < vout.Length ==> vout[i] in Repr && vout[i].Repr <= Repr && vout[i].Valid() && vout[i].txOut == outs[i]) &&
      |locktime| == Uint32Size() as int && BEByteSeqToUint32(locktime) == nLockTime
    }
  }

  class BitcoinBlockImpl {

    var nVersion : uint32;
    var hashPrevBlock : array<byte>;
    var hashMerkleRoot : array<byte>;
    var nTime : uint32;
    var nBits : uint32;
    var nNonce : uint32;
    var vtx : array<BitcoinTransactionImpl>;

    ghost var block : Block<Hash,BitcoinTransaction,BitcoinProof>;
    ghost var Repr : set<object>;

    predicate Valid()
      reads this, Repr, vtx;
      reads vtx[..];
    {
      this in Repr &&
      hashPrevBlock in Repr &&
      hashMerkleRoot in Repr &&
      vtx in Repr &&
      match block case Block(prevBlockHash, txs, proof) =>
      match proof case BitcoinProof(version, time, bits, nonce) =>
      |version| == Uint32Size() as int && BEByteSeqToUint32(version) == nVersion &&
      prevBlockHash == hashPrevBlock[..] &&
      merkle_tree_hash(txs) == hashMerkleRoot[..] &&
      |time| == Uint32Size() as int && BEByteSeqToUint32(time) == nTime &&
      |bits| == Uint32Size() as int && BEByteSeqToUint32(bits) == nBits &&
      |nonce| == Uint32Size() as int && BEByteSeqToUint32(nonce) == nNonce &&
      |txs| == vtx.Length  && forall i :: 0 <= i < vtx.Length ==> vtx[i] in Repr && vtx[i].Repr <= Repr && vtx[i].Valid() && txs[i] == vtx[i].tx
    }

  }

}

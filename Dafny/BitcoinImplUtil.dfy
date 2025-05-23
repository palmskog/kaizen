include "MathUtilImpl.dfy"
include "BlockchainImplUtil.dfy"
include "Bitcoin.dfy"
include "NativeTypes.dfy"

module {:extern "BitcoinImplUtilExt"} BitcoinImplUtilExt
{
  import opened BlockchainTypes
  import opened Bitcoin

  class {:extern "Util"} UtilExt
  {
    static method {:extern "VAFImpl"} VAFImplExt(p:BitcoinProof, bc:BlockChain<Hash,BitcoinTransaction,BitcoinProof>, txs:TxPool<BitcoinTransaction>) returns (vb:bool)
      ensures vb == VAF(p,bc,txs);

    static method {:extern "FCRImpl"} FCRImplExt(b1:BlockChain<Hash,BitcoinTransaction,BitcoinProof>, b2:BlockChain<Hash,BitcoinTransaction,BitcoinProof>) returns (b:bool)
      ensures b == FCR(b1,b2);

    static method {:extern "GenProofImpl"} GenProofImplExt(a:Address, bc:BlockChain<Hash,Transaction,VProof>, txs:TxPool<Transaction>, ts:Timestamp) returns (o:Option<(TxPool<Transaction>,VProof)>)
      ensures o == genProof(a, bc, txs, ts);

    static method {:extern "TxValidImpl"} TxValidImplExt(t:BitcoinTransaction, bc:BlockChain<Hash,BitcoinTransaction,BitcoinProof>) returns (b:bool)
      ensures b == txValid(t, bc);
  }
}

module {:extern "BitcoinImplUtil"} BitcoinImplUtil refines BlockchainImplUtil {
  import opened B = Bitcoin
  import BitcoinImplUtilExt
  import opened MathUtilImpl
  import opened NativeTypes
  import opened NativeTypesUtil

  class Util {

    static method TpExtendImpl(tp: Collections.Node?<Transaction>, bt:BlockTree<Hash,Transaction,VProof>, tx:Transaction) returns (tp': Collections.Node?<Transaction>)
      ensures Collections.NodeSeq(tp') == tpExtend(Collections.NodeSeq(tp), bt, tx);
    {
      if tp != null {
        var contains := Collections.Node.Contains(tp, tx);
        if !contains {
          tp' := new Collections.Node.Insert(tx, tp);
        } else {
          tp' := tp;
        }
      } else {
        tp' := new Collections.Node.Singleton(tx);
      }
    }

    static method TpExtendImplTreeMap(tp: Collections.Node?<Transaction>, bt:OSU.TreeMap<Block<Hash,Transaction,VProof>>, tx:Transaction) returns (tp': Collections.Node?<Transaction>)
      ensures Collections.NodeSeq(tp') == tpExtend(Collections.NodeSeq(tp), bt.kvmap, tx);
    {
      if tp != null {
        var contains := Collections.Node.Contains(tp, tx);
        if !contains {
          tp' := new Collections.Node.Insert(tx, tp);
        } else {
          tp' := tp;
        }
      } else {
        tp' := new Collections.Node.Singleton(tx);
      }
    }

    static method HashdataBitcoinTxInImpl(ti:BitcoinTxIn) returns (d:seq<byte>)
      ensures d == hashdataBitcoinTxIn(ti);
    {
      match ti
        case BitcoinTxIn(prevout_hash, prevout_n, scriptsig, sequence) =>
          d := prevout_hash + prevout_n + scriptsig + sequence;
    }

    static method FoldHashdataBitcoinTxInImpl(ins:seq<BitcoinTxIn>) returns (d:seq<byte>)
      ensures d == foldr_seq((i, s) => hashdataBitcoinTxIn(i) + s, [], ins);
    {
      d := [];
      var i := |ins|;
      while i > 0
        invariant 0 <= i <= |ins|;
        invariant 0 <= i <= |ins| ==> (d == foldr_seq((i, s) => hashdataBitcoinTxIn(i) + s, [], ins[i..]));
        decreases i;
      {
        var d' := HashdataBitcoinTxInImpl(ins[i-1]);
        d := d' + d;
        i := i - 1;
      }
    }

    static method FoldHashdataBitcoinTxInImpl_rec(ins:seq<BitcoinTxIn>) returns (d:seq<byte>)
      ensures d == foldr_seq((i, s) => hashdataBitcoinTxIn(i) + s, [], ins);
    {
      if |ins| == 0 {
        d := [];
      } else {
        var i := HashdataBitcoinTxInImpl(ins[0]);
        var d' := FoldHashdataBitcoinTxInImpl_rec(ins[1..]);
        d := i + d';
      }
    }

    static method HashdataBitcoinTxOutImpl(ti:BitcoinTxOut) returns (d:seq<byte>)
      ensures d == hashdataBitcoinTxOut(ti);
    {
      match ti
        case BitcoinTxOut(value, scriptpubkey) =>
          d := value + scriptpubkey;
    }

    static method FoldHashdataBitcoinTxOutImpl(outs:seq<BitcoinTxOut>) returns (d:seq<byte>)
      ensures d == foldr_seq((o, s) => hashdataBitcoinTxOut(o) + s, [], outs);
    {
      d := [];
      var i := |outs|;
      while i > 0
        invariant 0 <= i <= |outs|;
        invariant 0 <= i <= |outs| ==> (d == foldr_seq((o, s) => hashdataBitcoinTxOut(o) + s, [], outs[i..]));
        decreases i;
      {
        var d' := HashdataBitcoinTxOutImpl(outs[i-1]);
        d := d' + d;
        i := i - 1;
      }
    }

    static method FoldHashdataBitcoinTxOutImpl_rec(outs:seq<BitcoinTxOut>) returns (d:seq<byte>)
      ensures d == foldr_seq((o, s) => hashdataBitcoinTxOut(o) + s, [], outs);
    {
      if |outs| == 0 {
        d := [];
      } else {
        var i := HashdataBitcoinTxOutImpl(outs[0]);
        var d' := FoldHashdataBitcoinTxOutImpl_rec(outs[1..]);
        d := i + d';
      }
    }

    // FIXME: replace with real implementation of FCR once fully defined
    static method FCRImpl(b1:BlockChain<Hash,Transaction,VProof>, b2:BlockChain<Hash,Transaction,VProof>) returns (b:bool)
      ensures b == FCR(b1,b2);
    {
      b := BitcoinImplUtilExt.UtilExt.FCRImplExt(b1, b2);
    }

    static method VAFImpl(p:VProof, bc:BlockChain<Hash,Transaction,VProof>, txs:TxPool<Transaction>) returns (vb:bool)
      ensures vb <==> VAF(p, bc, txs);
    {
      vb := BitcoinImplUtilExt.UtilExt.VAFImplExt(p, bc, txs);
    }

    static method GenProofImpl(a:Address, bc:BlockChain<Hash,Transaction,VProof>, txs:TxPool<Transaction>, ts:Timestamp) returns (o:Option<(TxPool<Transaction>,VProof)>)
      ensures o == genProof(a, bc, txs, ts);
    {
      o := BitcoinImplUtilExt.UtilExt.GenProofImplExt(a, bc, txs, ts);
    }

    static method TxValidImpl(t:Transaction, bc:BlockChain<Hash,Transaction,VProof>) returns (b:bool)
      ensures |bc| == 0 ==> b;
      ensures b == txValid(t, bc);
    {
      if |bc| == 0 {
        b := true;
      } else {
        b := BitcoinImplUtilExt.UtilExt.TxValidImplExt(t, bc);
      }
    }

    static method HashdataTImpl(t:Transaction) returns (d:seq<byte>)
      ensures d == hashdataT(t);
    {
      match t
        case BitcoinTransaction(version, ins, outs, locktime) =>
          var dIn := FoldHashdataBitcoinTxInImpl(ins);
          var dOut := FoldHashdataBitcoinTxOutImpl(outs);
          d := version + BEUintToSeqByte(|ins|, 1) + dIn + BEUintToSeqByte(|outs|, 1) + dOut + locktime;
    }

    static method HashTImpl(t:Transaction) returns (h : Hash)
      ensures h == hashT(t);
    {
      var d := HashdataTImpl(t);
      h := BitcoinHash(d);
    }

    static method MerkleTreePassImpl(hs:seq<Hash>) returns (hs':seq<Hash>)
      ensures hs' == merkle_tree_pass(hs);    
    {
      if |hs| == 0 {
        hs' := [];
      } else if |hs| == 1 {
        var h := BitcoinHash(hs[0] + hs[0]);
        hs' := [h];
      } else {
        var hs'' := MerkleTreePassImpl(hs[2..]);
        var h := BitcoinHash(hs[0] + hs[1]);
        hs' := [h] + hs'';
      }
    }

    static method MapHashTImpl(txs:seq<Transaction>) returns (hs:seq<Hash>)
      ensures hs == map_seq(hashT, txs);
    {
      var hs' := [];
      var i := 0;
      ghost var elts := [];
      ghost var rem := txs;
      assert elts + rem == txs;
      while i < |txs|
        invariant 0 <= i <= |txs|;
        invariant elts + rem == txs;
        invariant hs' == map_seq(hashT, elts);
        invariant elts == txs[..|elts|];
        invariant |elts| == i;
      {
        elts := elts + [txs[i]];
        rem := rem[1..];
        var h := HashTImpl(txs[i]);
        hs' := hs' + [h];
        i := i + 1;
      }
      assert |elts| == |txs|;
      assert elts == txs;
      hs := hs';
    }

    static method MerkleTreeHashLoopImpl(hs:seq<Hash>, k:nat) returns (h:Hash)
      ensures h == merkle_tree_hash_loop(hs, k);
      decreases k;
    {
      if k == 0 {
        if |hs| == 1 {
          h := hs[0];
        } else {
          h := [];
        }
      } else {
        var hs' := MerkleTreePassImpl(hs);
        h := MerkleTreeHashLoopImpl(hs', k - 1);
      }
    }

    static method MerkleTreeHashImpl(txs:seq<Transaction>) returns (d:Hash)
      ensures d == merkle_tree_hash(txs);
    {
      var hs := MapHashTImpl(txs);
      var passes := CeilLog2Impl(|hs|);
      d := MerkleTreeHashLoopImpl(hs, passes);
    }

    static method HashdataBImpl(b:Block<Hash,Transaction,VProof>) returns (d:seq<byte>)
      ensures d == hashdataB(b);
    {
      match b
        case Block(prevBlockHash, txs, proof) =>
          match proof
            case BitcoinProof(version, time, bits, nonce) =>
              var dtxs := MerkleTreeHashImpl(txs);
              d := version + prevBlockHash + dtxs + time + bits + nonce;
    }

    static method HashBImpl(b:Block<Hash,Transaction,VProof>) returns (h : Hash)
      ensures h == hashB(b);
    {
      if b == GenesisBlock() {
        match b
          case Block(prevBlockHash, txs, proof) =>
            h := prevBlockHash;
      } else {
        var d := HashdataBImpl(b);
        h := BitcoinHash(d);
      }
    }

  }
}

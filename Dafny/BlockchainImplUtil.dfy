include "LinkedList.dfy"
include "Blockchain.dfy"
include "SeqUtil.dfy"
include "OrderedSeqUtil.dfy"

abstract module BlockchainImplUtil {
  import Collections
  import opened SeqUtil
  import opened SeqUtilImpl
  import opened BlockchainTypes
  import opened B : Blockchain

  class Util {

    static method TxValidImpl(t:Transaction, bc:BlockChain<Hash,Transaction,VProof>) returns (b:bool)
      ensures b <==> txValid(t, bc);

    static method HashTImpl(t:Transaction) returns (h : Hash)
      ensures h == hashT(t);

    static method HashBImpl(b:Block<Hash,Transaction,VProof>) returns (h : Hash)
      ensures h == hashB(b);

    static method FCRImpl(b1:BlockChain<Hash,Transaction,VProof>, b2:BlockChain<Hash,Transaction,VProof>) returns (b:bool)
      ensures b <==> FCR(b1,b2);

    static method GenProofImpl(a:Address, bc:BlockChain<Hash,Transaction,VProof>, txs:TxPool<Transaction>, ts:Timestamp) returns (o:Option<(TxPool<Transaction>,VProof)>)
      ensures o == genProof(a, bc, txs, ts);

    static method VAFImpl(p:VProof, bc:BlockChain<Hash,Transaction,VProof>, txs:TxPool<Transaction>) returns (vb:bool)
      ensures vb <==> VAF(p, bc, txs);

    static method TpExtendImpl(tp: Collections.Node?<Transaction>, bt:BlockTree<Hash,Transaction,VProof>, tx:Transaction) returns (tp': Collections.Node?<Transaction>)
      requires tp != null ==> tp.Valid();
      ensures tp' != null ==> tp'.Valid() && fresh(tp'.Repr - Collections.NodeRepr(old(tp)));
      ensures Collections.NodeSeq(tp') == tpExtend(Collections.NodeSeq(old(tp)), bt, tx);

    static method TpExtendImplTreeMap(tp: Collections.Node?<Transaction>, bt:OSU.TreeMap<Block<Hash,Transaction,VProof>>, tx:Transaction) returns (tp': Collections.Node?<Transaction>)
      requires tp != null ==> tp.Valid();
      requires bt.Valid();
      ensures tp' != null ==> tp'.Valid() && fresh(tp'.Repr - Collections.NodeRepr(old(tp)));
      ensures Collections.NodeSeq(tp') == tpExtend(Collections.NodeSeq(old(tp)), bt.kvmap, tx);
      ensures tp' == null ==> old(tp) == null;

    static method BtExtendImpl(bt:BlockTree<Hash,Transaction,VProof>, b:Block<Hash,Transaction,VProof>) returns (ebt:BlockTree<Hash,Transaction,VProof>)
      ensures ebt == btExtend(bt, b);
    {
      var h := HashBImpl(b);
      assert h == hashB(b);
      if h !in bt {
        ebt := bt[h := b];
      } else {
        ebt := bt;
      }
    }

    static method BtExtendImplTreeMap(bt:OSU.TreeMap<Block<Hash,Transaction,VProof>>, b:Block<Hash,Transaction,VProof>)
      modifies bt.Repr;
      requires bt.Valid();
      ensures bt.Valid();
      ensures bt.kvmap == btExtend(old(bt.kvmap), b);
      ensures fresh(bt.Repr - old(bt.Repr));
    {
      var h := HashBImpl(b);
      var c := bt.ContainsKey(h);
      if !c {
        bt.Put(h, b);
      }
    }

    static method PoolTxValidSeqImpl(pool: Collections.Node<Transaction>, bc:BlockChain<Hash,Transaction,VProof>) returns (vpool:TxPool<Transaction>)
      requires pool.Valid();
      ensures pool.Valid();
      ensures vpool == pool_txValid(bc, pool.list);
    {
      var vpl := [];
      var current := pool;
      ghost var rem := pool.list;
      ghost var elts := [];
      while (current != null)
        invariant if current != null then current.Valid() else true;
        invariant rem == Collections.NodeSeq(current);
        invariant elts + rem == pool.list;
        invariant vpl == filter_seq(t => txValid(t, bc), elts);
        decreases if current != null then |current.list| else -1;
      {
        var txv := TxValidImpl(current.elem, bc);
        if txv {
          vpl := vpl + [current.elem];
        }
        filter_seq_cat(t => txValid(t, bc), elts, [current.elem]);
        elts := elts + [current.elem];
        current := current.next;
        rem := Collections.NodeSeq(current);
      }
      assert elts == pool.list;
      vpool := vpl;
    }

    static method PoolTxValidImpl(pool: Collections.Node<Transaction>, bc:BlockChain<Hash,Transaction,VProof>) returns (vpool:Collections.Node?<Transaction>)
      modifies pool.Repr;
      requires pool.Valid();
      ensures vpool != null ==> vpool.Valid() && vpool.Repr <= old(pool.Repr);
      ensures Collections.NodeSeq(vpool) == pool_txValid(bc, old(pool.list));
    {
      var current := Collections.Node<Transaction>.Reverse(pool);
      ghost var revlist := current.list;
      assert |revlist| == |old(pool.list)|;
      assert forall i :: 0 <= i < |revlist| ==> revlist[i] == old(pool.list)[|old(pool.list)|-1-i];
      assert current.Repr <= old(pool.Repr);
      var poolTxValid : Collections.Node?<Transaction> := null;
      ghost var elts := [];
      ghost var revelts := [];
      ghost var rem := revlist;
      assert elts + rem == revlist;
      while (current != null)
        invariant |revelts| == |elts|;
        invariant poolTxValid != null ==>
          poolTxValid.Valid() &&
          poolTxValid.Repr <= old(pool.Repr);
          invariant current != null ==>
            current.Valid() &&
            current in old(pool.Repr) && current.Repr <= old(pool.Repr) &&
            (poolTxValid != null ==> current.Repr !! poolTxValid.Repr);
            invariant elts + rem == revlist;
            invariant elts == revlist[..|elts|];
            invariant forall i :: 0 <= i < |elts| ==> elts[i] == old(pool.list)[|old(pool.list)|-1-i] && elts[i] == revelts[|elts|-1-i];
            invariant rem == Collections.NodeSeq(current);
            invariant Collections.NodeSeq(poolTxValid) == pool_txValid(bc, revelts);
            decreases if current != null then |current.list| else -1;
      {
        elts := elts + [current.elem];
        revelts := [current.elem] + revelts;
        var nx := current.next;
        var txValid := TxValidImpl(current.elem, bc);
        if txValid {
          current.next := poolTxValid;
          if poolTxValid != null {
            current.size := 1 + poolTxValid.size;
            current.Repr := {current} + poolTxValid.Repr;
            current.list := [current.elem] + poolTxValid.list;
          } else {
            current.size := 1;
            current.Repr := {current};
            current.list := [current.elem];
          }
          poolTxValid := current;
        }
        current := nx;
        rem := Collections.NodeSeq(current);
      }
      assert poolTxValid != null ==> poolTxValid.Valid();
      assert |elts| == |revelts|;
      assert |revlist| == |old(pool.list)|;
      assert elts == revlist;
      Collections.RevEqAll(revlist, old(pool.list), revelts);
      assert Collections.NodeSeq(poolTxValid) == pool_txValid(bc, old(pool.list));
      vpool := poolTxValid;
    }

    static method PoolHashTImpl(pool:Collections.Node?<Transaction>) returns (hashes:seq<Hash>)
      requires pool != null ==> pool.Valid();
      ensures hashes == pool_hashT(Collections.NodeSeq(pool));
    {
      var n := pool;
      var hs := [];
      ghost var rem := Collections.NodeSeq(n);
      ghost var elts := [];
      assert elts + rem == Collections.NodeSeq(pool);
      while (n != null)
        invariant if n != null then n.Valid() else true;
        invariant rem == Collections.NodeSeq(n);
        invariant elts + rem == Collections.NodeSeq(pool);
        invariant hs == pool_hashT(elts);
        decreases |rem|;
      {
        var h := HashTImpl(n.elem);
        //hashTAppend(hs, elts, h, n.elem);
        hs := hs + [h];
        elts := elts + [n.elem];
        n := n.next;
        rem := Collections.NodeSeq(n);
      }
      assert elts == Collections.NodeSeq(pool);
      hashes := hs;
    }

    static method GetDataMsgPacketsImpl(n:Address, from:Address, hs:seq<Hash>) returns (ts: ToSend)
      ensures ts == getDataMsgPackets(n, from, hs);
    {
      ts := [];
      var i := 0;
      while( i < |hs|)
        invariant i <= |hs| 
        invariant 0 <= i <= |hs| ==> ts == getDataMsgPackets(n, from, hs[0..i])
        decreases |hs| - i
      {
        var p := Packet(n, from, GetDataMsg(hs[i]));
        ts := ts + [p];
        i := i + 1;
      }
    }

    static method GetDataMsgPacketsImpl_rec(n:Address, from:Address, hs:seq<Hash>) returns (ts:ToSend)
      ensures ts == getDataMsgPackets(n, from, hs);
    {
      if |hs| == 0 {
        ts := [];
      } else {
        var ts' := GetDataMsgPacketsImpl_rec(n, from, hs[1..]);
        var p := Packet(n, from, GetDataMsg(hs[0]));
        ts := [p] + ts';
      }
    }

    static method ConnectMsgPacketsImpl(n:Address, ps:peers_t) returns (ts:ToSend)
      ensures ts == connectMsgPackets(n, ps);
    {
      ts := [];
      var i := 0;
      while i < |ps|
        invariant i <= |ps|;
        invariant 0 <= i <= |ps| ==> ts == connectMsgPackets(n, ps[0..i]);
        decreases |ps| - i;
      {
        var p := Packet(n, ps[i], ConnectMsg);
        ts := ts + [p];
        i := i + 1;
      }
    }

    static method ConnectMsgPacketsImpl_rec(n:Address, ps:peers_t) returns (ts:ToSend)
      ensures ts == connectMsgPackets(n, ps);
    {
      if |ps| == 0 {
        ts := [];
      } else {
        var ts' := ConnectMsgPacketsImpl_rec(n, ps[1..]);
        var p := Packet(n, ps[0], ConnectMsg);
        ts := [p] + ts';
      }
    }

    static method EmitBroadcastImpl(a:Address, peers:Collections.Node<Address>, msg:Message, upper:int) returns (ts:ToSend)
      requires peers.Valid();
      requires 0 <= upper <= |peers.list|;
      ensures ts == emitBroadcast(a, peers.list[..upper], msg);
    {
      var ps := [];
      ghost var rem := peers.list;
      ghost var elts := [];
      var n := peers;
      assert elts + rem == peers.list;
      var k := 0;
      while (n != null && k < upper)
        invariant 0 <= k <= upper;
        invariant if n != null then n.Valid() else true;
        invariant rem == Collections.NodeSeq(n);
        invariant elts + rem == peers.list;
        invariant elts == peers.list[..k];
        invariant ps == emitBroadcast(a, elts, msg);
        decreases |rem|;
      {
        var p := Packet(a, n.elem, msg);
        //emitBroadcastEqAppend(a, msg, ps, elts, p, n.elem);
        ps := ps + [p];
        elts := elts + [n.elem];
        n := n.next;
        rem := Collections.NodeSeq(n);
        k := k + 1;
      }
      assert elts == peers.list[..upper];
      ts := ps;
    }

    static method SeqExcludeListImpl<T>(n:Collections.Node<T>, s:seq<T>) returns (xs:seq<T>)
      requires n.Valid();
      ensures xs == seq_exclude(s, n.list);
    {
      xs := [];
      var i := |s|;
      while i > 0
        invariant 0 <= i <= |s|;
        invariant 0 <= i <= |s| ==> xs == seq_exclude(s[i..], n.list);
        decreases i;
      {
        var contains := Collections.Node.Contains(n, s[i-1]);
        if !contains {
          xs := [s[i-1]] + xs;
        }
        i := i - 1;
      }
    }

    static method SeqExcludeListImpl_rec<T>(n:Collections.Node<T>, s:seq<T>) returns (xs:seq<T>)
      requires n.Valid();
      ensures xs == seq_exclude(s, n.list);
    {
      if |s| == 0 {
        xs := [];
      } else {
        var contains := Collections.Node.Contains(n, s[0]);
        if contains {
          xs := SeqExcludeListImpl(n, s[1..]);
        } else {
          var xs' := SeqExcludeListImpl_rec(n, s[1..]);
          xs := [s[0]] + xs';
        }
      }
    }

    static method GetBlockImpl(bt:BlockTree<Hash,Transaction,VProof>, k:Hash) returns (b:Block<Hash,Transaction,VProof>)
      ensures b == get_block(bt, k);
    {
      if k in bt {
        b := bt[k];
      } else {
        b := GenesisBlock();
      }
    }

    static method GetBlockImplTreeMap(bt:OSU.TreeMap<Block<Hash,Transaction,VProof>>, k:Hash) returns (b:Block<Hash,Transaction,VProof>)
      requires bt.Valid();
      ensures b == get_block(bt.kvmap, k);
    {
      var c := bt.ContainsKey(k);
      if c {
        b := bt.Get(k);
      } else {
        b := GenesisBlock();
      }
    }

    static method PoolHashTEqImpl(n:Collections.Node?<Transaction>, h:Hash) returns (s:TxPool<Transaction>)
      requires n != null ==> n.Valid();
      ensures s == pool_hashT_eq(h, Collections.NodeSeq(n))
    {
      s := [];
      ghost var elts := [];
      ghost var rem := Collections.NodeSeq(n);
      var current := n;
      while (current != null)
        invariant current != null ==> current.Valid();
        invariant elts + rem == Collections.NodeSeq(n);
        invariant rem == Collections.NodeSeq(current);
        invariant s == filter_seq(t => hashT(t) == h, elts);
        decreases if current != null then |current.list| else -1;
      {
        ghost var oldelts := elts;
        elts := elts + [current.elem];
        var ht := HashTImpl(current.elem);
        if ht == h {
          s := s + [current.elem];
        }
        filter_seq_cat(t => hashT(t) == h, oldelts, [current.elem]);
        current := current.next;
        rem := Collections.NodeSeq(current);
      }
      assert elts == Collections.NodeSeq(n);
    }

    static method GoodChainImpl(bc:BlockChain<Hash,Transaction,VProof>) returns (b:bool)
      ensures b <==> good_chain(bc);
    {
      if |bc| == 0 {
        b := false;
      } else {
        var gb := GenesisBlock();
        b := bc[0] == gb;
      }
    }

    static method AllTxValidImpl(txs:TxPool<Transaction>, bc:BlockChain<Hash,Transaction,VProof>) returns (b: bool)
      ensures b == all_seq(t => txValid(t, bc), txs);
    {
      b := true;
      var i := |txs|;
      while i > 0
        invariant 0 <= i <= |txs|;
        invariant 0 <= i <= |txs| ==> (b == all_seq(t => txValid(t, bc), txs[i..]));
        decreases i;
      {
        var t := TxValidImpl(txs[i-1], bc);
        b := t && b;
        i := i - 1;
      }
    }

    static method AllTxValidImpl_rec(txs:TxPool<Transaction>, bc:BlockChain<Hash,Transaction,VProof>) returns (b: bool)
      ensures b == all_seq(t => txValid(t, bc), txs);
    {
      if |txs| == 0 {
        b := true;
      } else {
        var t := TxValidImpl(txs[0], bc);
        var a := AllTxValidImpl_rec(txs[1..], bc);
        b := t && a;
      }
    }

    static method ValidChain'Impl(bc:BlockChain<Hash,Transaction,VProof>, prefix:BlockChain<Hash,Transaction,VProof>) returns (b:bool)
      ensures b <==> valid_chain'(bc, prefix);
    {
      if |bc| == 0 {
        b := true;
      } else {
        match bc[0]
          case Block(ph, txs, pr) =>
            var v := VAFImpl(pr, prefix, txs);
            var a := AllTxValidImpl(txs, prefix);
            var t := ValidChain'Impl(bc[1..], prefix + [bc[0]]);
            b := v && a && t;
      }
    }

    static method ValidChainImpl(bc:BlockChain<Hash,Transaction,VProof>) returns (b:bool)
      ensures b <==> valid_chain(bc);
    {
      b := ValidChain'Impl(bc, []);
    }

    static method ComputeChain'Impl(bt:BlockTree<Hash,Transaction,VProof>, b:Block<Hash,Transaction,VProof>, remaining:seq<Hash>, n:int) returns (bc:BlockChain<Hash,Transaction,VProof>)
      requires n >= 0;
      ensures bc == compute_chain'(bt, b, remaining, n);
      decreases n;
    {
      var hash := HashBImpl(b);
      if hash in remaining {
        if n == 0 {
          bc := [];
        } else {
          match b
            case Block(ph, txs, pr) =>
              if ph in bt {
                var rest := RemoveImpl(hash, remaining);
                var prev := bt[ph];
                var nbt := RemoveMapImpl(bt, hash);
                var n' := n-1;
                var cc := ComputeChain'Impl(nbt, prev, rest, n');
                bc := cc + [b];
              } else {
                bc := [b];
              }
        }
      } else {
        bc := [];
      }
    }

    static method ComputeChain'ImplTreeMap(bt:OSU.TreeMap<Block<Hash,Transaction,VProof>>, b:Block<Hash,Transaction,VProof>, remaining:seq<Hash>, n:int) returns (bc:BlockChain<Hash,Transaction,VProof>)
      modifies bt.Repr;
      requires bt.Valid();
      requires n >= 0;
      ensures bc == compute_chain'(old(bt.kvmap), b, remaining, n);
      decreases n;
    {
      var hash := HashBImpl(b);
      if hash in remaining {
        if n == 0 {
          bc := [];
        } else {
          match b
            case Block(ph, txs, pr) =>
              var cph := bt.ContainsKey(ph);
              if cph {
                var rest := RemoveImpl(hash, remaining);
                var prev := bt.Get(ph);
                var ch := bt.ContainsKey(hash);
                if ch {
                  bt.Remove(hash);
                }
                assert bt.kvmap == remove_map(old(bt.kvmap), hash);
                var n' := n-1;
                var cc := ComputeChain'ImplTreeMap(bt, prev, rest, n');
                bc := cc + [b];
              } else {
                bc := [b];
              }
        }
      } else {
        bc := [];
      }
    }

    static method ComputeChainImpl(bt:BlockTree<Hash,Transaction,VProof>, b:Block<Hash,Transaction,VProof>)
      returns (bc:BlockChain<Hash,Transaction,VProof>)
      ensures bc == compute_chain(bt, b);
    {
      var dom := DomainImpl(bt);
      var keys := OSU.OrderedSetToSeqImpl(dom);
      bc := ComputeChain'Impl(bt, b, keys, |keys|);
    }

    static method ComputeChainImplTreeMap(bt:OSU.TreeMap<Block<Hash,Transaction,VProof>>, b:Block<Hash,Transaction,VProof>) returns (bc:BlockChain<Hash,Transaction,VProof>)
      requires bt.Valid();
      ensures bc == compute_chain(bt.kvmap, b);
    {
      var dom := bt.KeySet();
      var keys := OSU.OrderedSetToSeqImpl(dom);
      var bt' := OSU.TreeMap.From(bt);
      bc := ComputeChain'ImplTreeMap(bt', b, keys, |keys|);
    }

    static method TakeBetterBCImpl(bc2:BlockChain<Hash,Transaction,VProof>, bc1:BlockChain<Hash,Transaction,VProof>) returns (bc:BlockChain<Hash,Transaction,VProof>)
      ensures bc == take_better_bc(bc2, bc1);
    {
      var gc := GoodChainImpl(bc2);
      var tvc := ValidChainImpl(bc2);
      var fcr := FCRImpl(bc2, bc1);
      if gc && tvc && fcr {
        bc := bc2;
      } else {
        bc := bc1;
      }
    }

    static method FoldrTakeBetterBCImpl(unit:BlockChain<Hash,Transaction,VProof>, curr:seq<BlockChain<Hash,Transaction,VProof>>)
      returns (bc:BlockChain<Hash,Transaction,VProof>)
      ensures bc == foldr_seq(take_better_bc, unit, curr);
    {
      if |curr| == 0 {
        bc := unit;
      } else {
        var ftb := FoldrTakeBetterBCImpl(unit, curr[1..]);
        bc := TakeBetterBCImpl(curr[0], ftb);
      }
    }

    static method AllBlocksAuxImpl(s:seq<Hash>, bt:BlockTree<Hash,Transaction,VProof>) returns (bc:BlockChain<Hash,Transaction,VProof>)
      ensures bc == map_seq(k => get_block(bt, k), s);
    {
      bc := [];
      var i := |s|;
      while i > 0
        invariant 0 <= i <= |s|;
        invariant 0 <= i <= |s| ==> (bc == map_seq(k => get_block(bt, k), s[i..]));
        decreases i;
    {
      var gb := GetBlockImpl(bt, s[i-1]);
      bc := [gb] + bc;
      i := i - 1;
      }
    }

    static method AllBlocksAuxImpl_rec(s:seq<Hash>, bt:BlockTree<Hash,Transaction,VProof>) returns (bc:BlockChain<Hash,Transaction,VProof>)
      ensures bc == map_seq(k => get_block(bt, k), s);
    {
      if |s| == 0 {
        bc := [];
      } else {
        var gb := GetBlockImpl(bt, s[0]);
        var ab := AllBlocksAuxImpl_rec(s[1..], bt);
        bc := [gb] + ab;
      }
    }

    static method AllBlocksAuxImplTreeMap(s:seq<Hash>, bt:OSU.TreeMap<Block<Hash,Transaction,VProof>>) returns (bc:BlockChain<Hash,Transaction,VProof>)
      requires bt.Valid();
      ensures bc == all_blocks_aux(bt.kvmap, s);
    {
      bc := [];
      var i := |s|;
      while i > 0
        invariant 0 <= i <= |s|;
        invariant 0 <= i <= |s| ==> bc == all_blocks_aux(bt.kvmap, s[i..]);
        decreases i;
      {
        var gb := GetBlockImplTreeMap(bt, s[i-1]);
        bc := [gb] + bc;
        i := i - 1;
      }
    }

    static method AllBlocksAuxImplTreeMap_rec(s:seq<Hash>, bt:OSU.TreeMap<Block<Hash,Transaction,VProof>>) returns (bc:BlockChain<Hash,Transaction,VProof>)
      requires bt.Valid();
      ensures bc == all_blocks_aux(bt.kvmap, s);
    {
      if |s| == 0 {
        bc := [];
      } else {
        var gb := GetBlockImplTreeMap(bt, s[0]);
        var ab := AllBlocksAuxImplTreeMap_rec(s[1..], bt);
        bc := [gb] + ab;
      }
    }

    static method AllBlocksImpl(bt:BlockTree<Hash,Transaction,VProof>) returns (bc:BlockChain<Hash,Transaction,VProof>)
      ensures bc == all_blocks(bt);
    {
      var dom := DomainImpl(bt);
      var keys := OSU.OrderedSetToSeqImpl(dom);
      bc := AllBlocksAuxImpl(keys, bt);
    }

    static method AllBlocksImplTreeMap(bt:OSU.TreeMap<Block<Hash,Transaction,VProof>>) returns (bc:BlockChain<Hash,Transaction,VProof>)
      requires bt.Valid();
      ensures bc == all_blocks(bt.kvmap);
    {
      var dom := bt.KeySet();
      var keys := OSU.OrderedSetToSeqImpl(dom);
      bc := AllBlocksAuxImplTreeMap(keys, bt);
    }

    static method AllChainsAuxImpl(bt:BlockTree<Hash,Transaction,VProof>, bc:BlockChain<Hash,Transaction,VProof>) returns (sbc:seq<BlockChain<Hash,Transaction,VProof>>)
    ensures sbc == map_seq(b => compute_chain(bt, b), bc);
    {
      sbc := [];
      var i := |bc|;
      while i > 0
        invariant 0 <= i <= |bc|;
        invariant 0 <= i <= |bc| ==> (sbc == map_seq(b => compute_chain(bt, b), bc[i..]));
        decreases i;
      {
        var cc := ComputeChainImpl(bt, bc[i-1]);
        sbc := [cc] + sbc;
        i := i - 1;
      }
    }

    static method AllChainsAuxImpl_rec(bt:BlockTree<Hash,Transaction,VProof>, bc:BlockChain<Hash,Transaction,VProof>)
      returns (sbc:seq<BlockChain<Hash,Transaction,VProof>>)
      ensures sbc == map_seq(b => compute_chain(bt, b), bc);
    {
      if |bc| == 0 {
        sbc := [];
      } else {
        var cc := ComputeChainImpl(bt, bc[0]);
        var aca := AllChainsAuxImpl_rec(bt, bc[1..]);
        sbc := [cc] + aca;
      }
    }

    static method AllChainsAuxImplTreeMap(bt:OSU.TreeMap<Block<Hash,Transaction,VProof>>, bc:BlockChain<Hash,Transaction,VProof>)
      returns (sbc:seq<BlockChain<Hash,Transaction,VProof>>)
      requires bt.Valid();
      ensures sbc == all_chains_aux(bt.kvmap, bc);
    {
      sbc := [];
      var i := |bc|;
      while i > 0
        invariant 0 <= i <= |bc|;
        invariant 0 <= i <= |bc| ==> sbc == all_chains_aux(bt.kvmap, bc[i..]);
        decreases i;
      {
        var cc := ComputeChainImplTreeMap(bt, bc[i-1]);
        sbc := [cc] + sbc;
        i := i - 1;
      }
    }

    static method AllChainsAuxImplTreeMap_rec(bt:OSU.TreeMap<Block<Hash,Transaction,VProof>>, bc:BlockChain<Hash,Transaction,VProof>)
      returns (sbc:seq<BlockChain<Hash,Transaction,VProof>>)
      requires bt.Valid();
      ensures sbc == all_chains_aux(bt.kvmap, bc);
    {
      if |bc| == 0 {
        sbc := [];
      } else {
        var cc := ComputeChainImplTreeMap(bt, bc[0]);
        var aca := AllChainsAuxImplTreeMap_rec(bt, bc[1..]);
        sbc := [cc] + aca;
      }
    }

    static method AllChainsImpl(bt:BlockTree<Hash,Transaction,VProof>) returns (sbc:seq<BlockChain<Hash,Transaction,VProof>>)
      ensures sbc == all_chains(bt)
    {
      var bc := AllBlocksImpl(bt);
      sbc := AllChainsAuxImpl(bt, bc);
    }

    static method AllChainsImplTreeMap(bt:OSU.TreeMap<Block<Hash,Transaction,VProof>>) returns (sbc:seq<BlockChain<Hash,Transaction,VProof>>)
      requires bt.Valid();
      ensures sbc == all_chains(bt.kvmap)
    {
      var bc := AllBlocksImplTreeMap(bt);
      sbc := AllChainsAuxImplTreeMap(bt, bc);
    }

    static method BtChainImpl(bt:BlockTree<Hash,Transaction,VProof>) returns (bc:BlockChain<Hash,Transaction,VProof>)
      ensures bc == btChain(bt);
    {
      var gb := GenesisBlock();
      var unit := [gb];
      var curr := AllChainsImpl(bt);
      bc := FoldrTakeBetterBCImpl(unit, curr);
    }

    static method BtChainImplTreeMap(bt:OSU.TreeMap<Block<Hash,Transaction,VProof>>) returns (bc:BlockChain<Hash,Transaction,VProof>)
      requires bt.Valid();
      ensures bc == btChain(bt.kvmap);
    {
      var gb := GenesisBlock();
      var unit := [gb];
      var curr := AllChainsImplTreeMap(bt);
      bc := FoldrTakeBetterBCImpl(unit, curr);
    }

    static method ValidChainBlockImpl(bc:BlockChain<Hash,Transaction,VProof>, b:Block<Hash,Transaction,VProof>) returns (v:bool)
      ensures v <==> valid_chain_block(bc, b);
    {
      match b
        case Block(ph, txs, pr) =>
          var vi := VAFImpl(pr, bc, txs);
          var at := AllTxValidImpl(txs, bc);
          v := vi && at;
    }

  }
  
}

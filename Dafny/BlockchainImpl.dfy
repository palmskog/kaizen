include "LinkedList.dfy"
include "BlockchainImplUtil.dfy"

abstract module BlockchainImpl {
  import Collections
  import opened SeqUtil
  import opened SeqUtilImpl
  import opened SeqUtilLemmas
  import opened BlockchainTypes
  import opened BIU : BlockchainImplUtil

  class StateImpl {

    var id : B.Address;
    var peers : Collections.Node<B.Address>;
    var blockTree : B.OSU.TreeMap<Block<B.Hash,B.Transaction,B.VProof>>;
    var txPool : Collections.Node?<B.Transaction>;

    ghost var Repr : set<object>;
    ghost var st : B.State;

    predicate Valid()
      reads this, peers, txPool, blockTree, Repr, peers.Repr, blockTree.Repr;
      reads if txPool != null then txPool.Repr else {};
    {
      this in Repr &&
      peers.Valid() && peers.Repr <= Repr && nodup(peers.list) &&
      blockTree.Valid() &&
      blockTree.Repr <= Repr && this !in blockTree.Repr && peers.Repr !! blockTree.Repr &&
      (txPool != null ==> txPool.Valid() && txPool.Repr <= Repr && txPool.Repr !! blockTree.Repr) &&
      match st
        case Node(i, ps, bt, tp) =>
          i == id &&
          bt == blockTree.kvmap &&
          ps == peers.list &&
          tp == Collections.NodeSeq(txPool)
    }

    constructor InitImpl(a: B.Address)
      ensures Valid();
      ensures id == a;
      ensures blockTree.kvmap == map[B.hashB(B.GenesisBlock()) := B.GenesisBlock()];
      ensures txPool == null;
      ensures st == B.Init(a);
      ensures fresh(peers);
    {
      var id_ := a;
      var peers_ := new Collections.Node.Singleton(a);
      assert peers_.list == [a];
      var gb := B.GenesisBlock();
      var h := Util.HashBImpl(gb);
      assert h == B.hashB(B.GenesisBlock());
      var blockTree_ := new B.OSU.TreeMap<Block<B.Hash,B.Transaction,B.VProof>>();
      blockTree_.Put(h, gb);
      assert (blockTree_.kvmap == map[B.hashB(B.GenesisBlock()) := B.GenesisBlock()]);
      var txPool_ := null;

      id := id_;
      peers := peers_;
      blockTree := blockTree_;
      txPool := txPool_;

      st := B.Node(a, [a], map[B.hashB(B.GenesisBlock()) := B.GenesisBlock()], []);
      Repr := {this, peers} + blockTree_.Repr;
    }

    constructor InitBtImpl(a: B.Address, bt:B.OSU.TreeMap<Block<B.Hash,B.Transaction,B.VProof>>)
      requires bt.Valid();
      ensures Valid();
      ensures id == a;
      ensures blockTree == bt;
      ensures txPool == null;
      ensures fresh(peers);
    {
      var id_ := a;
      var peers_ := new Collections.Node.Singleton(a);
      assert peers_.list == [a];
      var txPool_ := null;

      id := id_;
      peers := peers_;
      blockTree := bt;
      txPool := txPool_;

      st := B.Node(a, [a], bt.kvmap, []);
      Repr := {this, peers} + bt.Repr;
    }

    method BtExtendBlockTreeImpl(b:Block<B.Hash,B.Transaction,B.VProof>)
      modifies this, blockTree.Repr;
      requires Valid();
      ensures Valid();
      ensures id == old(id);
      ensures peers == old(peers);
      ensures txPool == old(txPool);
      ensures blockTree.kvmap == B.btExtend(old(blockTree.kvmap), b);
    {
      Util.BtExtendImplTreeMap(blockTree, b);
      st := B.Node(id, peers.list, blockTree.kvmap, Collections.NodeSeq(txPool));
      Repr := Repr - old(blockTree.Repr) + blockTree.Repr;
    }

    method PoolTxValidTxPoolImpl(bc:BlockChain<B.Hash,B.Transaction,B.VProof>)
      modifies this;
      modifies if txPool != null then txPool.Repr else {};
      requires Valid();
      requires forall o : object :: o in peers.Repr ==> o !in Collections.NodeRepr(txPool);
      ensures Valid();
      ensures id == old(id);
      ensures peers == old(peers);
      ensures blockTree == old(blockTree);
      ensures Collections.NodeSeq(txPool) == B.pool_txValid(bc, old(Collections.NodeSeq(txPool)));
    {
      if txPool != null {
        txPool := Util.PoolTxValidImpl(txPool, bc);
        Repr := Repr - old(txPool.Repr) + Collections.NodeRepr(txPool);
        st := B.Node(id, peers.list, blockTree.kvmap, Collections.NodeSeq(txPool));
      }
    }

    method ProcTxMsgImpl(tx:B.Transaction) returns (pt:B.ToSend)
      modifies this;
      requires Valid();
      requires forall o : object :: o in peers.Repr ==> o !in Collections.NodeRepr(txPool);
      ensures Valid();
      ensures id == old(id);
      ensures peers == old(peers);
      ensures blockTree == old(blockTree);
      ensures st == B.procTxMsg(old(st), tx).0;
      ensures pt == B.procTxMsg(old(st), tx).1;
    {
      txPool := Util.TpExtendImplTreeMap(txPool, blockTree, tx);
      st := B.Node(id, peers.list, blockTree.kvmap, Collections.NodeSeq(txPool));
      Repr := Repr - Collections.NodeRepr(old(txPool)) + Collections.NodeRepr(txPool);
      var dom := blockTree.KeySet();
      var keys := B.OSU.OrderedSetToSeqImpl(dom);
      assert keys == B.OSU.ordered_keys_of(blockTree.kvmap);

      var txph := Util.PoolHashTImpl(txPool);
      var ownHashes := keys + txph;
      ghost var ownHashes' := B.OSU.ordered_keys_of(blockTree.kvmap) + B.pool_hashT(Collections.NodeSeq(txPool));
      var msg := B.InvMsg(ownHashes);
      ghost var msg' := B.InvMsg(ownHashes');

      assert ownHashes == ownHashes';
      var upper := Collections.Node<B.Address>.Size(peers);
      assert peers.list[..upper] == peers.list;
      pt := Util.EmitBroadcastImpl(id, peers, msg, upper);
    }

    method ProcBlockMsgImpl(b:Block<B.Hash,B.Transaction,B.VProof>) returns (pt:B.ToSend)
      modifies this, blockTree.Repr;
      modifies if txPool != null then txPool.Repr else {};
      requires Valid();
      requires forall o : object :: o in peers.Repr ==> o !in Collections.NodeRepr(txPool);
      ensures Valid();
      ensures id == old(id);
      ensures peers == old(peers);
      ensures st == B.procBlockMsg(old(st), b).0;
      ensures pt == B.procBlockMsg(old(st), b).1;
    {
      Util.BtExtendImplTreeMap(blockTree, b);
      var phs := [];
      if txPool != null {
        var btc := Util.BtChainImplTreeMap(blockTree);
        txPool := Util.PoolTxValidImpl(txPool, btc);
        phs := Util.PoolHashTImpl(txPool);
        Repr := Repr - old(txPool.Repr) + Collections.NodeRepr(txPool);
      }
      var dom := blockTree.KeySet();
      var keys := B.OSU.OrderedSetToSeqImpl(dom);
      var ownHashes := keys + phs;
      var upper := Collections.Node<B.Address>.Size(peers);
      assert peers.list[..upper] == peers.list;
      pt := Util.EmitBroadcastImpl(id, peers, B.InvMsg(ownHashes), upper);
      st := B.Node(id, peers.list, blockTree.kvmap, Collections.NodeSeq(txPool));
      Repr := Repr - old(blockTree.Repr) + blockTree.Repr;
    }

    method ProcConnectMsgImpl(from:B.Address) returns (pt:B.ToSend)
      modifies this;
      requires Valid();
      ensures Valid();
      ensures id == old(id);
      ensures blockTree == old(blockTree);
      ensures txPool == old(txPool);
      ensures st == B.procConnectMsg(old(st), from).0;
      ensures pt == B.procConnectMsg(old(st), from).1;
      ensures from !in old(peers).list ==> fresh(peers);
    {
      var contains := Collections.Node<B.Address>.Contains(peers, from);
      if !contains {
          undupAddNotIn(from, peers.list);
          peers := new Collections.Node.Insert(from, peers);
          Repr := Repr + {peers};
          st := B.Node(id, peers.list, blockTree.kvmap, Collections.NodeSeq(txPool));
      } else {
        undupAddIn(from, peers.list);
      }

      var dom := blockTree.KeySet();
      var keys := B.OSU.OrderedSetToSeqImpl(dom);
      assert keys == B.OSU.ordered_keys_of(blockTree.kvmap);

      var txph := Util.PoolHashTImpl(txPool);
      var ownHashes := keys + txph;
      ghost var ownHashes' := B.OSU.ordered_keys_of(blockTree.kvmap) + B.pool_hashT(Collections.NodeSeq(txPool));
      var msg := B.InvMsg(ownHashes);
      ghost var msg' := B.InvMsg(ownHashes');

      assert ownHashes == ownHashes';
      pt := [B.Packet(id, from, msg)];
    }

    method ProcInvMsgImpl(from:B.Address, peerHashes:seq<B.Hash>) returns (pt:B.ToSend)
      requires Valid();
      ensures Valid();
      ensures st == B.procInvMsg(old(st), from, peerHashes).0;
      ensures pt == B.procInvMsg(old(st), from, peerHashes).1;
    {
      var dom := blockTree.KeySet();
      var keys := B.OSU.OrderedSetToSeqImpl(dom);
      assert keys == B.OSU.ordered_keys_of(blockTree.kvmap);

      var txph := Util.PoolHashTImpl(txPool);
      var ownHashes := keys + txph;
      ghost var ownHashes' := B.OSU.ordered_keys_of(blockTree.kvmap) + B.pool_hashT(Collections.NodeSeq(txPool));

      assert ownHashes == ownHashes';
      var newH := SeqExcludeImpl(peerHashes, ownHashes);
      seq_excludeMultisetEq(peerHashes, ownHashes, ownHashes');
      pt := Util.GetDataMsgPacketsImpl(id, from, newH);
    }

    method ProcGetDataMsgImpl(from:B.Address, h:B.Hash) returns (pt:B.ToSend)
      requires Valid();
      ensures Valid();
      ensures st == B.procGetDataMsg(old(st), from, h).0;
      ensures pt == B.procGetDataMsg(old(st), from, h).1;
    {
      if from == id {
        pt := [];
      } else {
        var c := blockTree.ContainsKey(h);
        if c {
          var b := blockTree.Get(h);
          pt := [B.Packet(id, from, B.BlockMsg(b))];
        } else {
          var s := Util.PoolHashTEqImpl(txPool, h);
          if |s| == 0 {
            pt := [];
          } else {
            pt := [B.Packet(id, from, B.TxMsg(s[0]))];
          }
        }
      }
    }

    method ProcAddrMsgImpl(knownPeers:seq<B.Address>) returns (pt:B.ToSend)
      modifies this;
      modifies peers.Repr;
      requires Valid();
      requires forall o : object :: o in Collections.NodeRepr(txPool) ==> o !in peers.Repr;
      ensures Valid();
      ensures id == old(id);
      ensures blockTree == old(blockTree);
      ensures txPool == old(txPool);
      ensures st == B.procAddrMsg(old(st), knownPeers).0;
      ensures pt == B.procAddrMsg(old(st), knownPeers).1;
    {
      var newP := Util.SeqExcludeListImpl(peers, knownPeers);
      if newP == [] {
        pt := [];
      } else {
        assert forall p :: p in newP ==> p !in peers.list;
        assert forall p :: p in peers.list ==> p !in newP;
        var connects := Util.ConnectMsgPacketsImpl(id, newP);
        var undupNewP := UndupImpl(newP);
        assert undupNewP == undup(newP);
        undupAppend(peers.list, newP);
        assert undup(peers.list + newP) == undup(peers.list + undupNewP);
        undupNodup(newP);
        assert nodup(undupNewP);
        assert nodup(peers.list);
        inUndupAll(newP);
        undupInAll(newP);
        undupAppendNotIn(peers.list, undupNewP);
        undupNodupEq(peers.list + undupNewP);
        assert undup(peers.list + undupNewP) == peers.list + undupNewP;
        var peerslistLen := Collections.Node<B.Address>.Size(peers);
        ghost var oldpeerslist := peers.list;
        var peerslist := Collections.Node<B.Address>.Elements(peers);
        assert peerslist == oldpeerslist;
        if undupNewP != [] {
          var undupNewPList := Collections.Node<B.Address>.FromSeq(undupNewP);
          assert undupNewPList.list == undupNewP;
          //ghost var peerslist := peers.list;
          peers := Collections.Node<B.Address>.Append(peers, undupNewPList);
          assert peers.list == peerslist + undupNewP;
          assert nodup(peers.list);
          //assume peers.list == undup(peerslist + newP);
          st := B.Node(id, peers.list, blockTree.kvmap, Collections.NodeSeq(txPool));
          Repr := Repr + undupNewPList.Repr;
          assert peers.list == undup(peerslist + newP);
        } else {
          assert peers.list == undup(peers.list + undupNewP);
          assert peers.list == undup(peers.list + newP);
        }
        var msg := B.AddrMsg(peerslist + undupNewP);
        assert peers.list[..peerslistLen] == peerslist;
        var addrs := Util.EmitBroadcastImpl(id, peers, msg, peerslistLen);
        assert addrs == B.emitBroadcast(id, peerslist, msg);
        pt := connects + addrs;
        assert pt == B.emitMany(B.connectMsgPackets(id, seq_exclude(knownPeers, oldpeerslist))) + addrs;
      }
    }

    method ProcTxTImpl(tx:B.Transaction) returns (pt:B.ToSend)
      requires Valid();
      ensures Valid();
      ensures st == B.procTxT(old(st), tx).0;
      ensures pt == B.procTxT(old(st), tx).1;
    {
      var peersSize := Collections.Node<B.Address>.Size(peers);
      assert peers.list[..peersSize] == peers.list;
      pt := Util.EmitBroadcastImpl(id, peers, B.TxMsg(tx), peersSize);
      assert pt == B.emitBroadcast(id, peers.list, B.TxMsg(tx));
    }

    method ProcMintTImpl(ts:B.Timestamp) returns (pt:B.ToSend)
      modifies this, blockTree.Repr;
      modifies if txPool != null then txPool.Repr else {};
      requires Valid();
      requires forall o : object :: o in peers.Repr ==> o !in Collections.NodeRepr(txPool);
      ensures Valid();
      ensures id == old(id);
      ensures peers == old(peers);
      ensures st == B.procMintT(old(st), ts).0;
      ensures pt == B.procMintT(old(st), ts).1;
    {
      var bc := Util.BtChainImplTreeMap(blockTree);
      var allowedTxs := [];
      if txPool != null {
        allowedTxs := Util.PoolTxValidSeqImpl(txPool, bc);
      }
      var attempt := Util.GenProofImpl(id, bc, allowedTxs, ts);
      match attempt
        case None =>
          pt := [];
        case Some(tpf) =>
          var txs := tpf.0;
          var pf := tpf.1;
          var gb := B.GenesisBlock();
          var prevBlock := LastImpl(gb, bc);
          var hb := Util.HashBImpl(prevBlock);
          var block := Block(hb, txs, pf);
          var btc := Util.BtChainImplTreeMap(blockTree);
          var vcb := Util.ValidChainBlockImpl(btc, block);
          if vcb {
            var dom := blockTree.KeySet();
            var keys := B.OSU.OrderedSetToSeqImpl(dom);
            Util.BtExtendImplTreeMap(blockTree, block);
            var phs := [];
            if txPool != null {
              var btcn := Util.BtChainImplTreeMap(blockTree);
              txPool := Util.PoolTxValidImpl(txPool, btcn);
              phs := Util.PoolHashTImpl(txPool);
              Repr := Repr - old(txPool.Repr) + Collections.NodeRepr(txPool);
            }
            var ownHashes := keys + phs;
            var upper := Collections.Node<B.Address>.Size(peers);
            assert peers.list[..upper] == peers.list;
            pt := Util.EmitBroadcastImpl(id, peers, B.BlockMsg(block), upper);
            st := B.Node(id, peers.list, blockTree.kvmap, Collections.NodeSeq(txPool));
            Repr := Repr - old(blockTree.Repr) + blockTree.Repr;
          } else {
            pt := [];
          }
    }

    method ProcMsgImpl(from:B.Address, msg:B.Message, ts:B.Timestamp) returns (pt:B.ToSend)
      modifies this, peers.Repr, blockTree.Repr;
      modifies if txPool != null then txPool.Repr else {};
      requires Valid();
      ensures Valid();
      ensures id == old(id);
      ensures st == B.procMsg(old(st), from, msg, ts).0;
      ensures pt == B.procMsg(old(st), from, msg, ts).1;
    {
      assume forall o : object :: o in Collections.NodeRepr(txPool) ==> o !in peers.Repr;
      assume forall o : object :: o in peers.Repr ==> o !in Collections.NodeRepr(txPool);
      match msg
        case AddrMsg(ps) =>
          pt := ProcAddrMsgImpl(ps);
        case ConnectMsg =>
          pt := ProcConnectMsgImpl(from);
        case BlockMsg(b) =>
          pt := ProcBlockMsgImpl(b);
        case TxMsg(tx) =>
          pt := ProcTxMsgImpl(tx);
        case InvMsg(s) =>
          pt := ProcInvMsgImpl(from, s);
        case GetDataMsg(h) =>
          pt := ProcGetDataMsgImpl(from, h);
    }

    method ProcIntImpl(tr:B.InternalTransition, ts:B.Timestamp) returns (pt:B.ToSend)
      modifies this, blockTree.Repr;
      modifies if txPool != null then txPool.Repr else {};
      requires Valid();
      ensures Valid();
      ensures id == old(id);
      ensures st == B.procInt(old(st), tr, ts).0;
      ensures pt == B.procInt(old(st), tr, ts).1;
    {
      assume forall o : object :: o in peers.Repr ==> o !in Collections.NodeRepr(txPool);
      match tr
        case TxT(tx) =>
          pt := ProcTxTImpl(tx);
        case MintT =>
          pt := ProcMintTImpl(ts);
    }

  }

}

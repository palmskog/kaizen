include "SeqUtil.dfy"
include "OrderedSeqUtil.dfy"
include "NativeTypes.dfy"

module {:extern "BlockchainTypes"} BlockchainTypes {

  datatype Option<T> = Some(v:T) | None

  datatype Block<Hash,Transaction(==),VProof> = Block(prevBlockHash:Hash, txs:seq<Transaction>, proof:VProof)

  type BlockChain<Hash,Transaction,VProof> = seq<Block<Hash,Transaction,VProof>>

  type TxPool<Transaction> = seq<Transaction>

  type BlockTree<Hash,Transaction,VProof> = map<Hash,Block<Hash,Transaction,VProof>>

}

abstract module Blockchain {
  import opened NativeTypes
  import opened BlockchainTypes
  import opened SeqUtil
  import opened OSU : OrderedSeqUtil

  type Hash = O.T
  type Transaction(==)
  type VProof(==)

  type Address = int32
  type Timestamp = seq<byte>

  function method GenesisBlock() : Block<Hash,Transaction,VProof>

  function hashT(t:Transaction) : Hash
  function hashB(b:Block<Hash,Transaction,VProof>) : Hash

  function genProof(a:Address, bc:BlockChain<Hash,Transaction,VProof>, txs:TxPool<Transaction>, ts:Timestamp) : Option<(TxPool<Transaction>,VProof)>

  predicate VAF(p:VProof, bc:BlockChain<Hash,Transaction,VProof>, txs:TxPool<Transaction>)

  predicate FCR(b1:BlockChain<Hash,Transaction,VProof>, b2:BlockChain<Hash,Transaction,VProof>)

  predicate txValid(t:Transaction, bc:BlockChain<Hash,Transaction,VProof>)

  function tpExtend(tp:TxPool<Transaction>, bt:BlockTree<Hash,Transaction,VProof>, t:Transaction) : TxPool<Transaction>

  function pool_txValid(bc:BlockChain<Hash,Transaction,VProof>, txs:TxPool<Transaction>) : TxPool<Transaction> {
    filter_seq(t => txValid(t, bc), txs)
  }

  function btExtend(bt:BlockTree<Hash,Transaction,VProof>, b:Block<Hash,Transaction,VProof>) : BlockTree<Hash,Transaction,VProof> {
    if hashB(b) in bt then
      bt
    else
      bt[hashB(b) := b]
  }

  // All paths/chains should start with the GenesisBlock
  function compute_chain'(bt:BlockTree<Hash,Transaction,VProof>, b:Block<Hash,Transaction,VProof>, remaining:seq<Hash>, n:int) : BlockChain<Hash,Transaction,VProof>
    requires n >= 0;
    decreases n;
  {
    // Preventing cycles in chains
    if hashB(b) in remaining then
      var rest := remove(hashB(b), remaining);
      if n == 0 then
        []
      else
        match b
          case Block(ph, txs, pr) =>
            if ph in bt then // Build chain prefix recursively
              var prev := bt[ph];
              compute_chain'(remove_map(bt, hashB(b)), prev, rest, n - 1) + [b]
            else // No parent
              [b]
    else
      []
  }

  // Compute chain from the block
  function compute_chain(bt:BlockTree<Hash,Transaction,VProof>, b:Block<Hash,Transaction,VProof>) : BlockChain<Hash,Transaction,VProof> {
    compute_chain'(bt, b, ordered_keys_of(bt), |ordered_keys_of(bt)|)
  }

  // All chains from the given tree
  predicate good_chain(bc:BlockChain<Hash,Transaction,VProof>) {
    if |bc| == 0 then
      false
    else
      bc[0] == GenesisBlock()
  }

  // Transaction validity
  predicate valid_chain'(bc:BlockChain<Hash,Transaction,VProof>, prefix:BlockChain<Hash,Transaction,VProof>) {
    if |bc| == 0 then
      true
    else
      match bc[0]
        case Block(ph, txs, pr) =>
          VAF(pr, prefix, txs) && all_seq(t => txValid(t, prefix), txs) && valid_chain'(bc[1..], prefix + [bc[0]])
  }

  predicate valid_chain(bc:BlockChain<Hash,Transaction,VProof>) {
    valid_chain'(bc, [])
  }

  // Total get_block function
  function get_block(bt:BlockTree<Hash,Transaction,VProof>, k:Hash) : Block<Hash,Transaction,VProof> {
    if k in bt then bt[k] else GenesisBlock()
  }

  // Collect all blocks
  function all_blocks(bt:BlockTree<Hash,Transaction,VProof>) : BlockChain<Hash,Transaction,VProof> {
    map_seq(k => get_block(bt, k), ordered_keys_of(bt))
  }

  function all_chains(bt:BlockTree<Hash,Transaction,VProof>) : seq<BlockChain<Hash,Transaction,VProof>> {
    map_seq(b => compute_chain(bt, b), all_blocks(bt))
  }

  function good_chains(bt:BlockTree<Hash,Transaction,VProof>) : seq<BlockChain<Hash,Transaction,VProof>> {
    filter_seq(c => good_chain(c) && valid_chain(c), all_chains(bt))
  }

  // Get the blockchain
  function take_better_bc(bc2:BlockChain<Hash,Transaction,VProof>, bc1:BlockChain<Hash,Transaction,VProof>) : BlockChain<Hash,Transaction,VProof> {
    if (good_chain(bc2) && valid_chain(bc2)) && FCR(bc2, bc1) then bc2 else bc1
  }

  function btChain(bt:BlockTree<Hash,Transaction,VProof>) : BlockChain<Hash,Transaction,VProof> {
    foldr_seq(take_better_bc, [GenesisBlock()], all_chains(bt))
  }

  predicate valid_chain_block(bc:BlockChain<Hash,Transaction,VProof>, b:Block<Hash,Transaction,VProof>) {
    match b
      case Block(ph, txs, pr) =>
        VAF(pr, bc, txs) && all_seq(t => txValid(t, bc), txs)
  }

  function pool_hashT(txs:TxPool<Transaction>) : seq<Hash> {
    map_seq(hashT, txs)
  }

  function pool_hashT_eq(h:Hash, txs:TxPool<Transaction>) : TxPool<Transaction> {
    filter_seq(t => hashT(t) == h, txs)
  }

  type peers_t = seq<Address>

  datatype Message = AddrMsg(ps:peers_t) | ConnectMsg | BlockMsg(b:Block<Hash,Transaction,VProof>) | TxMsg(t:Transaction) | InvMsg(s:seq<Hash>) | GetDataMsg(h:Hash)

  datatype Packet = Packet(src:Address, dst:Address, msg:Message)

  datatype State = Node(id:Address, peers:peers_t, blockTree:BlockTree<Hash,Transaction,VProof>, txPool:TxPool<Transaction>)

  function Init(n:Address) : State
  {
    Node(n, [n], map[hashB(GenesisBlock()) := GenesisBlock()], [])
  }

  type ToSend = seq<Packet>

  function emitZero() : ToSend {
    []
  }

  function emitOne(packet:Packet) : ToSend {
    [packet]
  }

  function emitMany(packets:ToSend) : ToSend {
    packets
  }

  function emitBroadcast(from:Address, dst:seq<Address>, msg:Message) : ToSend {
    map_seq(d => Packet(from, d, msg), dst)
  }

  function connectMsgPackets(n:Address, ps:peers_t) : ToSend {
    map_seq(p => Packet(n, p, ConnectMsg), ps)
  }

  function getDataMsgPackets(n:Address, from:Address, hs:seq<Hash>) : ToSend {
    map_seq(h => Packet(n, from, GetDataMsg(h)), hs)
  }

  function procMsg(st:State, from:Address, msg:Message, ts:Timestamp) : (State, ToSend) {
    match st
      case Node(n, prs, bt, pool) =>
        match msg
          case ConnectMsg() =>
            var ownHashes := ordered_keys_of(bt) + pool_hashT(pool);
            (Node(n, undup([from] + prs), bt, pool), emitOne(Packet(n, from, InvMsg(ownHashes))))
          case AddrMsg(knownPeers) =>
            var newP := seq_exclude(knownPeers, prs);
            if newP == [] then
              (st, emitZero())
            else
              var connects := connectMsgPackets(n, newP);
              var updP := undup(prs + newP);
              (Node(n, updP, bt, pool), emitMany(connects) + emitBroadcast(n, prs, AddrMsg(updP)))
          case BlockMsg(b) =>
            var newBt := btExtend(bt, b);
            var newPool := pool_txValid(btChain(newBt), pool);
            var ownHashes := ordered_keys_of(newBt) + pool_hashT(newPool);
            (Node(n, prs, newBt, newPool), emitBroadcast(n, prs, InvMsg(ownHashes)))
          case TxMsg(tx) =>
            var newPool := tpExtend(pool, bt, tx);
            var ownHashes := ordered_keys_of(bt) + pool_hashT(newPool);
            (Node(n, prs, bt, newPool), emitBroadcast(n, prs, InvMsg(ownHashes)))
          case InvMsg(peerHashes) =>
            var ownHashes := ordered_keys_of(bt) + pool_hashT(pool);
            var newH := seq_exclude(peerHashes, ownHashes);
            var gets := getDataMsgPackets(n, from, newH);
            (st, emitMany(gets))
          case GetDataMsg(h) =>
            if from == n then
              (st, emitZero())
            else
              var matchingBlocks := if h in bt then [bt[h]] else [];
              if |matchingBlocks| == 0 then
                var matchingTxs := pool_hashT_eq(h, pool);
                if |matchingTxs| == 0 then
                  (st, emitZero())
                else
                  (Node(n, prs, bt, pool), emitOne(Packet(n, from, TxMsg(matchingTxs[0]))))
              else
                (Node(n, prs, bt, pool), emitOne(Packet(n, from, BlockMsg(matchingBlocks[0]))))
  }

  datatype InternalTransition = TxT(t:Transaction) | MintT

  function procInt(st:State, tr:InternalTransition, ts:Timestamp) : (State, ToSend) {
    match st
      case Node(n, prs, bt, pool) =>
        match tr
          case TxT(tx) =>
            (st, emitBroadcast(n, prs, TxMsg(tx)))
          case MintT => // Assumption: nodes broadcast to themselves as well! => simplifies logic
            var bc := btChain(bt);
            var allowedTxs := pool_txValid(bc, pool);
            match genProof(n, bc, allowedTxs, ts)
              case None => (st, emitZero())
              case Some(tpf) =>
                var txs := tpf.0;
                var pf := tpf.1;
                var prevBlock := last(GenesisBlock(), bc);
                var block := Block(hashB(prevBlock), txs, pf);
                if valid_chain_block(btChain(bt), block) then
                  var newBt := btExtend(bt, block);
                  var newPool := pool_txValid(btChain(newBt), pool);
                  var ownHashes := ordered_keys_of(newBt) + pool_hashT(newPool);
                  (Node(n, prs, newBt, newPool), emitBroadcast(n, prs, BlockMsg(block)))
                else
                  (st, emitZero())
  }

  type StateMap = map<Address, State>

  function initState(n:int32) : StateMap
    requires n >= 0;
  {
    if n == 0 then
      map[]
    else
      initState(n - 1)[n := Init(n)]
  }

  type PacketSoup = seq<Packet>

  datatype World = World(localState:StateMap, inFlightPackets:PacketSoup, consumedPackets:PacketSoup)

  datatype Qualifier = Qualifier(ts:Timestamp, allowed:Address)

  type Schedule = seq<Qualifier>

  predicate validH(bt:BlockTree<Hash,Transaction,VProof>) {
    forall h :: h in bt ==> h == hashB(bt[h])
  }

  predicate has_init_block(bt:BlockTree<Hash,Transaction,VProof>) {
    if hashB(GenesisBlock()) in bt then
      bt[hashB(GenesisBlock())] == GenesisBlock()
    else
      false
  }

  function initWorld(n:int32) : World
    requires n >= 0;
  {
    World(initState(n), [], [])
  }

  predicate system_step_idle(w:World, w':World, q:Qualifier) {
    w == w'
  }

  predicate system_step_deliver(w:World, w':World, q:Qualifier) {
    match w
      case World(localState, inFlightPackets, consumedPackets) =>
        exists p :: p in inFlightPackets &&
        match p
          case Packet(src, dst, msg) =>
            match q
              case Qualifier(ts, allowed) =>
                dst == allowed &&
                dst in localState &&
                match procMsg(localState[dst], src, msg, ts)
                  case (st', ms) =>
                    w' == World(localState[dst := st'], remove(p, inFlightPackets) + ms, consumedPackets + [p])
  }

  predicate system_step_intern(w:World, w':World, q:Qualifier) {
    match w
      case World(localState, inFlightPackets, consumedPackets) =>
        exists proc :: proc in localState &&
        match q
          case Qualifier(ts, allowed) =>
            proc == allowed && exists t ::
            match procInt(localState[proc], t, ts)
              case (st', ms) =>
                w' == World(localState[proc := st'], ms + inFlightPackets, consumedPackets)
  }

  predicate system_step(w:World, w':World, q:Qualifier) {
    system_step_idle(w, w', q) || system_step_deliver(w, w', q) || system_step_intern(w, w', q)
  }

  // helper functions for more practical refinement

  function all_blocks_aux(bt:BlockTree<Hash,Transaction,VProof>, ks:seq<Hash>) : BlockChain<Hash,Transaction,VProof>
    ensures all_blocks_aux(bt, ks) == map_seq(k => get_block(bt, k), ks);
  {
    if |ks| == 0 then []
    else
      var k := ks[0];
      var b := get_block(bt, k);
      [b] + all_blocks_aux(bt, ks[1..])
  }

  function all_chains_aux(bt:BlockTree<Hash,Transaction,VProof>, bc:BlockChain<Hash,Transaction,VProof>) : seq<BlockChain<Hash,Transaction,VProof>>
    ensures all_chains_aux(bt, bc) == map_seq(b => compute_chain(bt, b), bc);
  {
    if |bc| == 0 then []
    else
      var bc' := compute_chain(bt, bc[0]);
      [bc'] + all_chains_aux(bt, bc[1..])
  }

  function procTxMsg(st:State, tx:Transaction) : (State, ToSend)
    ensures forall from, ts :: procTxMsg(st, tx) == procMsg(st, from, TxMsg(tx), ts);
  {
    match st
      case Node(n, prs, bt, pool) =>
        var newPool := tpExtend(pool, bt, tx);
        var ownHashes := ordered_keys_of(bt) + pool_hashT(newPool);
        (Node(n, prs, bt, newPool), emitBroadcast(n, prs, InvMsg(ownHashes)))
  }

  function procAddrMsg(st:State, knownPeers:peers_t) : (State, ToSend)
     ensures forall from, ts :: procAddrMsg(st, knownPeers) == procMsg(st, from, AddrMsg(knownPeers), ts);
  {
    match st
      case Node(n, prs, bt, pool) =>
        var newP := seq_exclude(knownPeers, prs);
        if newP == [] then
          (st, emitZero())
        else
          var connects := connectMsgPackets(n, newP);
          var updP := undup(prs + newP);
          (Node(n, updP, bt, pool), emitMany(connects) + emitBroadcast(n, prs, AddrMsg(updP)))
  }

  function procConnectMsg(st:State, from:Address) : (State, ToSend)
    ensures forall ts :: procConnectMsg(st, from) == procMsg(st, from, ConnectMsg, ts);
  {
    match st
      case Node(n, prs, bt, pool) =>
        var ownHashes := ordered_keys_of(bt) + pool_hashT(pool);
        (Node(n, undup([from] + prs), bt, pool), emitOne(Packet(n, from, InvMsg(ownHashes))))
  }

  function procBlockMsg(st:State, b:Block<Hash,Transaction,VProof>) : (State, ToSend)
    ensures forall from, ts :: procBlockMsg(st, b) == procMsg(st, from, BlockMsg(b), ts);
  {
    match st
      case Node(n, prs, bt, pool) =>
        var newBt := btExtend(bt, b);
        var newPool := pool_txValid(btChain(newBt), pool);
        var ownHashes := ordered_keys_of(newBt) + pool_hashT(newPool);
        (Node(n, prs, newBt, newPool), emitBroadcast(n, prs, InvMsg(ownHashes)))
  }

  function procInvMsg(st:State, from:Address, peerHashes:seq<Hash>) : (State, ToSend)
    ensures forall ts :: procInvMsg(st, from, peerHashes) == procMsg(st, from, InvMsg(peerHashes), ts);
  {
    match st
      case Node(n, prs, bt, pool) =>
        var ownHashes := ordered_keys_of(bt) + pool_hashT(pool);
        var newH := seq_exclude(peerHashes, ownHashes);
        var gets := getDataMsgPackets(n, from, newH);
        (st, emitMany(gets))
  }

  function procGetDataMsg(st:State, from:Address, h:Hash) : (State, ToSend)
    ensures forall ts :: procGetDataMsg(st, from, h) == procMsg(st, from, GetDataMsg(h), ts);
  {
    match st
      case Node(n, prs, bt, pool) =>
        if from == n then
        (st, emitZero())
        else
          var matchingBlocks := if h in bt then [bt[h]] else [];
          if |matchingBlocks| == 0 then
            var matchingTxs := pool_hashT_eq(h, pool);
            if |matchingTxs| == 0 then
              (st, emitZero())
            else
              (Node(n, prs, bt, pool), emitOne(Packet(n, from, TxMsg(matchingTxs[0]))))
          else
            (Node(n, prs, bt, pool), emitOne(Packet(n, from, BlockMsg(matchingBlocks[0]))))
  }

  function procTxT(st:State, tx:Transaction) : (State, ToSend)
    ensures forall ts :: procTxT(st, tx) == procInt(st, TxT(tx), ts);
  {
    match st
      case Node(n, prs, bt, pool) =>
        (st, emitBroadcast(n, prs, TxMsg(tx)))
  }

  function procMintT(st:State, ts:Timestamp) : (State, ToSend)
    ensures procMintT(st, ts) == procInt(st, MintT, ts);
  {
     match st
      case Node(n, prs, bt, pool) =>
        var bc := btChain(bt);
        var allowedTxs := pool_txValid(bc, pool);
        match genProof(n, bc, allowedTxs, ts)
          case None => (st, emitZero())
          case Some(tpf) =>
            var txs := tpf.0;
            var pf := tpf.1;
            var prevBlock := last(GenesisBlock(), bc);
            var block := Block(hashB(prevBlock), txs, pf);
            if valid_chain_block(btChain(bt), block) then
              var newBt := btExtend(bt, block);
              var newPool := pool_txValid(btChain(newBt), pool);
              var ownHashes := ordered_keys_of(newBt) + pool_hashT(newPool);
              (Node(n, prs, newBt, newPool), emitBroadcast(n, prs, BlockMsg(block)))
            else
              (st, emitZero())
  }

}

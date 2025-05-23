include "Blockchain.dfy"
include "OrderedSeqUtil.dfy"
include "MathUtil.dfy"
include "BitcoinConstants.dfy"
include "NativeTypes.dfy"
include "NativeTypesUtil.dfy"

module {:extern "BitcoinUtilExt"} BitcoinUtilExt
{
  import opened NativeTypes

  class {:extern "Util"} UtilExt
  {
    static function method {:extern "SHA256"} SHA256Ext(messageBytes:seq<byte>) : seqbyte32
  }
}

module {:extern "Bitcoin"} Bitcoin refines Blockchain
{
  import opened OSU = OrderedSeqUtilSeqByte32AsInt
  import opened MathUtil
  import opened BitcoinConstants
  import opened NativeTypesUtil
  import BitcoinUtilExt

  // version: 4 bytes; time: 4 bytes; bits: 4 bytes; nonce: 4 bytes
  datatype BitcoinProof = BitcoinProof(version:seq<byte>, time:Timestamp, bits:seq<byte>, nonce:seq<byte>)

  // prevout_hash: 32 bytes; prevout_n: 4 bytes; scriptsig: <= 140 bytes; sequence: 4 bytes
  datatype BitcoinTxIn = BitcoinTxIn(prevout_hash:seq<byte>, prevout_n:seq<byte>, scriptsig:seq<byte>, sequence:seq<byte>)
  // value: 8 bytes; scriptpubkey: <= 10,000 bytes
  datatype BitcoinTxOut = BitcoinTxOut(value:seq<byte>, scriptpubkey:seq<byte>)

  // version: 4 bytes; locktime: 4 bytes
  datatype BitcoinTransaction = BitcoinTransaction(version:seq<byte>, ins:seq<BitcoinTxIn>, outs:seq<BitcoinTxOut>, locktime:Timestamp)

  type Transaction = BitcoinTransaction
  type VProof = BitcoinProof

  function method SHA256(messageBytes:seq<byte>) : Hash {
    BitcoinUtilExt.UtilExt.SHA256Ext(messageBytes)
  }

  function method BitcoinHash(messageBytes:seq<byte>) : Hash {
    SHA256(SHA256(messageBytes))
  }

  function hashdataBitcoinTxIn(ti:BitcoinTxIn) : seq<byte> {
    match ti
      case BitcoinTxIn(prevout_hash, prevout_n, scriptsig, sequence) =>
        prevout_hash + prevout_n + scriptsig + sequence
  }

  function hashdataBitcoinTxOut(ti:BitcoinTxOut) : seq<byte> {
    match ti
      case BitcoinTxOut(value, scriptpubkey) =>
        value + scriptpubkey
  }

  function hashdataT(t:Transaction) : seq<byte> {
    match t
      case BitcoinTransaction(version, ins, outs, locktime) =>
        version +
        BEUintToSeqByte(|ins|, 1) +
        foldr_seq((i, s) => hashdataBitcoinTxIn(i) + s, [], ins) +
        BEUintToSeqByte(|outs|, 1) +
        foldr_seq((o, s) => hashdataBitcoinTxOut(o) + s, [], outs) +
        locktime
  }

  function hashT(t:Transaction) : Hash {
    BitcoinHash(hashdataT(t))
  }

  function hashdataB(b:Block<Hash,Transaction,VProof>) : seq<byte> {
    match b
      case Block(prevBlockHash, txs, proof) =>
        match proof
          case BitcoinProof(version, time, bits, nonce) =>
            version + prevBlockHash + merkle_tree_hash(txs) + time + bits + nonce
  }

  function hashB(b:Block<Hash,Transaction,VProof>) : Hash {
    if b == GenesisBlock() then
      match b case Block(prevBlockHash, txs, proof) => prevBlockHash
    else
      BitcoinHash(hashdataB(b))
  }

  // FIXME: replace with realistic tpExtend specification
  function tpExtend(tp:TxPool<Transaction>, bt:BlockTree<Hash,Transaction,VProof>, t:Transaction) : TxPool<Transaction>
  {
    if t !in tp then
      [t] + tp
    else
      tp
  }

  // FIXME: replace with realistic specification
  function genProof(a:Address, bc:BlockChain<Hash,Transaction,VProof>, txs:TxPool<Transaction>, ts:Timestamp) : Option<(TxPool<Transaction>,VProof)>
  {
    if a == 0 then
      None
    else
      Some(([], BitcoinProof([], [], [], [])))
  }

  // FIXME: replace with realistic specification
  predicate VAF(p:VProof, bc:BlockChain<Hash,Transaction,VProof>, txs:TxPool<Transaction>)
  {
    true
  }

  // FIXME: replace with realistic specification
  predicate FCR(b1:BlockChain<Hash,Transaction,VProof>, b2:BlockChain<Hash,Transaction,VProof>)
  {
    true
  }

  // FIXME: replace with realistic specification
  predicate txValid(t:Transaction, bc:BlockChain<Hash,Transaction,VProof>)
  {
    true
  }

  function merkle_tree_pass(hs:seq<Hash>) : seq<Hash>
  {
    if |hs| == 0 then []
    else if |hs| == 1 then [BitcoinHash(hs[0] + hs[0])]
    else [BitcoinHash(hs[0] + hs[1])] + merkle_tree_pass(hs[2..])
  }

  function merkle_tree_hash_loop(hs:seq<Hash>, k:nat) : Hash
    decreases k;
  {
    if k == 0 then (if |hs| == 1 then hs[0] else [])
    else merkle_tree_hash_loop(merkle_tree_pass(hs), k - 1)
  }

  function merkle_tree_hash(txs:seq<Transaction>) : Hash
  {
    var hs := map_seq(hashT, txs);
    var passes := ceil_log2(|hs|);
    merkle_tree_hash_loop(hs, passes)
  }

  function method GenesisBlockTxIn() : BitcoinTxIn
  {
    BitcoinTxIn(
      GenesisBlockTxIn_prevout_hash(),
      GenesisBlockTxIn_prevout_n(),
      GenesisBlockTxIn_scriptsig(),
      GenesisBlockTxIn_sequence()
    )
  }

  function method GenesisBlockTxOut() : BitcoinTxOut
  {
    BitcoinTxOut(
      GenesisBlockTxOut_value(),
      GenesisBlockTxOut_scriptpubkey()
    )
  }

  function method GenesisBlockTx() : BitcoinTransaction
  {
    BitcoinTransaction(
      GenesisBlockTx_version(),
      [GenesisBlockTxIn()],
      [GenesisBlockTxOut()],
      GenesisBlockTx_locktime()
    )
  }

  function method GenesisBlockPr() : BitcoinProof
  {
    BitcoinProof(
      GenesisBlockPr_version(),
      GenesisBlockPr_time(),
      GenesisBlockPr_bits(),
      GenesisBlockPr_nonce()
    )
  }

  function method GenesisBlock() : Block<Hash,Transaction,VProof>
  {
    Block(GenesisBlock_hash(), [GenesisBlockTx()], GenesisBlockPr())
  }
}

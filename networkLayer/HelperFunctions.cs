#define LOCAL
using System;
using Newtonsoft.Json.Linq;
using System.IO;
using System.Collections.Generic;
using System.Numerics;
using Bitcoin;
using Dafny;
using _39_OrderedSeqUtilSeqByte32AsInt_Compile;

using BitcoinBlock = BlockchainTypes.Block<Dafny.Sequence<byte>, Bitcoin.BitcoinTransaction, Bitcoin.BitcoinProof>;

namespace networkLayer
{
    public static class HelperFunctions
    {
        static Dictionary<string, BitcoinTransaction> TransactionDictionary = new Dictionary<string, BitcoinTransaction>();
        static Dictionary<string, Sequence<byte>> BitcoinToDafnyTransactionHash = new Dictionary<string, Sequence<byte>>();
        static Dictionary<string, Sequence<byte>> BitcoinToDafnyBlockHash = new Dictionary<string, Sequence<byte>>();
        public static Dictionary<Sequence<byte>, string> DafnyToBitcoinTransactionHash = new Dictionary<Sequence<byte>, string>();
        public static Dictionary<Sequence<byte>, string> DafnyToBitcoinBlockHash = new Dictionary<Sequence<byte>, string>();
        //only used in testing function 
        static Dictionary<string, Sequence<BigInteger>> hashToBlock = new Dictionary<string, Sequence<BigInteger>>();

        public static string GetClusterDataFile()
        {
#if (LOCAL)
            return "./data/local-cluster.json";
#elif (REALIMP)
            return "./data/prod-cluster.json";
#elif (EMULABEXP)
            return "./data/emulab-cluster.json";
#endif
        }

        public static string GetInitialStateFile()
        {
#if (LOCAL)
            return "./data/local-blocks.json";
#elif (REALIMP)
            return "./data/blocks.json";
#elif (EMULABEXP)
            return "./data/experiments/blocks.json";
#endif
        }

        public static string GetAllTransactionsFile()
        {
#if (LOCAL)
            return "./data/all-transactions.json";
#elif (REALIMP)
            return "./data/all-transactions.json";
#elif (EMULABEXP)
            return "./data/experiments/tx.json";
#endif
        }


        public static Sequence<byte> GetSequenceForTransactionHash(string hashTransaction)
        {
            return BitcoinToDafnyTransactionHash.GetValueOrDefault(hashTransaction);
        }

        public static void PopulateBlocksMap(ref TreeMap<BitcoinBlock> map)
        {
            JArray allBlocks = JArray.Parse(File.ReadAllText(GetInitialStateFile()));
            var numBlocks = allBlocks.Count;
            var pairs = new Pair<Sequence<byte>, BitcoinBlock>[numBlocks];

            Console.WriteLine("Loading the blocks from the file.");
            for (int i = 0; i < allBlocks.Count; i++)
            {
                JObject block = (JObject)allBlocks[i];
                JArray txs = (JArray)block.GetValue("tx");
                BitcoinTransaction[] bitcoinTransactions = new BitcoinTransaction[txs.Count];
                for (int j = 0; j < txs.Count; j++)
                {
                    bitcoinTransactions[j] = TransactionDictionary.GetValueOrDefault((string)txs[j]);
                }

                uint version = (uint)block.GetValue("version");
                uint bits = 24 + (uint)i; // todo: talk about removing hard coding.
                uint time = (uint)block.GetValue("time");
                uint nonce = (uint)block.GetValue("nonce");
                BitcoinBlock Bitcoinblock;
                BitcoinProof proof;
                Sequence<byte> prevHash;
                Sequence<byte> hashB;
                if (i == 0)
                {
                    Bitcoinblock = Bitcoin.__default.GenesisBlock();
                    //This is the genesis block
                }
                else
                {
                    proof = new BitcoinProof(new BitcoinProof_BitcoinProof(
                        Converter.ConvertUIntToBytes(version),
                        Converter.ConvertUIntToBytes(time),
                        Converter.ConvertUIntToBytes(bits),
                        Converter.ConvertUIntToBytes(nonce)));
                    string bitcoinHash = (string)block.GetValue("previousblockhash");
                    prevHash = BitcoinToDafnyBlockHash.GetValueOrDefault(bitcoinHash);
                    Bitcoinblock = new BitcoinBlock(
                        new BlockchainTypes.Block_Block<Sequence<byte>, BitcoinTransaction, BitcoinProof>(
                        prevHash, new Sequence<BitcoinTransaction>(bitcoinTransactions), proof)
                    );
                }

                BitcoinImplUtil.Util.HashBImpl(Bitcoinblock, out hashB);
                string myHash = (string)block.GetValue("hash");
                BitcoinToDafnyBlockHash.Add(myHash, hashB);
                DafnyToBitcoinBlockHash.Add(hashB, myHash);
                map.Put(hashB, Bitcoinblock);
            }           
        }

        public static void PopulateDictionaryWithTransactions()
        {
            JArray allTransactions = JArray.Parse(File.ReadAllText(GetAllTransactionsFile()));
            Console.WriteLine("Loading " + allTransactions.Count + " transactions!");
            for (int i = 0; i < allTransactions.Count; i++)
            {
                JObject transaction = (JObject)allTransactions[i];
                string txID = (string)transaction.GetValue("txid");

                uint version = (uint)i;
                uint locktime = (uint)transaction.GetValue("locktime") + (uint)i;
                JArray vins = (JArray)transaction.GetValue("vin");
                JArray vouts = (JArray)transaction.GetValue("vout");

                int vinSize = vins.Count;
                int voutSize = vouts.Count;
                BitcoinTxIn[] bitcoinTxIns = new BitcoinTxIn[vinSize];
                BitcoinTxOut[] bitcoinTxOuts = new BitcoinTxOut[voutSize];
                byte[] empty = new byte[0];
                for (int j = 0; j < vinSize; j++)
                {
                    if (((JObject)vins[j]).ContainsKey("coinbase"))
                    {
                        BitcoinTxIn txIn = new BitcoinTxIn(new BitcoinTxIn_BitcoinTxIn(
                            new Sequence<byte>(empty),
                            new Sequence<byte>(empty),
                            new Sequence<byte>(empty),
                            new Sequence<byte>(empty)));
                        bitcoinTxIns[j] = txIn;
                    }
                    else
                    {
                        uint sequence = (uint)((JObject)vins[j]).GetValue("sequence");
                        uint prev_n = (uint)((JObject)vins[j]).GetValue("vout");
                        uint n = (uint)i;
                        string hash = (string)((JObject)vins[j]).GetValue("txid");
                        BitcoinTxIn txIn = new BitcoinTxIn(new BitcoinTxIn_BitcoinTxIn(
                            BitcoinToDafnyTransactionHash.GetValueOrDefault(hash),
                            Converter.ConvertUIntToBytes(prev_n),
                            new Sequence<byte>(empty),
                            Converter.ConvertUIntToBytes(sequence)));

                        bitcoinTxIns[j] = txIn;

                    }
                }


                for (int j = 0; j < voutSize; j++)
                {
                    ulong value = (ulong)((double)((JObject)vouts[j]).GetValue("value") * Math.Pow(10.0, 8.0));
                    BitcoinTxOut txOut = new BitcoinTxOut(new BitcoinTxOut_BitcoinTxOut(
                        Converter.ConvertULongToBytes(value),
                        new Sequence<byte>(empty)
                    ));
                    bitcoinTxOuts[j] = txOut;
                }

                BitcoinTransaction bitcoinTx = new BitcoinTransaction(
                    new BitcoinTransaction_BitcoinTransaction(
                        Converter.ConvertUIntToBytes(version),
                        new Sequence<BitcoinTxIn>(bitcoinTxIns),
                        new Sequence<BitcoinTxOut>(bitcoinTxOuts),
                        Converter.ConvertUIntToBytes(locktime)));

                Sequence<byte> hashSequence;
                BitcoinImplUtil.Util.HashTImpl(bitcoinTx, out hashSequence);

                BitcoinToDafnyTransactionHash.Add(txID, hashSequence);
                DafnyToBitcoinTransactionHash.Add(hashSequence, txID);

                TransactionDictionary.Add(txID, bitcoinTx);
            }
        }


        public static void PopulateDictionaryWithNodes(ref Dictionary<int, NodeInfo> dictionary)
        {
            JObject nodeData = JObject.Parse(File.ReadAllText(@GetClusterDataFile()));
            JArray allNodes = (JArray)nodeData.GetValue("nodes");

            for (int i = 0; i < allNodes.Count; i++)
            {
                JObject obj = (JObject)allNodes[i];
                int id = (int)obj.GetValue("id");
                int port = (int)obj.GetValue("port");
                string IPAddress = (string)obj.GetValue("ip_address");
                String path = (string)obj.GetValue("unspent_transactions");
                String key = (string)obj.GetValue("key");
                String address = (string)obj.GetValue("address");
                
                NodeInfo node = new NodeInfo(IPAddress, port, address, key, path);
                dictionary.Add(id, node);
            }   
        }

        public static uint GetEpochTime()
        {
            TimeSpan t = DateTime.UtcNow - new DateTime(1970, 1, 1);
            uint secondsSinceEpoch = (uint)t.TotalSeconds;
            return secondsSinceEpoch;
        }

    }
}

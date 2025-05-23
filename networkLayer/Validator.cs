#define LOCAL
using System;
using System.Numerics;
using Bitcoin;
using BitcoinImpl;
using Dafny;
using Newtonsoft.Json.Linq;
using System.IO;
using System.Collections.Generic;
using BitcoinBlock = BlockchainTypes.Block<Dafny.Sequence<byte>, Bitcoin.BitcoinTransaction, Bitcoin.BitcoinProof>;


namespace networkLayer
{
    public class Validator
    {
        static void GetChain(StateImpl state, out Sequence<BitcoinBlock> chain)
        {
            var blockTree = state.blockTree;
            BigInteger length;
            blockTree.Size(out length);
            Console.WriteLine(" The size of the BlockTree inside the state. " + length);
            BitcoinImplUtil.Util.BtChainImplTreeMap(blockTree, out chain);
        }

        public static void ValidateNumBlocks(StateImpl currentState, int localBlocks)
        {
            Sequence<BitcoinBlock> chain;
            GetChain(currentState, out chain);
            int chainElements = chain.Elements.Length;
            if (chainElements != localBlocks)
            {
                Console.WriteLine("So, according to the shim, you should have "
                                  + localBlocks + " blocks, but found "
                                  + chainElements + " in dafny.");
            }
        }

        public static void PrintCurrentChain(StateImpl currentState)
        {
            Sequence<BitcoinBlock> chain;
            GetChain(currentState, out chain);
            var transactionCache = new Dictionary<BitcoinTransaction, int>();
            Console.WriteLine("There are " + chain.Elements.Length
                              + " blocks in the chain right now.");


            //Console.WriteLine("The initially loaded Blocks are:\n");

            for (int i = 0; i < chain.Elements.Length; i++)
            {
                Sequence<byte> hashB;
                BitcoinImplUtil.Util.HashBImpl(chain.Elements[i], out hashB);
                var numTransactions = chain.Elements[i].dtor_txs.Elements.Length;
                if (i > 7)
                {
#if (LOCAL)
                    Console.WriteLine("===== ");


                    Console.WriteLine("{");
                    Console.WriteLine("  This Block Hash " + hashB);
                    Console.WriteLine("  Previous Block Hash " + chain.Elements[i]
                                      .dtor_prevBlockHash);
#endif
                    var bitcoinTransaction = chain.Elements[i].dtor_txs;
                    Console.WriteLine("  Num Transactions in block " + i + " " +
                                      +bitcoinTransaction.Elements.Length);
                    for (int k = 0; k < bitcoinTransaction.Elements.Length; k++)
                    {
                        if (transactionCache.ContainsKey(bitcoinTransaction.Elements[k]) && k!=0) //coinbase transaction.
                        {
                            Console.WriteLine("Something is wrong. " +
                                              "This transaction is a part of " +
                                              "another block in the chain - in block " + i);
                            Console.WriteLine(bitcoinTransaction.Elements[k]);
                            Environment.Exit(0);
                        }

                        var transactionDtorIns = bitcoinTransaction.Elements[k].dtor_ins;
                        #if (LOCAL)
                        Console.WriteLine(bitcoinTransaction.Elements[k]);
#endif
                        if (transactionDtorIns.Length > 0)
                        {
                            var prevHashT = transactionDtorIns.Elements[0].dtor_prevout__hash;
                            //Console.WriteLine("Prev hash of this is " + HelperFunctions
                            //                  .DafnyToBitcoinTransactionHash
                            //                  .GetValueOrDefault(prevHashT));
                            if (k != 0 )
                            {
                                transactionCache.Add(bitcoinTransaction.Elements[k], i);
                            }
                           
                        }
                        else
                        {
                            Console.WriteLine("No TxIns? This is weird. Aborting. NEEDS TO BE FIXED.");
                            Console.WriteLine("  Proof " + chain.Elements[i].dtor_proof);
                            Console.WriteLine("}");
                            Environment.Exit(0);
                        }
                    }
#if (LOCAL)
                    Console.WriteLine("  Proof " + chain.Elements[i].dtor_proof);
                    Console.WriteLine("}");
#endif
                }
                if (i==7)
                {
                    Console.WriteLine("New Blocks are (added after initial state):\n");
                }
            }
        }

        public static void ValidateInitialChain(StateImpl currentState)
        {
            Sequence<BitcoinBlock> chain;
            GetChain(currentState, out chain);

            string localState = HelperFunctions.GetInitialStateFile();
            JArray allBlocks = JArray.Parse(File.ReadAllText(localState));
            var numBlocks = allBlocks.Count;

            if (numBlocks != chain.Elements.Length)
            {
                Console.WriteLine("The number of blocks in " + localState 
                                  + " and the dafny state don't match!");
                Console.WriteLine(numBlocks + " " + chain.Elements.Length);
                PrintCurrentChain(currentState);
                return;
                //Environment.Exit(-1);
            }
            int issues = 0; 
            for (int i = 0; i < chain.Elements.Length; i++)
            {
                
                string blockHash;
                JObject block = (JObject)allBlocks[i];
                string hash = (string)block.GetValue("hash");
                Sequence<byte> hashB;
                BitcoinImplUtil.Util.HashBImpl(chain.Elements[i], out hashB);
                HelperFunctions.DafnyToBitcoinBlockHash
                               .TryGetValue(hashB, out blockHash);
                if (blockHash != hash)
                {
                    Console.WriteLine("This is Element " + i + " in the chain " 
                                      + blockHash);
                    Console.WriteLine("The actual block should be " + hash);
                    issues++;
                }
            }
            Console.WriteLine("ValidateInitialChain:: Validation of " +
                              "initial state complete. Issues found " + issues);
        }
    }
}

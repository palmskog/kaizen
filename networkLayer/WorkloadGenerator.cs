using System;
using System.Threading;
using System.IO;
using Newtonsoft.Json.Linq;
using System.Collections.Generic;
using Google.Protobuf.Messages;
using Google.Protobuf;

/**
 * This class will be transmitting transactions from outside.
 * So we have a separate Network connection here as well which can broadcast the connections
 * 
 */
namespace networkLayer
{
    
    public class WorkloadGenerator
    {
        const double fee = 0.00999000;
        Dictionary<int, NodeInfo> nodes;
        Client client;
        int delay = 50;       // This is the minimum delay between 2 transactions.
        Random random = new Random();
        
        public void InitializeCluster()
        {
            nodes = new Dictionary<int, NodeInfo>();
            client = new Client(9000);
            HelperFunctions.PopulateDictionaryWithNodes(ref nodes);
            HelperFunctions.PopulateDictionaryWithTransactions();
        }

        public void broadcastAddresses()
        {
            foreach (KeyValuePair<int, NodeInfo> kvp in nodes)
            {
                SendAddrMessage(kvp.Value.getIPAddress(), kvp.Value.getPort());
            }
        }

        public JArray loadSendRateData() {
            JObject meta = JObject.Parse(File.ReadAllText(@"./data/transactions.json"));
            return (JArray)meta.GetValue("transactions");
        }

        public void broadcastTransactions()
        {
            JArray dataRateTrans = loadSendRateData();

            int j = 0;
            int size = dataRateTrans.Count;
            long timePrev = (long)((JObject)((JObject)dataRateTrans[0]).GetValue("x"))
                                                             .GetValue("time");

            int maxUnspentTransaction = 0;
            foreach (KeyValuePair<int, NodeInfo> kvp in nodes) {
                if (maxUnspentTransaction < kvp.Value.getUnspentTransactions().Count)
                {
                    maxUnspentTransaction = kvp.Value.getUnspentTransactions().Count;   
                }
            }
            Console.WriteLine("maxUnspent: " + maxUnspentTransaction);

            int nodeToSend = 1;

            for (int k = 0; k < maxUnspentTransaction; k++) {
                
                foreach (KeyValuePair<int, NodeInfo> kvp in nodes)
                {
                    NodeInfo node = kvp.Value;
                    if (k < node.getUnspentTransactions().Count) {

                        Console.WriteLine("Sending transaction no: " + k + " " + "for node: " + node.getAddress());

                        UnspentTransaction transaction = (node.getUnspentTransactions())[k];

                        // instead of randomly picking who to send the money to, I'll just pick the next node
                        int nextNode = nodeToSend % (nodes.Count) + 1;
                        nodeToSend += 1;
                        Console.WriteLine(nodeToSend + " " + nextNode);
			            NodeInfo receiver = nodes[nextNode];

                        j++;
                        if (j == size)
                        {
                            timePrev = (long)((JObject)((JObject)dataRateTrans[0]).GetValue("x"))
                                                                     .GetValue("time");
                            j = 1;
                        }
                        long time = (long)((JObject)((JObject)dataRateTrans[j]).GetValue("x"))
                                                                     .GetValue("time");
                        long diff = time - timePrev + delay;
                        timePrev = time;

                        Transaction t = createRawTransaction(transaction, receiver, node);

                        String ipAddress = receiver.getIPAddress();
                        int port = receiver.getPort();

                        client.SendMessage(t, ipAddress, port);
                        Console.WriteLine("Sending Transaction to " +
                                          ipAddress + " " + port.ToString() +
                                          " " + t.TxIns[0].PrevoutHash + " " +
                                          t.TxOuts[0].Value + " " + transaction.getAmount());

                        if (diff > 0)
                        {
                            Thread.Sleep((int)diff);
                        }

                    }

                }
            }

        }

        public Transaction createRawTransaction (UnspentTransaction unspentTransaction, NodeInfo receiver, NodeInfo sender)
        {
            Transaction transaction = new Transaction
            {
                Time = HelperFunctions.GetEpochTime(),
                Version = 1 // TODO: make this a const later
            };
            // transactions are simple and have one input and output each 

            Dafny.Sequence<byte> previousBytes = HelperFunctions.GetSequenceForTransactionHash(unspentTransaction.getTxId());
            if (previousBytes == null) 
            {
                Console.WriteLine("Couldn't find previousBytes in dictionary. Hmm. " + unspentTransaction.getTxId());

                Environment.Exit(0);
            }
            byte[] byteArray = previousBytes.Elements;


            TxIn transactionIn = new TxIn
            {
                PrevoutN = unspentTransaction.getVOut(),
                PrevoutHash = unspentTransaction.getTxId(),
                Sequence = 1, // TODO: make a const later, used with locktime
                Script = "",
                PrevoutHashBytes = ByteString.CopyFrom(byteArray) // This will be used by node and not bitcoin node
            };

            Console.WriteLine(new Dafny.Sequence<byte>(byteArray));

            transaction.TxIns.Add(transactionIn);

            TxOut transactionOut = new TxOut
            {
                Value = Convert.ToUInt64((unspentTransaction.getAmount() - fee) * Math.Pow(10.0, 8.0)),
                ScriptPublicKey = receiver.getAddress()
            };

            transaction.TxOuts.Add(transactionOut);
            Console.WriteLine("Sending: " + transaction.TxIns[0].PrevoutHash + ", " + transaction.TxIns[0].Script + ", " + transaction.TxIns[0].Sequence + "," + transaction.TxIns[0].PrevoutN);
            return transaction;
        }

        public void SendAddrMessage(String ipAddress, int port)
        {
            Addr address = new Addr();
            foreach (KeyValuePair<int, NodeInfo> kvp in nodes)
            {
                if (kvp.Value.getIPAddress().Equals(ipAddress) && 
                    kvp.Value.getPort().Equals(port))
                {
                    Console.WriteLine("NOT SENDING THIS TO " + ipAddress + " " + port);
                }
                else
                {
                    address.Peers.Add(kvp.Key);
                }

            }
            client.SendMessage(address, ipAddress, port);
        }
    }
}

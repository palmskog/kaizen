using System;
using Bitcoin;
using BitcoinImpl;
using _39_OrderedSeqUtilSeqByte32AsInt_Compile;
using Google.Protobuf.Messages;
using System.Numerics;
using System.Collections.Generic;
using Dafny;
using Google.Protobuf;
using System.Threading;

using BitcoinBlock = BlockchainTypes.Block<Dafny.Sequence<byte>, Bitcoin.BitcoinTransaction, Bitcoin.BitcoinProof>;


namespace networkLayer
{
    public class Node
    {
        StateImpl myState;
        Server server;
        Client client;
        Dictionary<BitcoinTransaction, int> transactionCache = new Dictionary<BitcoinTransaction, int>();
        protected Object messageLock;
        protected uint totalTransactionsReceived = 0;
        protected Queue<ReceivedMessage> incomingMessages;
        Dictionary<int, NodeInfo> otherNodes;
        AutoResetEvent waitHandle = new AutoResetEvent(false);

        public Node(int port, int id, int x)
        {
            Console.WriteLine("BitCoin Node Base Constructor");
            otherNodes = new Dictionary<int, NodeInfo>();
            HelperFunctions.PopulateDictionaryWithNodes(ref otherNodes);
            incomingMessages = new Queue<ReceivedMessage>();
            messageLock = new Object();
            myState = new StateImpl();

            client = new Client(id);
            server = new Server(this, port);
            server.StartServer();
        }


        public Node(int port, int id)
        {
            otherNodes = new Dictionary<int, NodeInfo>();
            HelperFunctions.PopulateDictionaryWithNodes(ref otherNodes);
            incomingMessages = new Queue<ReceivedMessage>();
            messageLock = new Object();
            myState = new StateImpl();
            BitcoinImplUtilExt.Logger.SetFileName(id + "");
            client = new Client(id);
            server = new Server(this, port);
            LoadInitialState(id);
#if (VALIDATE)
            Validator.ValidateInitialChain(myState);
#endif
            server.StartServer();
        }

        void LoadInitialState(int id)
        {
            HelperFunctions.PopulateDictionaryWithTransactions();
           
            var treeMap = new TreeMap<BitcoinBlock>();
            HelperFunctions.PopulateBlocksMap(ref treeMap);
            myState.InitBtImpl(id, treeMap);
            BigInteger length;
            treeMap.Size(out length);
            Console.WriteLine(length + " blocks loaded.");
        }

        public void AddToQueue(ReceivedMessage message)
        {
            lock (messageLock)
            {
                
                if (message.message is Transaction)
                {
                    var bitcoinTx = Converter.ProtobufToBitcoinTransaction(((Transaction)message.message));
                    if (!transactionCache.ContainsKey(bitcoinTx))
                    {
                        BitcoinImplUtilExt.Logger.Info("TransactionAddedToQueue;" + bitcoinTx);
                        incomingMessages.Enqueue(message);
                        transactionCache.Add(bitcoinTx, 0);
                    }
                    else
                    {
                        Console.WriteLine("Skipping this transaction.");
                    }
                }
                else
                {
                    incomingMessages.Enqueue(message);
                }
            }
            //Added something in the queue, so we signal the main thread to 
            //process the queue
            waitHandle.Set();
        }

        // This is called in a while true loop by Program.cs
        // To avoid busy waiting, we make the thread go to sleep when the queue
        // is empty
        public void ProcessQueue()
        {
            if (incomingMessages.Count > 0)
            {
                IMessage toProcess = null;
                int from = 0;
                lock (messageLock)
                {
                    ReceivedMessage message = incomingMessages.Dequeue();
                    toProcess = message.message;
                    from = message.from;
                }
                if (toProcess == null)
                {
                    Console.WriteLine("Unrecognized");
                }
                else if (toProcess is Transaction)
                {
                    Transaction transactionMessage = (Transaction)toProcess;
                    totalTransactionsReceived += 1;
                    ReceivedTransactionMessage(transactionMessage, from);
                }
                else if (toProcess is Inv)
                {
                    Inv invMessage = (Inv)toProcess;
                    ReceivedInvMessage(invMessage, from);
                }
                else if (toProcess is Addr)
                {
                    Addr addrMessage = (Addr)toProcess;
                    ReceivedAddrMessage(addrMessage, from);
                }
                else if (toProcess is BlockMessage)
                {
                    BlockMessage block = (BlockMessage)toProcess;
                    ReceivedBlockMessage(block, from);
                }
                else if (toProcess is GetData)
                {
                    GetData getData = (GetData)toProcess;
                    ReceivedDataMessage(getData, from);
                }
                else if (toProcess is Connect)
                {
                    ReceivedConnectMessage(from);
                }
                else
                {
                    Console.WriteLine("Some unknown message received.");
                    Environment.Exit(0);
                }
            }
            else
            {
                //Validator.PrintCurrentChain(myState);
                //Since the queue is empty, we block the thread. 
                Console.WriteLine("Nothing to process.");
                BitcoinImplUtilExt.Logger.ForceFlush();
                waitHandle.WaitOne();
            }
        }

        public void ReceivedConnectMessage(int from)
        {
            Message_ConnectMsg connectMsg = new Message_ConnectMsg();
            var connectMessage = new Message(connectMsg);
            var time = HelperFunctions.GetEpochTime();
            Sequence<Packet> packets;
            myState.ProcMsgImpl(from, connectMessage,
                                Converter.ConvertUIntToBytes(time),
                                out packets);
            Console.WriteLine("Sending packets after receiving" +
                              " connect message " + packets.Elements.Length);
            for (int i = 0; i < packets.Elements.Length; i++)
            {
                SendPacket(packets.Elements[i]);
            }
        }

        public void ReceivedBlockMessage(BlockMessage message, int from)
        {
            Console.WriteLine("Received BLOCK message.");
            var bitcoinTransactions = new BitcoinTransaction[message.Transactions.Count];
            for (int i = 0; i < message.Transactions.Count; i++)
            {
                bitcoinTransactions[i] = Converter.ProtobufToBitcoinTransaction(message.Transactions[i]);
            }

            var seq = new Sequence<BitcoinTransaction>(bitcoinTransactions);
            BitcoinProof proof = new BitcoinProof(new BitcoinProof_BitcoinProof(
                Converter.ConvertUIntToBytes(message.Proof.Version),
                Converter.ConvertUIntToBytes(message.Proof.Time),
                Converter.ConvertUIntToBytes(message.Proof.Bits),
                Converter.ConvertUIntToBytes(message.Proof.Nonce)));

            var block = new BitcoinBlock(
                new BlockchainTypes.Block_Block<Sequence<byte>,
                BitcoinTransaction, BitcoinProof>(
                    new Sequence<byte>(message.Hash.ToByteArray()),
                    seq, proof)
            );
            Message_BlockMsg blockMsg = new Message_BlockMsg(block);
            var bitcoinMessage = new Message(blockMsg);
            var time = Converter
                .ConvertUIntToBytes(HelperFunctions.GetEpochTime());
            Sequence<Packet> packets;
            myState.ProcMsgImpl(from, bitcoinMessage, time, out packets);
            #if (VALIDATE)
            Validator.PrintCurrentChain(myState);
#endif

            //Console.WriteLine("Sending packets after receiving blocks " + packets.Elements.Length);

            for (int i = 0; i < packets.Elements.Length; i++)
            {
                SendPacket(packets.Elements[i]);
            }
        }

        public void ReceivedDataMessage(GetData getData, int from)
        {
            //Console.WriteLine("RECEIVED GETDATA MESSAGE! " + from);
            var hash = getData.Hash;
            var hashBytes = hash.ToByteArray();
            //Console.WriteLine(new Sequence<byte>(hashBytes));

            Message_GetDataMsg getDataMsg = new Message_GetDataMsg(new Sequence<byte>(hashBytes));
            var message = new Message(getDataMsg);
            Sequence<Packet> packets;
            var time = Converter
                .ConvertUIntToBytes(HelperFunctions.GetEpochTime());
            myState.ProcMsgImpl(from, message, time, out packets);
            //Console.WriteLine("Sending packets after getData message received " + packets.Elements.Length);
            for (int i = 0; i < packets.Elements.Length; i++)
            {
                SendPacket(packets.Elements[i]);
            }
        }

        public virtual void ReceivedAddrMessage(Addr address, int from)
        {
            Console.WriteLine("RECEIVED addr MESSAGE!");
            var length = address.Peers.Count;
            var arr = new int[length];
            for (int i = 0; i < length; i++)
            {
                arr[i] = address.Peers[i];
            }

            var addresses = new Sequence<int>(arr);
            var time = Converter
                .ConvertUIntToBytes(HelperFunctions.GetEpochTime());
            var message = new Message(new Message_AddrMsg(addresses));
            Sequence<Packet> packets;
            myState.ProcMsgImpl(from, message, time, out packets);

            for (int i = 0; i < packets.Elements.Length; i++)
            {
                SendPacket(packets.Elements[i]);
            }
        }

        public void ReceivedInvMessage(Inv inv, int from)
        {
            //Console.WriteLine("RECEIVED INV MESSAGE! " + from);
            var length = inv.Hashes.Count;
            var arr = new Sequence<byte>[length];

            for (int i = 0; i < length; i++)
            {
                var bytes = inv.Hashes[i].HashDigits.ToByteArray();
                arr[i] = new Sequence<byte>(bytes);
            }

            var hashes = new Sequence<Sequence<byte>>(arr);
            var message = new Message(new Message_InvMsg(hashes));
            var time = Converter
                .ConvertUIntToBytes(HelperFunctions.GetEpochTime());
            Sequence<Packet> packets;

            myState.ProcMsgImpl(from, message, time, out packets);
            for (int i = 0; i < packets.Elements.Length; i++)
            {
                SendPacket(packets.Elements[i]);
            }
        }

        public virtual void ReceivedTransactionMessage(Transaction transaction, int from)
        {
            Console.WriteLine("RECEIVED TRANSACTION MESSAGE!");
            var bitcoinTx = Converter.ProtobufToBitcoinTransaction(transaction);
            Console.WriteLine("\n" + bitcoinTx + "\n");
            var message = new Message(new Message_TxMsg(bitcoinTx));
            var time = Converter
                .ConvertUIntToBytes(HelperFunctions.GetEpochTime());
            Sequence<Packet> packets;
            BitcoinImplUtilExt.Logger.Info("TransactionProcessedByQueue;" + bitcoinTx);
            myState.ProcMsgImpl(from, message, time, out packets);

            foreach (Packet packet in packets.Elements)
            {
                SendPacket(packet);
            }

            Console.WriteLine("The size of the txPool is " + myState.txPool.size);
            if (myState.txPool.size % 2 == 0)
            {
                Console.WriteLine("Going to MINT BLOCKS here " + totalTransactionsReceived);
                MintBlocks();
            }
        }

        public void MintBlocks()
        {
            var timestamp = HelperFunctions.GetEpochTime();
            Sequence<Packet> packets;
            BitcoinImplUtilExt.Logger.Info("MintBlock;begin;");
            myState.ProcMintTImpl(Converter.ConvertUIntToBytes(timestamp), out packets);
            BitcoinImplUtilExt.Logger.Info("MintBlock;end;");
            Console.WriteLine("MINTED BLOCK : Packets " + packets.Elements.Length);
#if (VALIDATE)
            Validator.PrintCurrentChain(myState);
#endif
            for (int i = 0; i < packets.Elements.Length; i++)
            {
                SendPacket(packets.Elements[i]);
            }
        }

        public void SendPacket(Packet packet)
        {
            BigInteger sendTo = packet.dtor_dst;
            BigInteger from = packet.dtor_src;
            var message = packet.dtor_msg;
            NodeInfo recipient = otherNodes.GetValueOrDefault((int)sendTo);
            if (message.is_BlockMsg)
            {
                client.SendBlockMessage(message, recipient);
            }
            else if (message.is_InvMsg)
            {
                client.SendInvMessage(message, recipient);
            }
            else if (message.is_TxMsg)
            {
                client.SendTransactionMessage(message, recipient);
            }
            else if (message.is_AddrMsg)
            {
                //Console.WriteLine("SENDING ADDR MESSAGE. " + from + " " + sendTo);
                client.SendAddrMessage(message, recipient);
            }
            else if(message.is_ConnectMsg)
            {
                client.SendConnectMessage(message, recipient);
            }
            else if (message.is_GetDataMsg)
            {
                client.SendGetDataMessage(message, recipient);
            }
        }

    }
}

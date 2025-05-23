using System;
using System.Net;
using System.Net.Sockets;
using Google.Protobuf;
using Google.Protobuf.Messages;
using System.IO;
using Bitcoin;
using System.Numerics;
using Dafny;

namespace networkLayer
{
    public class Client
    {
        Int32 myID;

        public Client(Int32 id)
        {
            myID = id;
        }

        // 1. Takes a Google Protobuf Object
        // 2. Based on the Class of the Object, assigns a Message Type
        // 3. Serializes this and assigns it as the Byte Payload of the Wrapper Message
        // 4. Serializes the whole Wrapper Message and returns the byte array
        public byte[] Serialize(IMessage m)
        {
            byte[] message;
            using (var stream = new MemoryStream())
            {
                m.WriteTo(stream);
                message = stream.ToArray();
            }
            
            WrapperMessage.Types.MessageType t;

            if (m is Transaction)
            {
                t = WrapperMessage.Types.MessageType.Transaction;
            }
            else if (m is Addr)
            {
                t = WrapperMessage.Types.MessageType.Addr;
            }
            else if (m is Inv)
            {
                t = WrapperMessage.Types.MessageType.Inv;
            }
            else if (m is BlockMessage)
            {
                t = WrapperMessage.Types.MessageType.Block;
            }
            else if (m is GetData)
            {
                t = WrapperMessage.Types.MessageType.Getdata;
            }
            else if (m is Connect)
            {
                t = WrapperMessage.Types.MessageType.Connect;
            }
            else
            {
                t = WrapperMessage.Types.MessageType.Unknown;
            }

            byte[] wrapper = new WrapperMessage {
                Type = t,
                From = myID,
                Payload = ByteString.CopyFrom(message)
            }.ToByteArray();

            return wrapper;
        }

        public void SendConnectMessage(Message message, NodeInfo recipient)
        {
            Connect connectMsg = new Connect();
            var toPrint = "Sending an CONNECT message to " +
               recipient.getIPAddress() + "::" + recipient.getPort();
            Console.WriteLine(toPrint);
            SendMessage(connectMsg, recipient.getIPAddress(), recipient.getPort());
        }

        public void SendTransactionMessage(Message message, NodeInfo recipient)
        {
            Transaction txMsg = new Transaction();
            var bitcoinTransaction = message.dtor_t;
            var arr = new BitcoinTransaction[1];
            arr[0] = bitcoinTransaction;
            var sequence = new Sequence<BitcoinTransaction>(arr);
            txMsg = Converter.DafnyToProtobufTransactions(sequence)[0];
            SendMessage(txMsg, recipient.getIPAddress(), recipient.getPort());
        }

        public void SendAddrMessage(Message message, NodeInfo recipient)
        {
            Addr addrMessage = new Addr();
            var peers = message.dtor_ps;

            for (int i = 0; i < peers.Length; i++)
            {
                addrMessage.Peers.Add((int)peers.Elements[i]);
            }
            var toPrint = "Sending an ADDR message to " +
                recipient.getIPAddress() + "::" + recipient.getPort();
            Console.WriteLine(toPrint);
            SendMessage(addrMessage, recipient.getIPAddress(), recipient.getPort());
        }

        public void SendGetDataMessage(Message message, NodeInfo recipient)
        {
            var hash = message.dtor_h;
            var hashbytes = hash.Elements;
            GetData getDataMsg = new GetData();
            getDataMsg.Hash = ByteString.CopyFrom(hashbytes);

            var toPrint = "Sending a GETDATA message to " +
                recipient.getIPAddress() + "::" + recipient.getPort();
            //Console.WriteLine(toPrint);
            SendMessage(getDataMsg, recipient.getIPAddress(), recipient.getPort());
        }

        public void SendInvMessage(Message message, NodeInfo recipient)
        {
            var hashes = message.dtor_s;
            var length = hashes.Length;

            Inv invMsg = new Inv();
            var i = 0;

            foreach (Sequence<byte> hash in hashes.Elements)
            {
                ByteString obj = ByteString.CopyFrom(hash.Elements);
                Hash element = new Hash
                {
                    HashDigits = obj
                };

                invMsg.Hashes.Add(element);
                i++;
            }
            var toPrint = "Sending an INV message to " 
                + recipient.getIPAddress() + "::" + recipient.getPort();
            //Console.WriteLine(toPrint);
            SendMessage(invMsg, recipient.getIPAddress(), recipient.getPort());
        }

        public void SendBlockMessage(Message message, NodeInfo recipient)
        {
            var block = message.dtor_b;
            var seq = block.dtor_txs;
            var bitcoinProof = block.dtor_proof;
            var nonce = Converter.ConvertBytesToUInt(bitcoinProof.dtor_nonce);
            var time = Converter.ConvertBytesToUInt(bitcoinProof.dtor_time);
            var version = Converter.ConvertBytesToUInt(bitcoinProof.dtor_version);
            var bits = Converter.ConvertBytesToUInt(bitcoinProof.dtor_bits);

            BitcoinProofMessage proof = new BitcoinProofMessage
            {
                Nonce = nonce,
                Version = version,
                Time = time,
                Bits = bits
            };

            var prevHash = block.dtor_prevBlockHash.Elements;
            var byteHash = ByteString.CopyFrom(prevHash);
            BlockMessage blockMsg = new BlockMessage
            {  
                Hash = byteHash,
                Proof = proof
            };

            var transactions = Converter.DafnyToProtobufTransactions(seq);

            for (int i = 0; i < transactions.Length; i++)
            {
                blockMsg.Transactions.Add(transactions[i]);
            }

            var toPrint = "Sending a block message to " +
                recipient.getIPAddress() + "::" + recipient.getPort();
            //Console.WriteLine(toPrint);
            //Console.WriteLine("The number of transactions that " +
            //                  "are part of the block " + transactions.Length);
            SendMessage(blockMsg, recipient.getIPAddress(), recipient.getPort());
        }

        public void SendMessage(IMessage message, string address, int port)
        {
            var client = new UdpClient();
            var endPoint = new IPEndPoint(IPAddress.Parse(address), port);
            client.Connect(endPoint);
            var serializedMessage = Serialize(message);
            client.Send(serializedMessage, serializedMessage.Length);
            var receivedData = client.Receive(ref endPoint);
            client.Close();
        }
    }
}

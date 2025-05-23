using System;
using System.Net;
using System.Net.Sockets;
using System.Text;
using System.Threading;
using System.Collections.Generic;
using Google.Protobuf;
using Google.Protobuf.Messages;

namespace networkLayer
{
    public class ReceivedMessage {
        public IMessage message;
        public int from;
    }

    public class Server
    {

        public Dictionary<byte[], string> mapToIp = new Dictionary<byte[], string>();
        int port = 9050; //Defaults
        Node node;

        public Server(Node node, int port)
        {
            this.node = node;
            this.port = port;
        }

        // This function starts the server
        // Listening on port specified by user
        public void Listen()
        {
            byte[] response = new byte[1024];
            IPEndPoint ipep = new IPEndPoint(IPAddress.Any, port);
            UdpClient newsock = new UdpClient(ipep);
            IPEndPoint sender = new IPEndPoint(IPAddress.Any, 0);

            while(true)
            {
                response = newsock.Receive(ref sender);
                ReceivedMessage obj = new ReceivedMessage();
                IMessage m = Deserialize(response, ref obj.from);

                obj.message = m;
                node.AddToQueue(obj);
                newsock.Send(response, response.Length, sender);
                //newsock.Close();
                //Console.WriteLine("Closed connection, new one will begin.");
            }
        }

        // Deserializes wrapper message
        // Based on the message type, deserializes and 
        // returns respective object 
        public IMessage Deserialize(byte [] data, ref int from)
        {
            WrapperMessage m = WrapperMessage.Parser.ParseFrom(data);
            from = m.From;

            if (m.Type.Equals(WrapperMessage.Types.MessageType.Transaction)) 
            {
                return Transaction.Parser.ParseFrom(m.Payload);
            }
            else if (m.Type.Equals(WrapperMessage.Types.MessageType.Inv))
            {
                return Inv.Parser.ParseFrom(m.Payload);
            }
            else if (m.Type.Equals(WrapperMessage.Types.MessageType.Addr))
            {
                return Addr.Parser.ParseFrom(m.Payload);
            }
            else if (m.Type.Equals(WrapperMessage.Types.MessageType.Connect))
            {
                return Connect.Parser.ParseFrom(m.Payload);
            }
            else if (m.Type.Equals(WrapperMessage.Types.MessageType.Block))
            {
                return BlockMessage.Parser.ParseFrom(m.Payload);
            }
            else if (m.Type.Equals(WrapperMessage.Types.MessageType.Getdata))
            {
                return GetData.Parser.ParseFrom(m.Payload);
            }
            else
            {
                return null;
            }
        }

        // Called by the node to start listening
        public void StartServer()
        {
            Thread t = new Thread(new ThreadStart(Listen));
            t.Start();
            t.IsBackground = true;
        }

    }
}

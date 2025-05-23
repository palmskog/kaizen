using System;
using System.Numerics;


/**
 * This will be the entry point of this program.
 * Based on the arguments passed, we will either start the BroadcastSender or
 * a Node
 */
namespace networkLayer
{
    public class Program
    {
        public static void Main(string[] args)
        {
            int type = Int32.Parse(args[0]);
         
            if (type == 1)
            {
                int port = Int32.Parse(args[1]);
                int id = Int32.Parse(args[2]);
                Console.WriteLine("Initializing a Node here...");
                Console.WriteLine(port);
                Console.WriteLine(id);
                Node myself = new Node(port, id);
                //todo: fix the while true hack
                while (true)
                {
                    myself.ProcessQueue();
                }
            }
            else if (type == 2)
            {
                Console.WriteLine("Initializing bitcoin node....");
                int port = Int32.Parse(args[1]);
                int id = Int32.Parse(args[2]);
                BitcoinNode bitcoinNode = new BitcoinNode(port, id);
                while (true)
                {
                    bitcoinNode.ProcessQueue();
                }
            }
            else
            {
                Console.WriteLine("Initializing the Broadcast Sender... " +
                                  "Hope you have only started it after initializing " +
                                  "all nodes in cluster.json. Will get socket errors, " +
                                  "otherwise.");
                WorkloadGenerator broadcastSender = new WorkloadGenerator();
                broadcastSender.InitializeCluster();
                broadcastSender.broadcastAddresses();
                broadcastSender.broadcastTransactions();
            }
        }
    }
}

using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using Newtonsoft.Json.Linq;
using Google.Protobuf;
using Google.Protobuf.Messages;

namespace networkLayer
{
    public class BitcoinNode : Node
    {
        String key;
        int num;

        public BitcoinNode(int port, int id) : base(port, id, 1)
        {
            num = 0;
            Console.WriteLine("BitcoinNode Constructor");
           
            int myId = id;
            JObject nodeData = JObject.Parse(File.ReadAllText(HelperFunctions.GetClusterDataFile()));
            JArray allNodes = (JArray)nodeData.GetValue("nodes");

            for (int i = 0; i < allNodes.Count; i++)
            {
                JObject obj = (JObject)allNodes[i];
                int readId = (int)obj.GetValue("id");
                if (readId == myId) {
                    this.key = (string)obj.GetValue("key");    
                    String address = (string)obj.GetValue("address");
                }
            }   
        }

        public override void ReceivedAddrMessage(Addr address, int from) {
            Console.WriteLine("IGNORING");
        }

        public override void ReceivedTransactionMessage(Transaction transaction, int from)
        {
            // Add logic here
            if (transaction.TxIns.Count != 1) {
                Console.WriteLine("More than one TxIn in the transaction. Shutting down");
                Environment.Exit(13);
            }
            if (transaction.TxOuts.Count != 1)
            {
                Console.WriteLine("More than one TxIn in the transaction. Shutting down");
                Environment.Exit(13);
            }

            TxIn @in = transaction.TxIns[0];
            TxOut @out = transaction.TxOuts[0];

            string prevhash = @in.PrevoutHash;
            uint previndex = @in.PrevoutN;
            string address = @out.ScriptPublicKey;
            double amount = @out.Value / Math.Pow(10.0, 8.0);

            string command = "sudo /var/bitcoin/bitcoin-1/src/bitcoin-cli -regtest ";
            command += " createsignrawtransaction '''";
            command += "[{ \\\"txid\\\": ";
            command += "\\\"'"+ prevhash+"'\\\" , ";
            command += "\\\"vout\\\": '0' }] ''' ''' {";
            command += " \\\"'" + address + "'\\\": ";
            command += " " + amount + "} ''' '[\\\"" + this.key ;
            command += "\\\"]'";

            Console.WriteLine("Command: " + command);
            ExecuteCommand(command);

            if (num == 0) {
                command = "sudo /var/bitcoin/bitcoin-1/src/bitcoin-cli -regtest generate 1";    
                Console.WriteLine("Command: " + command);
                ExecuteCommand(command);
            }
            num = 1;


        }
        //'''[{ "txid": "'hash'" , "vout": '0' }] '''''' { "'address'":  50} ''' '["key"]'
        //''' [ { "txid": "'$TX_ID'",  "vout": '0' } ] ''' '''{ "'$NEW_ADDR'":  49.99999}'''  '["cVQNCs2rgXuyTceuoN9i13sWCxKXKB7Fjy3xZYLuBULqibjDiqx8"]';

        public static void ExecuteCommand(string command)
        {
            Process proc = new System.Diagnostics.Process();
            proc.StartInfo.FileName = "/bin/bash";
            proc.StartInfo.Arguments = "-c \" " + command + " \"";
            proc.StartInfo.UseShellExecute = false;
            proc.StartInfo.RedirectStandardOutput = true;
            proc.Start();

            while (!proc.StandardOutput.EndOfStream)
            {
                Console.WriteLine(proc.StandardOutput.ReadLine());
            }
        }

    }
}

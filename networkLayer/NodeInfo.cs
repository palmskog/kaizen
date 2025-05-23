using System;
using System.IO;
using System.Collections.Generic;
using Newtonsoft.Json.Linq;

namespace networkLayer
{
    public class NodeInfo
    {

        String ipAddress;
        int port;
        String address;
        String key;
        List<UnspentTransaction> unspentTransactions;

        public NodeInfo(String ipAddress, int port)
        {
            this.ipAddress = ipAddress;
            this.port = port;
        }

        public NodeInfo(String ipAddress, int port, String address, String key, String path)
        {
            this.ipAddress = ipAddress;
            this.port = port;
            this.address = address;
            this.key = key;
            unspentTransactions = new List<UnspentTransaction>();
            loadUnspentTransactions(path);
        }

        public void loadUnspentTransactions(String path) {
            
            JArray jsonTransactions = JArray.Parse(File.ReadAllText(path));
            for (int i = 0; i < jsonTransactions.Count; i++)
            {
                JObject obj = (JObject)jsonTransactions[i];
                string id = (string)obj.GetValue("txid");
                double amount = (double)obj.GetValue("amount");
                uint vout = (uint)obj.GetValue("vout");

                UnspentTransaction transaction = new UnspentTransaction(id, amount, vout);
                unspentTransactions.Add(transaction);
            }  

        }

        public String getIPAddress()
        {
            return ipAddress;
        }

        public int getPort()
        {
            return port;
        }

        public String getAddress() 
        {
            return address;
        }

        public String getKey()
        {
            return key;
        }

        public List<UnspentTransaction> getUnspentTransactions()
        {
            return unspentTransactions;
        }
    }
}

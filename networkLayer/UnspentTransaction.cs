using System;

namespace networkLayer
{
    public class UnspentTransaction
    {

        string txId;
        double amount;
        uint vOut;


        public UnspentTransaction(string txId, double amount, uint vOut)
        {
            this.txId = txId;
            this.amount = amount;
            this.vOut = vOut;
        }

        public string getTxId()
        {
            return txId;
        }

        public double getAmount()
        {
            return amount;
        }

        public uint getVOut()
        {
            return vOut;
        }
    }
}

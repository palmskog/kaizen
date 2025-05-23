using System;
using System.Numerics;
using Dafny;
using System.Text;
using Bitcoin;
using Google.Protobuf.Messages;
using Google.Protobuf;

namespace networkLayer
{
    public static class Converter
    {
        public static Sequence<byte> ConvertStringToBytes(string text)
        {
            byte[] bytes = Encoding.ASCII.GetBytes(text);
            return new Sequence<byte>(bytes);
        }

        public static Sequence<BigInteger> ConvertBytesToBigIntegers(byte[] bytes)
        {
            BigInteger[] array = new BigInteger[bytes.Length];
            int i = 0;
            foreach (byte b in bytes)
            {
                array[i] = (BigInteger)bytes[i];
                i++;
            }
            Sequence<BigInteger> sequence = new Sequence<BigInteger>(array);
            return sequence;
        }

        public static byte[] ConvertBigIntegersToBytes(Sequence<BigInteger> sequence)
        {
            byte[] bytes = new byte[sequence.Length];
            for (int i = 0; i < sequence.Length; i++)
            {
                bytes[i] = (byte)sequence.Select(i);
            }
            return bytes;
        }

        public static int ConvertBigIntegersToInt(Sequence<BigInteger> sequence)
        {
            byte[] bytes = ConvertBigIntegersToBytes(sequence);
            int value = BitConverter.ToInt32(bytes, 0);
            return value;
        }

        public static uint ConvertBytesToUInt(Sequence<byte> sequence)
        {
            byte[] bytes = sequence.Elements;
            uint value = BitConverter.ToUInt32(bytes, 0);
            return value;
        }

        public static string ConvertBigIntegersToString(Sequence<byte> sequence)
        {
            byte[] bytes = sequence.Elements;
            string value = Encoding.ASCII.GetString(bytes);
            return value;
        }

        public static Sequence<byte> ConvertUIntToBytes(uint integer)
        {
            byte[] bytes = BitConverter.GetBytes(integer);
            return new Sequence<byte>(bytes);
        }

        public static Sequence<byte> ConvertULongToBytes(ulong integer)
        {
            byte[] bytes = BitConverter.GetBytes(integer);
            return new Sequence<byte>(bytes);
        }

        public static Sequence<byte> ConvertBigIntegerToBytes(BigInteger integer)
        {
            byte[] bytes = integer.ToByteArray();
            return new Sequence<byte>(bytes);
        }

        public static ulong ConvertBytesToULong(Sequence<byte> sequence)
        {
            byte[] bytes = sequence.Elements;
            ulong value = BitConverter.ToUInt64(bytes, 0);
            return value;
        }

        // The hashes of transactions are handled different from the rest
        // We only use unspent transactions as our prev_hashes. 
        // On startup, we put all the unspent transactions in memory, with their
        // given txID and the Dafny returned hash. We use this dictionary for lookups
        // In the protobuf we send the string, and to Dafny we send the seq<ints>
        public static Transaction[] DafnyToProtobufTransactions(Sequence<BitcoinTransaction> txs)
        {
            Transaction[] toReturn = new Transaction[txs.Length];
            for (int i = 0; i < txs.Elements.Length; i++)
            {
                BitcoinTransaction tx = txs.Elements[i];
                //Console.WriteLine(tx);
                Transaction protobufTx = new Transaction();
                if (tx.dtor_version.Length > 0)
                {
                    protobufTx = new Transaction
                    {
                        Version = ConvertBytesToUInt(tx.dtor_version),
                        Time = ConvertBytesToUInt(tx.dtor_locktime)
                    };
                }
                else
                {
                    Console.WriteLine("This shouldn't be empty. Aborting.");
                    Console.WriteLine(tx);
                    Environment.Exit(-1);
                }
                var vins = tx.dtor_ins.Length;
                for (int j = 0; j < vins; j++)
                {
                    BitcoinTxIn txIn = tx.dtor_ins.Elements[j];
                    string hashOfTransaction;
                    HelperFunctions.
                                   DafnyToBitcoinTransactionHash.
                                   TryGetValue(txIn.dtor_prevout__hash, 
                                               out hashOfTransaction);

                    TxIn transactionIn = new TxIn();
                    if (txIn.dtor_prevout__n.Length > 0)
                    {
                        transactionIn.PrevoutN = ConvertBytesToUInt(txIn.dtor_prevout__n);
                        transactionIn.PrevoutHashBytes = ByteString.CopyFrom(txIn.dtor_prevout__hash.Elements);
                        transactionIn.Sequence = ConvertBytesToUInt(txIn.dtor_sequence);
                        transactionIn.Script = ConvertBigIntegersToString(txIn.dtor_scriptsig);
                    }

                    protobufTx.TxIns.Add(transactionIn);
                }
                var vouts = tx.dtor_outs.Length;
                for (int j = 0; j < vouts; j++)
                {
                    BitcoinTxOut txOut = tx.dtor_outs.Elements[j];
                    TxOut transactionOut = new TxOut
                    {
                        Value = ConvertBytesToULong(txOut.dtor_value),
                        ScriptPublicKey = ConvertBigIntegersToString(txOut.dtor_scriptpubkey)
                    };
                    protobufTx.TxOuts.Add(transactionOut);
                }
                toReturn[i] = protobufTx;
            }
            return toReturn;
        }

        public static BitcoinTransaction ProtobufToBitcoinTransaction(Transaction transaction)
        {
            var txInLength = transaction.TxIns.Count;
            var txOutLength = transaction.TxOuts.Count;

            BitcoinTxIn[] bitcoinTxIns = new BitcoinTxIn[txInLength];
            BitcoinTxOut[] bitcoinTxOuts = new BitcoinTxOut[txOutLength];
            byte[] empty = new byte[0];
            for (int i = 0; i < txInLength; i++)
            {
                uint prev_n = transaction.TxIns[i].PrevoutN;
                uint sequence = transaction.TxIns[i].Sequence;
                string script = transaction.TxIns[i].Script;
                byte[] previous_hash_bytes = transaction.TxIns[i].PrevoutHashBytes.ToByteArray();

                // If the size of previous hash bytes is 0 then it is a coinbase tx
                if (previous_hash_bytes.Length > 0) 
                {
                    bitcoinTxIns[i] = new BitcoinTxIn(new BitcoinTxIn_BitcoinTxIn(
                        new Sequence<byte>(previous_hash_bytes),
                        ConvertUIntToBytes(prev_n),
                        ConvertStringToBytes(script),
                        ConvertUIntToBytes(sequence)
                    ));
                }
                else
                {
                    bitcoinTxIns[i] = new BitcoinTxIn(new BitcoinTxIn_BitcoinTxIn(
                        new Sequence<byte>(empty),
                        new Sequence<byte>(empty),
                        new Sequence<byte>(empty),
                        new Sequence<byte>(empty)));
                }
            }

            for (int i = 0; i < txOutLength; i++)
            {
                ulong value = transaction.TxOuts[i].Value;
                string hash = transaction.TxOuts[i].ScriptPublicKey;
                bitcoinTxOuts[i] = new BitcoinTxOut(new BitcoinTxOut_BitcoinTxOut(
                    ConvertULongToBytes(value),
                    ConvertStringToBytes(hash)
                ));
            }

            var bitcoinTx = new BitcoinTransaction(
                new BitcoinTransaction_BitcoinTransaction(
                    ConvertUIntToBytes(transaction.Version),
                    new Sequence<BitcoinTxIn>(bitcoinTxIns),
                    new Sequence<BitcoinTxOut>(bitcoinTxOuts),
                    ConvertUIntToBytes(transaction.Time)
                ));

            return bitcoinTx;
        }

    }
}

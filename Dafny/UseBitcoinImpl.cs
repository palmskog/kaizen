using System;
using System.Numerics;
using Bitcoin;
using BitcoinImpl;

public class UseBitcoinImpl
{

    public static Dafny.Sequence<char> FromString(string s) {
      return new Dafny.Sequence<char>(s.ToCharArray());
    }

    public static void Main()
    {
      Console.WriteLine("creating state");
      var s = new StateImpl();
      s.InitImpl(1);

      Console.WriteLine("creating transaction");
      var emptyIntSeq = new Dafny.Sequence<byte>(new byte[0]);
      var emptyTxInSeq = new Dafny.Sequence<BitcoinTxIn>(new BitcoinTxIn[0]);
      var emptyTxOutSeq = new Dafny.Sequence<BitcoinTxOut>(new BitcoinTxOut[0]);
      var txtx = new BitcoinTransaction_BitcoinTransaction(emptyIntSeq, emptyTxInSeq, emptyTxOutSeq, emptyIntSeq);
      var tx = new BitcoinTransaction(txtx);

      Console.WriteLine("creating message");
      var msg = new Message(new Message_TxMsg(tx));

      Console.WriteLine("calling ProcMsg on state");
      Dafny.Sequence<Packet> pt;
      s.ProcMsgImpl(2, msg, emptyIntSeq, out pt);

      Console.WriteLine("printing first element in transaction pool");
      Console.WriteLine(s.txPool.elem);
    }

}

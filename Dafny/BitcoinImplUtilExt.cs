using System;
using System.Collections.Generic;
using System.Collections;
using System.IO;
using System.Linq;
using System.Numerics;
using System.Runtime.Serialization.Formatters.Binary;
using System.Runtime.Serialization;
using System.Security.Cryptography;
using System.Text;
using BlockchainTypes;
using Bitcoin;


namespace @BitcoinImplUtilExt
{


	public partial class @Util
	{


		// convert from C# strings to Dafny strings
		public static void @FromString(string s, out Dafny.Sequence<char> ch)
		{
			ch = new Dafny.Sequence<char>(s.ToCharArray());
		}

		public static void @convertBigInttoSeq(BigInteger integer, out Dafny.Sequence<byte> seq) {
			seq = new Dafny.Sequence<byte>(integer.ToByteArray());
		}

		public static void ConvertULongToByteSeq(ulong integer, out Dafny.Sequence<byte> sequence)
		{
			sequence = new Dafny.Sequence<byte>(BitConverter.GetBytes(integer)); 
		}

		public static void convertUInttoSeq (uint integer, out Dafny.Sequence<byte> o)
		{
			o = new Dafny.Sequence<byte>(BitConverter.GetBytes(integer));
		}

		public static void convertSeqToBigInt (Dafny.Sequence<byte> seq, out BigInteger bigInteger)
		{
			bigInteger = new BigInteger(seq.Elements.Concat(new byte[] { 0 }).ToArray());
		}

		// The last block in the sequence is the last added block. So instead of traversing in a for loop, we should find the last block and then traverse backwards until we find the fork.
		public static void ForkRoot(Dafny.Sequence<Block<Dafny.Sequence<byte>,BitcoinTransaction,BitcoinProof>> bc1,
			Dafny.Sequence<Block<Dafny.Sequence<byte>,BitcoinTransaction,BitcoinProof>> bc2,
			out Block_Block<Dafny.Sequence<byte>,BitcoinTransaction,BitcoinProof> root)
		{	    
			int j = 0;
			Dafny.Sequence<byte> hash;
			Dictionary<Dafny.Sequence<byte>, int> map = new Dictionary<Dafny.Sequence<byte>, int>();

			foreach (Block<Dafny.Sequence<byte>,BitcoinTransaction,BitcoinProof> block1 in bc1.Elements)
			{	
				@BitcoinImplUtil.@Util.@HashBImpl(block1, out hash);
				j++;
				map.Add(hash, 0);
			}
	    	// traversing backwards from the other chain to find the root
			
			for(int i = bc2.Length - 1; i >= 0 ; i--)
			{
				@BitcoinImplUtil.@Util.@HashBImpl(bc2.Select(i), out hash);
				try
				{
					map.Add(hash, 0);
				}
				catch (ArgumentException)
				{
		    		// We don't need to do anything with the ArgumentException --> this is the common block
					root = ((Block_Block<Dafny.Sequence<byte>,BitcoinTransaction,BitcoinProof>) bc2.Select(i)._D);
					return;
				}
			}
			var emptyTrSeq = new Dafny.Sequence<Bitcoin.BitcoinTransaction>(new Bitcoin.BitcoinTransaction[0]);
			var emptyHashSeq = new Dafny.Sequence<byte>(new byte[0]);
			var p = new Bitcoin.BitcoinProof_BitcoinProof(emptyHashSeq, emptyHashSeq, emptyHashSeq, emptyHashSeq);
			var emptyProofSeq = new Bitcoin.BitcoinProof(p);
			root = new BlockchainTypes.Block_Block<Dafny.Sequence<byte>, Bitcoin.BitcoinTransaction, Bitcoin.BitcoinProof>(emptyHashSeq, emptyTrSeq, emptyProofSeq);
		}

		public static void @getTransactionValue(BitcoinTransaction transaction, Dafny.Sequence<Block<Dafny.Sequence<byte>,BitcoinTransaction,BitcoinProof>> bc, out BigInteger value)
		{
			value = 0;
			BigInteger v = 0;
			foreach (BitcoinTxOut out_ in ((Bitcoin.@BitcoinTransaction_BitcoinTransaction)transaction._D).outs.Elements) {
				convertSeqToBigInt(((Bitcoin.BitcoinTxOut_BitcoinTxOut)out_._D).value, out v); 
				value += v;
			}
			return;
		}	

	         public static void @FCRAuxImpl(Dafny.Sequence<Block<Dafny.Sequence<byte>,BitcoinTransaction,BitcoinProof>> bc,
					     out BigInteger cw,
					     out BigInteger tc)
	         {
		     // chain weight
		     cw = new BigInteger(0);
		     // total number of transactions
		     tc = new BigInteger(0);
		 }

		public static void @FCRImpl(Dafny.Sequence<Block<Dafny.Sequence<byte>,BitcoinTransaction,BitcoinProof>> bc1,
			Dafny.Sequence<Block<Dafny.Sequence<byte>,BitcoinTransaction,BitcoinProof>> bc2,
			out bool b)
		{
			Logger.Info("FCRImpl;start;"+bc1.Length+";"+bc2.Length+";");

			for(int i = bc1.Length - 1; i >= 0; i--) {
				Dafny.Sequence<byte> blockHash;
				@BitcoinImplUtil.@Util.@HashBImpl(bc1.Elements[i], out blockHash);
			}

			for(int i = bc2.Length - 1; i >= 0; i--) {
				Dafny.Sequence<byte> blockHash;
				@BitcoinImplUtil.@Util.@HashBImpl(bc2.Elements[i], out blockHash);
			}

			Block_Block<Dafny.Sequence<byte>,BitcoinTransaction,BitcoinProof> root;
			ForkRoot(bc1, bc2, out root);

			Block<Dafny.Sequence<byte>,BitcoinTransaction,BitcoinProof> rootB = new Block<Dafny.Sequence<byte>,BitcoinTransaction,BitcoinProof>(root);

			if (root.prevBlockHash.Length == 0 && root.txs.Length == 0 && root.proof.dtor_nonce.Length == 0) {
				b = false;
				Console.WriteLine("There is no connection between the two chains");
				Logger.Info("FCRImpl;end;"+bc1.Length+";"+bc2.Length+";false;noconnection");
				return; //There is no connection between them. It is unlikely that this will happen
			}

			BigInteger blockChain1Weight = 0;
			BigInteger blockChain2Weight = 0;

			int blocksInBC1 = bc1.Elements.Length;
			int blocksInBC2 = bc2.Elements.Length;

			int blockChain1Txs = 0;
			int blockChain2Txs = 0;

			Dafny.Sequence<byte> rootHash;
			@BitcoinImplUtil.@Util.@HashBImpl(rootB, out rootHash);

			Dafny.Sequence<byte> tHash;
			@BitcoinImplUtil.@Util.@HashBImpl(bc1.Select(bc1.Length - 1), out tHash);

			bool condition = false;
			compareHashes(rootHash, tHash, out condition);

			for(int i = bc1.Length - 1; i >= 0 && !condition ; i--)
			{
				Dafny.Sequence<BitcoinTransaction> currTxs = ((Block_Block<Dafny.Sequence<byte>,BitcoinTransaction,BitcoinProof>) bc1.Select(i)._D).txs;
				foreach(BitcoinTransaction currTx in currTxs.Elements) {
					BigInteger sum = 0;
					getTransactionValue(currTx, bc1, out sum);
					blockChain1Weight += sum;
					blockChain1Txs += 1;
				} 
				if (i - 1 >=0) {
					@BitcoinImplUtil.@Util.@HashBImpl(bc1.Select(bc1.Length - 1), out tHash);
					compareHashes(rootHash, tHash, out condition);
				}
			}

			condition = false;
			@BitcoinImplUtil.@Util.@HashBImpl(bc2.Select(bc2.Length - 1), out tHash);
			compareHashes(rootHash, tHash, out condition);

			for(int i = bc2.Length - 1; i >= 0 && !condition ; i--)
			{
				Dafny.Sequence<BitcoinTransaction> currTxs = ((Block_Block<Dafny.Sequence<byte>,BitcoinTransaction,BitcoinProof>) bc2.Select(i)._D).txs;
				foreach(BitcoinTransaction currTx in currTxs.Elements) {
					BigInteger sum = 0;
					getTransactionValue(currTx, bc2, out sum);
					blockChain2Weight += sum;
					blockChain2Txs += 1;
				}
				if (i - 1 >=0) {
					@BitcoinImplUtil.@Util.@HashBImpl(bc2.Select(i - 1), out tHash);
					compareHashes(rootHash, tHash, out condition);
				}
			}

			Logger.Info("FCRImpl;end;"+bc1.Length+";"+bc2.Length+";");
			if (blockChain1Weight > blockChain2Weight) {
				b = true; 
				return;
			}  
			else if (blockChain1Weight < blockChain2Weight) {b = false; return;} 

			if (blockChain1Txs > blockChain2Txs) {b = true; return; }  
			else if (blockChain1Txs < blockChain2Txs) {b = false; return;} 

			if (blocksInBC1 > blocksInBC2) {b = true; return; }  
			else if (blocksInBC2 > blocksInBC1) {b = false; return;} 

			b = true;
		}

		public static void @compareHashes(Dafny.Sequence<byte> hash1,
			Dafny.Sequence<byte> hash2,
			out bool vb)
		{
			if (hash1.Length != hash2.Length)  {
				vb = false;
				return;
			}

			var ihash1 = new BigInteger(hash1.Elements);
			var ihash2 = new BigInteger(hash2.Elements);

			if (BigInteger.Compare(ihash1, ihash2) != 0) {
				vb = false;
			} else {
				vb = true;
			}
		}

			/*Finding out if a block does not already exist in the chain that has the same hash*/
		public static void @VAFImpl(BitcoinProof proof,
			Dafny.Sequence<Block<Dafny.Sequence<byte>,BitcoinTransaction,BitcoinProof>> blockChain,
			Dafny.Sequence<BitcoinTransaction> txPool,
			out bool vb)
		{
			Logger.Info("VAFImpl;start;"+blockChain.Length+";"+txPool.Length);

			if (blockChain.Length == 0) // given that the chain is empty or that there is only the genesis block with no transactions
		    {
		    	vb = true;
		    	Logger.Info("VAFImpl;end;"+blockChain.Length+";"+txPool.Length+";zerolength");
		    	return;
		    }

			Block<Dafny.Sequence<byte>,BitcoinTransaction,BitcoinProof> finalBlockInChain =
			blockChain.Select(blockChain.Length - 1);

			Dafny.Sequence<byte> prevBlockHash;
			@BitcoinImplUtil.@Util.@HashBImpl(finalBlockInChain, out prevBlockHash);

			Block_Block<Dafny.Sequence<byte>,BitcoinTransaction,BitcoinProof> blockBlock =
			new Block_Block<Dafny.Sequence<byte>,BitcoinTransaction,BitcoinProof>(prevBlockHash, txPool, proof);
			Block<Dafny.Sequence<byte>,BitcoinTransaction,BitcoinProof> block = 
			new Block<Dafny.Sequence<byte>,BitcoinTransaction,BitcoinProof>(blockBlock);

			Dafny.Sequence<byte> blockHash;
			@BitcoinImplUtil.@Util.@HashBImpl(block, out blockHash);

			foreach (Block<Dafny.Sequence<byte>,BitcoinTransaction,BitcoinProof> b in blockChain.Elements)
			{	
				Dafny.Sequence<byte> currentBlockHash;
				@BitcoinImplUtil.@Util.@HashBImpl(b, out currentBlockHash);

				bool condition;
				compareHashes(currentBlockHash, blockHash, out condition);
				if (condition) { // if a cycle is found.
					Logger.Info("VAFImpl;end;"+blockChain.Length+";"+txPool.Length+";cycle");
					vb = false;
					return;
				}

			}
			Logger.Info("VAFImpl;end;"+blockChain.Length+";"+txPool.Length+";good");
			vb = true;
		}


		public static void @GenProofImpl(int address,
			Dafny.Sequence<Block<Dafny.Sequence<byte>,BitcoinTransaction,BitcoinProof>> blockChain,
			Dafny.Sequence<BitcoinTransaction> txPool,
			Dafny.Sequence<byte> timestamp,
			out Option<@_System.@__tuple_h2<Dafny.Sequence<@Bitcoin.@BitcoinTransaction>,@Bitcoin.@BitcoinProof>> o)
		{

			Logger.Info("GenProofImpl;start;"+blockChain.Length+";"+txPool.Length);

			if (txPool.Elements.Length == 0)
			{
				Console.WriteLine("0 transactions sent to GenProofImpl");
				Logger.Info("GenProofImpl;end;"+blockChain.Length+";"+txPool.Length);
				o = new Option<@_System.@__tuple_h2<Dafny.Sequence<@Bitcoin.@BitcoinTransaction>,@Bitcoin.@BitcoinProof>>(new Option_None<@_System.@__tuple_h2<Dafny.Sequence<@Bitcoin.@BitcoinTransaction>,@Bitcoin.@BitcoinProof>>());
				return;
			}

			uint targetBits = 0; 

			BigInteger largeValue = BigInteger.Pow(2, (256 - (int)targetBits));

			Dafny.Sequence<byte> version;
			convertUInttoSeq(1, out version);

			Dafny.Sequence<byte> targetToSeq;
			convertUInttoSeq(targetBits, out targetToSeq);

			Dafny.Sequence<byte> prevBlockHash;
			@BitcoinImplUtil.@Util.@HashBImpl(blockChain.Select(blockChain.Length - 1), out prevBlockHash);

			uint nonce = 0;
			Dafny.Sequence<byte> n;
		    convertUInttoSeq(nonce, out n); // for initialization

		    BitcoinProof p;
		    BitcoinProof_BitcoinProof proof;

		    Dafny.Sequence<byte> blockHash;

		    while (nonce < Int32.MaxValue) 
		    {
		    	proof = new BitcoinProof_BitcoinProof(version, timestamp, targetToSeq, n);
		    	p = new BitcoinProof(proof);

		    	Block_Block<Dafny.Sequence<byte>, BitcoinTransaction, BitcoinProof> block = 
		    	new  Block_Block<Dafny.Sequence<byte>, BitcoinTransaction, BitcoinProof>(prevBlockHash, txPool, p);

		    	Block<Dafny.Sequence<byte>, BitcoinTransaction, BitcoinProof> b = 
		    	new  Block<Dafny.Sequence<byte>, BitcoinTransaction, BitcoinProof>(block);

		    	@BitcoinImplUtil.@Util.@HashBImpl(b, out blockHash);

		    	BigInteger hashVal;
		    	convertSeqToBigInt(blockHash, out hashVal);


		    	if (BigInteger.Compare(hashVal, largeValue) == -1)
		    	{
		    		break;	
		    	}
		    	else
		    	{
		    		nonce ++; 
		    		convertBigInttoSeq(nonce, out n);
		    	}
		    }

		    BitcoinTransaction[] txs = new BitcoinTransaction[1 + txPool.Elements.Length];
		    BitcoinTransaction tx;
		    generateCoinbaseTransaction(timestamp, out tx);
		    txs[0] = tx;

		    for (int i = 0; i < txPool.Elements.Length; i++)
		    {
		    	txs[i+1] = txPool.Select(i);
		    	Logger.Info("GenProofImpl;tx;"+blockChain.Length+";"+txPool.Length+";"+txs[i+1]);
		    }

		    Dafny.Sequence<BitcoinTransaction> result = Dafny.Sequence<BitcoinTransaction>.FromElements(txs);
		    proof = new BitcoinProof_BitcoinProof(version, timestamp, targetToSeq, n);
		    p = new BitcoinProof(proof);

		    @_System.@__tuple_h2<Dafny.Sequence<@Bitcoin.@BitcoinTransaction>, @Bitcoin.@BitcoinProof> test;
		    test = new @_System.@__tuple_h2<Dafny.Sequence<@Bitcoin.@BitcoinTransaction>, @Bitcoin.@BitcoinProof>(new @_System.__tuple_h2____hMake2<Dafny.Sequence<@Bitcoin.@BitcoinTransaction>, @Bitcoin.@BitcoinProof>(result, p));
		    o = new Option<@_System.@__tuple_h2<Dafny.Sequence<@Bitcoin.@BitcoinTransaction>,@Bitcoin.@BitcoinProof>>(new Option_Some<@_System.@__tuple_h2<Dafny.Sequence<@Bitcoin.@BitcoinTransaction>,@Bitcoin.@BitcoinProof>>(test));
		    Logger.Info("GenProofImpl;end;"+blockChain.Length+";"+txPool.Length);
		    return;
		}

		public static void @generateCoinbaseTransaction(Dafny.Sequence<byte> timestamp, out BitcoinTransaction tx) {
			var emptySeq = new Dafny.Sequence<byte>(new byte[0]);
			BitcoinTxIn txIn = new BitcoinTxIn(new BitcoinTxIn_BitcoinTxIn(emptySeq, emptySeq, emptySeq, emptySeq));
			BitcoinTxIn [] txInArr = new BitcoinTxIn[1];
			txInArr[0] = txIn;
			var txInSeq = Dafny.Sequence<BitcoinTxIn>.FromElements(txInArr);

			Dafny.Sequence<byte> valueSeq;
			ConvertULongToByteSeq((ulong)50, out valueSeq);

			BitcoinTxOut txOut = new BitcoinTxOut(new BitcoinTxOut_BitcoinTxOut(valueSeq, emptySeq));
			BitcoinTxOut [] txOutArr = new BitcoinTxOut[1];
			txOutArr[0] = txOut;
			var txOutSeq = Dafny.Sequence<BitcoinTxOut>.FromElements(txOutArr);

			Dafny.Sequence<byte> versionSeq;
			uint versionNum = 2;
			convertUInttoSeq(versionNum, out versionSeq);

			var txtx = new BitcoinTransaction_BitcoinTransaction(versionSeq, txInSeq, txOutSeq, timestamp);
			tx = new BitcoinTransaction(txtx);
		}

		public static void IsCoinBaseTransaction(BitcoinTransaction transaction, out bool b) 
		{
			var ins = ((Bitcoin.@BitcoinTransaction_BitcoinTransaction)transaction._D).@ins;
			if (ins.Length != 1) {
				b = false;
				return;
			}

			Dafny.Sequence<byte> hash = ((Bitcoin.BitcoinTxIn_BitcoinTxIn) ins.Select(0)._D).prevout__hash;
			if (hash.Length == 0) {
				b = true;
				return;
			}
			b = false;
		}



		public static void @TxValidImpl(BitcoinTransaction transaction,
			Dafny.Sequence<Block<Dafny.Sequence<byte>,BitcoinTransaction,BitcoinProof>> blockChain,
			out bool b)
		{
			Logger.Info("TxValidImpl;start;"+transaction+";"+blockChain.Length);
		    if (blockChain.Length == 0) // given that the chain is empty or that there is only the genesis block with no transactions
		    {
		    	b = true;
		    	Logger.Info("TxValidImpl;end;"+transaction+";"+blockChain.Length+";false");
		    	//Console.WriteLine("Block chain length is 0.");
		    	return;
		    }
		    

		    bool isCoinBaseTransaction;
		    IsCoinBaseTransaction(transaction, out isCoinBaseTransaction);


		    if (isCoinBaseTransaction) {
		    	b = true;
		    	Logger.Info("TxValidImpl;end;"+transaction+";"+blockChain.Length+";coinbase");
		    	return;
		    }

		    Dafny.Sequence<byte> transactionHash;
		    @BitcoinImplUtil.@Util.@HashTImpl(transaction, out transactionHash);

		    int length = ((Bitcoin.@BitcoinTransaction_BitcoinTransaction)transaction._D).@ins.Length;
		    bool [] array = new bool[length];	
		    for (int i = 0; i < length; i++)
		    array[i] = false;

		    BigInteger prevTransactionAmount = 0;
		    BigInteger transactionAmount = 0;

		    foreach (Block<Dafny.Sequence<byte>,BitcoinTransaction,BitcoinProof> block in blockChain.Elements)
		    {				
		    	Dafny.Sequence<BitcoinTransaction> currTxs = ((Block_Block<Dafny.Sequence<byte>,BitcoinTransaction,BitcoinProof>) block._D).txs;

		    	for (int i = 0; i < length; i++) { 

		    		BitcoinTxIn in_ = ((Bitcoin.@BitcoinTransaction_BitcoinTransaction)transaction._D).@ins.Select(i);
		    		BigInteger index;
		    		convertSeqToBigInt(in_.dtor_prevout__n, out index);

		    		Dafny.Sequence<byte> prevOutHash = ((Bitcoin.BitcoinTxIn_BitcoinTxIn) in_._D).prevout__hash;

			        //checking if the transaction exists already
		    		foreach (BitcoinTransaction t in currTxs.Elements) {
		    			bool condition;
		    			Dafny.Sequence<byte> t_hash;
		    			@BitcoinImplUtil.@Util.@HashTImpl(t, out t_hash);					
		    			compareHashes(transactionHash, t_hash, out condition);
		    			if (condition) { 
		    				b = false;
		    				Logger.Info("TxValidImpl;end;"+transaction+";"+blockChain.Length+";false;alreadythere");
		    				Console.WriteLine("Transaction already exists in the chain.");
		    				return;
		    			} 

						//checking if another transaction exists with one of the same prev hash	
		    			condition = false;	
		    			int inputsLength = t.dtor_ins.Elements.Length;

		    			for (int j = 0; j < inputsLength; j++) {
		    				BitcoinTxIn _in = t.dtor_ins.Elements[j];
		    				Dafny.Sequence<byte> txPrevIn = _in.dtor_prevout__hash;
		    				compareHashes(txPrevIn, prevOutHash, out condition);
		    				if (condition) {
		    					Logger.Info("TxValidImpl;end;"+transaction+";"+blockChain.Length+";false;doublespend");
		    					b = false;
		    					return;
		    				}
		    			}


						// checking if the previous transaction exists
		    			condition = false;
		    			compareHashes(t_hash, prevOutHash, out condition);
		    			if (condition) {  
		    				BigInteger pTA;
		    				convertSeqToBigInt(t.dtor_outs.Select((int)index).dtor_value, out pTA);
		    				prevTransactionAmount += pTA;
		    				array[i] = true;
		    			}
		    		}
		    	}
		    }

		    foreach (BitcoinTxOut _out in transaction.dtor_outs.Elements)
		    {
		    	BigInteger amount;
		    	convertSeqToBigInt(_out.dtor_value, out amount);
		    	transactionAmount += amount;
		    }

		    for (int i = 0; i < length; i++) {
		    	if (!array[i]) {
		    		Console.WriteLine("The prev transaction does not exist.");
		    		Logger.Info("TxValidImpl;end;"+transaction+";"+blockChain.Length+";false");
		    		b = false;
		    		return;
		    	}
		    }

		    if (prevTransactionAmount < transactionAmount)
		    {
		    	b = false;
		    	Logger.Info("TxValidImpl;end;"+transaction+";"+blockChain.Length+";false;amounts");
		    	Console.WriteLine("The amounts don't match: " + prevTransactionAmount + " " + transactionAmount);
		    	return;
		    }

		    Logger.Info("TxValidImpl;end;"+transaction+";"+blockChain.Length+";true");
		    b = true;
		    return;
		}

	}


	/*
	* A tiny logger class. 
	* Used only for the purpose of metrics. 
	*
	*/
	public class Logger
	{
		static string FILE_NAME = "BlockchainLog-";
		static string BUFFER = "";
		static int BUFFER_SIZE = 20;
		static int currentBufferSize = 0; 

		// So that nodes can append an ID differentiate log files
		public static void SetFileName(string fileName)
		{
			FILE_NAME += fileName + ".log";
		}

		public static void Info(String line)
		{
			long milliseconds = DateTime.Now.Ticks / TimeSpan.TicksPerMillisecond;
			line = milliseconds + ";[INFO];" + line + "\n";
			BUFFER += line;
			FlushToFile();
		}

		public static void Warn(String line)
		{
			long milliseconds = DateTime.Now.Ticks / TimeSpan.TicksPerMillisecond;
			line = milliseconds + ";[WARN];" + line + "\n";
			BUFFER += line;
			FlushToFile();
		}

		public static void Error(String line)
		{
			long milliseconds = DateTime.Now.Ticks / TimeSpan.TicksPerMillisecond;
			line = milliseconds + ";[ERROR];" + line + "\n";
			BUFFER += line;
			FlushToFile();
		}

		public static void ForceFlush()
		{
			currentBufferSize = BUFFER_SIZE;
			FlushToFile();
		}

		private static void FlushToFile()
		{
			currentBufferSize += 1;
			if (currentBufferSize < BUFFER_SIZE)
			{
				return;
			}

			string path = FILE_NAME;
            // This text is added only once to the file.
            if (!File.Exists(path))
            {
                Console.WriteLine("Creating the file.");
                // Create a file to write to.
                using (StreamWriter sw = File.CreateText(path))
                {
                    sw.WriteLine("");
                }
            }

            using (StreamWriter sw = File.AppendText(path))
            {
                sw.WriteLine(BUFFER);
            }
            BUFFER = "";
            currentBufferSize = 0;
		}
	}

}

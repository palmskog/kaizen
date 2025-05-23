default: UseBitcoinImpl.exe

BitcoinImpl.cs: LinkedList.dfy SeqUtil.dfy NativeTypes.dfy NativeTypesUtil.dfy TotalOrder.dfy OrderedSeqUtil.dfy MathUtil.dfy MathUtilImpl.dfy Blockchain.dfy BlockchainImplUtil.dfy Bitcoin.dfy BitcoinImplUtil.dfy BitcoinConstants.dfy BitcoinImpl.dfy
	-Dafny.exe /compile\:1 /spillTargetCode\:1 /nologo /out\:BitcoinImpl.cs BitcoinImpl.dfy

BitcoinImpl.dll: BitcoinImpl.cs BitcoinUtilExt.cs BitcoinImplUtilExt.cs
	mcs /t\:library /r\:System.Numerics.dll BitcoinImpl.cs BitcoinUtilExt.cs BitcoinImplUtilExt.cs

LinkedListMain.exe LinkedListMain.exe.mdb: LinkedListMain.dfy LinkedList.dfy
	Dafny.exe /compile\:1 /nologo LinkedListMain.dfy

LinkedList.dll LinkedList.cs LinkedList.dll.mdb: LinkedList.dfy
	-Dafny.exe /compile\:2 /spillTargetCode\:1 /nologo LinkedList.dfy

LinkedListLib.dll: LinkedList.cs
	mcs /target:library /r\:System.Numerics.dll /out\:LinkedListLib.dll LinkedList.cs

UseLinkedList.exe: UseLinkedList.cs LinkedList.dll
	mcs UseLinkedList.cs /r\:LinkedList.dll

UseBitcoinImpl.exe: UseBitcoinImpl.cs BitcoinImpl.dll
	mcs UseBitcoinImpl.cs /r\:System.Numerics.dll /r\:BitcoinImpl.dll

clean:
	rm -f *.dll *.exe *.mdb LinkedList.cs BitcoinImpl.cs

.PHONY: default clean

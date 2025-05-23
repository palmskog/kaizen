This is a dotnet project that runs the shim layer with the Dafny implementation of Bitcoin.
This also contains a workload generator that can be used for both our reference 
implementation and the actual implementation. It also contains a layer that interacts with the 
actual Bitcoin implementation and can create raw transactions.


This is a console application, and can be run by:
`dotnet run <type> <port> <id>`

<type> takes either 1 or 2 or 3. 1 starts the progam as a node (interacting with Dafny) on the system and 3 starts 
the program as the WorkloadGenerator. 2 starts the bitcoin-node, which calls the 
create-transaction functions for the actual bitcoin implementation.

To build and run a demo of running the layer with Dafny: 

1. Install dotnet 
2. Make sure the first line of HelperFunctions.c says `#define LOCAL`
3. If changes are made in the Dafny folder, please recompile BitcoinImpl.dll and copy it into networkLayer/DLL/ 
3. Open three terminal windows in the folder networkLayer/DLL
    - On first one, `dotnet run 1 9050 1`
    - On second one, `dotnet run 1 9051 2`
    - On third one, after validation of initial state is succeeded in both the above, `dotnet run 3`


The WorkloadGenerator parses the transaction data from files and sends it to all the nodes in the network. 
You can see the files where we read from in cluster.json unspent transactions of each node.

Transactions will be broadcasted, and block minting happens after every 2 transactions are received. 

todo: write a script to automate demo. 

The same workload generator is used for the actual Bitcoin implementation. If you have the regtest set up, 
you can modify cluster.json accordingly, and start the workload for the real implementation by:
`dotnet run 2`

IMPORTANT: The nodes are configured in cluster.json, so make sure you start your 
nodes following that same config. 

todo: add a startup script that sshes into all the nodes and starts them from cluster.json 

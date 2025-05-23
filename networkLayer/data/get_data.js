const WebSocket = require('ws');
const fs = require('fs');
var trans = {
    count: 0,
    transactions: []
};


// connect to blockchain api
const ws = new WebSocket('wss://ws.blockchain.info/inv', {
  perMessageDeflate: false
});
// subscribe to transactions
ws.on('open', () => {
    ws.send("{\"op\":\"unconfirmed_sub\"}");
    // end program after some time
    setTimeout(() =>{
        ws.close();
    },  30 * 60000); // get transactions for 30 minutes
});
//
ws.on('message', (data) => {
    trans.transactions.push(JSON.parse(data));
    trans.count += 1;
});
// file dump
ws.on('close', function (){
    fs.writeFileSync('./transactions.json', JSON.stringify(trans, null, 2), 'utf-8')
})

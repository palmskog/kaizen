include "BlockchainImpl.dfy"
include "BitcoinImplUtil.dfy"

module {:extern "BitcoinImpl"} BitcoinImpl refines BlockchainImpl {
  import opened BIU = BitcoinImplUtil

  class StateImpl {

    method ProcMsgImpl...
    {
      assert ...;
      assert ...;
      ...;
    }

    method ProcIntImpl...
    {
      assert ...;
      ...;
    }

	}

  method TestProcMsg(s: StateImpl)
    modifies s.Repr;
    requires s.Valid();
  {
    var msg := B.ConnectMsg();
    var pt := s.ProcMsgImpl(1, msg, []);
    ghost var st := s.st;
    assert pt == B.procMsg(st, 1, msg, []).1;
  }

}

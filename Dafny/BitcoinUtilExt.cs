using System.Numerics;
using System.Security.Cryptography;

namespace @BitcoinUtilExt
{

  public partial class @Util
  {

      public static Dafny.Sequence<byte> @SHA256(Dafny.Sequence<byte> messageBytes)
      {
	  SHA256 sha256 = SHA256Managed.Create();
	  byte[] data = messageBytes.Elements;
          byte[] hash = sha256.ComputeHash(data);
	  return new Dafny.Sequence<byte>(hash);
      }
  }

}

using System.Collections.Generic;

namespace Microsoft.Dafny
{
  public class MessageInvariantsFile {

    // List of invariants
    private List<SendInvariant> sendInvariants;
    private List<ReceiveInvariant> receiveInvariants;
    private List<ReceiveSkolemization> receiveSkolemizations;

    public bool IncludeCustomInvariants { get; set; } = false;

    // Constructor
    public MessageInvariantsFile()
    {
      sendInvariants = new List<SendInvariant>{};
      receiveInvariants = new List<ReceiveInvariant>{};
      receiveSkolemizations = new List<ReceiveSkolemization>{};
    }

    public List<SendInvariant> SendInvariants {
      get { return sendInvariants; }
    }

    public List<ReceiveInvariant> ReceiveInvariants {
      get { return receiveInvariants; }
    }

    public List<ReceiveSkolemization> ReceiveSkolemizations {
      get { return receiveSkolemizations; }
    }

    public void AddSendInvariant(SendInvariant si) {
      sendInvariants.Add(si);
    }

    public void AddReceiveInvariant(ReceiveInvariant ri) {
      receiveInvariants.Add(ri);
    }

    public void AddReceiveSkolemization(ReceiveSkolemization rs) {
      receiveSkolemizations.Add(rs);
    }

  } // end class MessageInvariantsFile
}
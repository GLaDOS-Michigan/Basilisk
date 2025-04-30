using System.Collections.Generic;

namespace Microsoft.Dafny {

public class BasiliskField {
  public string Name { get; set;}
  public string Type { get; set;}

  public BasiliskField(string name, string type) {
    Name = name;
    Type = type;
  }
}

public class StepFootprint {
  public string Step { get; set;}
  public List<BasiliskField> Fields { get; set;}

  public StepFootprint(string step) {
    Step = step;
    Fields = new List<BasiliskField>();
  }
}

public class HostFootprint {
  // Map from message type to list of step footprints
  public Dictionary<string, List<StepFootprint>> MsgFootprints { get; set;}

  public HostFootprint() {
    MsgFootprints = new Dictionary<string, List<StepFootprint>>();
  }
}


public class HostHint {
  // Map from Message type to list of list of fields
  public Dictionary<string, List<List<BasiliskField>>> HostHints { get; set;}

  public HostHint() {
    HostHints = new Dictionary<string, List<List<BasiliskField>>>();
  }
}
}
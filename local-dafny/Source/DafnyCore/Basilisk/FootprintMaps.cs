using System;
using System.Collections.Generic;
using JetBrains.Annotations;

namespace Microsoft.Dafny{
    public class UpdatedFunctions {
        public Dictionary<String, List<String>> updatedParameters = new Dictionary<String, List<String>>(); 
    }

    public class MessageUpdates {
        public Dictionary<String, UpdatedFunctions> updatedFunctions = new Dictionary<String, UpdatedFunctions>();

        public Dictionary<String, Dictionary<String, List<String>>> unflattenDict(){
            Dictionary<String, Dictionary<String, List<String>>> functionDictUnflattened = new Dictionary<String, Dictionary<String, List<String>>>();
            foreach (KeyValuePair<String, UpdatedFunctions> messageKvp in updatedFunctions){
                functionDictUnflattened.Add(messageKvp.Key, messageKvp.Value.updatedParameters);
            }
            return functionDictUnflattened;


        }
    }
}  
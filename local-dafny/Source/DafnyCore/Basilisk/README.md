# Basilisk source files

* DistributedSystemDriver.cs -- Driver for lifting a synchronous protocol description into an asynchronous one
* DistributedSystemFile.cs -- Data structure used by DistributedSystemDriver
* DistributedSystemPrinter.cs -- Data structure for formatting the asynchronous protocol description into a Dafny program
* MessageInvariantsFile.cs -- Data structure used by RegularInvariantsDriver
* MonotonicityInvariant.cs -- Data structure to encode a Monotonicity Invariant
* MonotonicityInvariantsFile.cs -- Data structure used by RegularInvariantsDriver
* OwnershipInvariantsFile.cs -- Data structure used by RegularInvariantsDriver
* ReceiveInvariant.cs -- Data structure to encode a Receive Invariant
* RegularInvariantsDriver.cs -- Driver for generating Regular Invariants
* RegularInvariantsPrinter.cs -- Data structure for formatting Regular Invariants into a Dafny program
* SendInvariant.cs -- Data structure to encode a Send Invariant
* templates.json -- A database of strings used by the various printer programs

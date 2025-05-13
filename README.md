# Basilisk

This is the code base for the Basilisk prototype, as described in the OSDI'25 paper
"Basilisk: Using Provenance Invariants to Automate Proofs of Undecidable Protocols".

The paper builds on the concept of an Invariant Taxonomy introduced in [Kondo](https://www.usenix.org/conference/osdi24/presentation/zhang-nuda), and factors the invariants of a distributed protocol into various sub-classes of Regular Invariants. Given a distributed protocol, Basilisk automatically generates a set of Regular invariants that is strong enough to form the *inductive invariant* of the protocol.

## Project Layout

This artifact has two main directories.

### local-dafny/

The directory local-dafny/ contains the source code and executable for the Basilisk tool. It is built on top of the [Kondo artifact](https://github.com/GLaDOS-Michigan/Kondo), which itself is a fork of
[Dafny 4.2.0](https://github.com/dafny-lang/dafny/releases/tag/v4.2.0).

The core Basilisk functionality is implemented in the local-dafny/Source/DafnyCore/Basilisk/ sub-directory.

### basilisk/

The directory basilisk/ contains the protocols on which Basilisk is evaluated, together with the scripts for performing the evaluation.

### kondo/

The directory kondo/ contains the protocols on which Kondo is evaluated, as a reference.

## Installation

The following instructions have been tested on an M3 MacBook Pro running MacOS Sequoia. Libraries and commands for other OS may differ.

### Build And Test Local Dafny

We begin with building our local version of Dafny that contains Basilisk extensions. 

1. Dependencies:
	* Install .NET SDK (version 6.0)
		* This can be done using brew: `brew install dotnet-sdk`,
		* Or through a manual install [https://dotnet.microsoft.com/en-us/download/dotnet/6.0](https://dotnet.microsoft.com/en-us/download/dotnet/6.0)
	* [python3 and pip3 are needed but they are likely already part of the Mac installation]
2. Build Dafny. From the project root, run:

	```bash
	cd local-dafny
	make
	```
	This should take less than 20 seconds.
	Note that you may also be required to install [Java 17](https://www.oracle.com/java/technologies/javase/jdk17-archive-downloads.html) as a dependency for gradle.
3. To check that Dafny runs as expected, run from the local-dafny directory:

	```bash
	 ./Scripts/dafny /compile:0 test.dfy
	```
	The expected output is
	> `Dafny program verifier finished with 1 verified, 0 errors`
	
### Verifying Protocols

Now that Dafny is set up, we check that all 16 protocols in our evaluation passes the Dafny verifier. From the repository root, run:

```bash
cd basilisk/
./verify-all 
```

Note that warnings of the form `Warning: /!\ No terms found to trigger on.` can be safely ignored.

This script runs the Dafny verifier on each of the protocol, and takes about 5min on an M3 MacBook Pro.

> [!IMPORTANT]  
> This step must be completed before moving on to the [Paper Evaluation](#paper-evaluation) section, as it produces auto-generated files required to complete the evaluation.

One may also verify each version of each protocol individually, by running the `verify` script in the respective sub-directory for the protocol version. For instance:

```bash
./basilisk/clientServer/automate_gen2/verify
```

## Paper Evaluation

This section involves reproducing the results published in the paper.

Basilisk's goal is to relieve developer effort in verifying distributed systems. It accomplishes this on two fronts:

1. The user only needs to provide a few simple hints for Basilisk to automatically generate an inductive invariant for each protocol.
2. The user should be responsible for writing fewer lines of proof code, compared to its predecessor Kondo.

The next two section detail how we obtain these numbers.

### Verifying Claim 1

**Claim:** *User only needs to provide a few simple hints for Basilisk to automatically generate an inductive invariant for each protocol.*

There are two types of hints, namely monotonic type annotations, and Provenance hints, both listed in Table 1 of the paper. These numbers are obtained through manual inspection.
Using only these hints, basilisk generates invariants sufficient to form the inductive invariants of the evaluated protocols.

For **monotonic type annotations**, we count the number of monotonic variables in the host state of each protocol, i.e., types that begin with the `Monotonic` prefix.
These are located within the `Variables` datatype definition within each host.dfy file.
For example, we can look at the `Variables` definition in basilisk/paxos/automate_gen2/hosts.dfy, to see that 5 monotonic variables are used.
Note that Basilisk's use of monotonic variables is identical to Kondo, and hence Basilisk shares the same numbers as Kondo.

For **provenance hints**, we count the number of predicates defined in the customMessageInvariants.dfy file for protocol (e.g., basilisk/multiPaxos/automate_gen2/customMessageInvariants.dfy).
Note that only protocols that actually require such hints have such a file in their directory.

In contrast, Kondo's use of "Recv hints" is derived from inspecting Kondo's codebase.
In Kondo, these are predicates in the hosts.dfy file that end with the suffix "trigger" (e.g., `predicate ReceivePromiseTrigger` in [this file](https://github.com/GLaDOS-Michigan/Kondo/blob/main/kondoPrototypes/paxos/hosts.dfy)).

To demonstrate that we **prove protocols using only Basilisk's generated invariants** as the inductive invariant, we can study the "verify" script located in each protocol's directory (e.g., basilisk/multiPaxos/automate_gen2/verify). In the script:

1. Command Basilisk to generate a set of footprints using the Atomic Sharding Algorithm described in section 4 of the paper. This generates the file footprintsAutogen.json in the same directory as the verify script.
2. Command Basilisk to use the generated json file, together with the protocol definition, to generate a set of Regular Invariants, in the files messageInvariantsAutogen.dfy, monotonicityInvariantsAutogen.dfy, and ownershipInvariantsAutogen.dfy (when ownership invariants are applicable).
3. Verify the applicationProofDemo.dfy file. This file is what users of Basilisk writes. It defines the inductive invariant as the conjunct of all generated Regular Invariants, and uses it to prove the protocol, without defining any additional invariants.

### Verifying Claim 2

**Claim:** *Users write fewer lines of proof code using Basilisk, compared to Kondo.*

This claim is evaluated by the "Lines of proof" columns in Table 1 of the paper.
The lines of proof code a user writes when using Basilisk is contained in the respective `basilisk/<protocol>/automate_gen2/applicationProofDemo.dfy` files.

To compare with Kondo, we include the Kondo protocols under the /kondo directory. For Kondo, the number of lines of "Safety proof" is the lines of code in `kondo/<protocol>/sync/applicationProof.dfy`, minus the lines for invariant definitions. Meanwhile, the "Total" proof is the sum of the "Safety" column and "Mods" column in [Table 1 of the Kondo paper](https://www.usenix.org/system/files/osdi24-zhang-nuda.pdf).

To generate these numbers, simply run

```bash
cd basilisk/evaluation
python3 eval.py
```

The results are written to the sloc.csv file.

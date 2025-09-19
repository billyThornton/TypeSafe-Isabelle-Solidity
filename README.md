# A Formal Semantics of Solidity in Isabelle/HOL

This directory contains a formal semantics of Solidity in Isabelle/HOL and a series of theories to verify the type safety of this semantics. 
Initially, this semantics has been developed in Haskell and translated
in an "ad-hoc" way using an "in-house" version of Haskabelle for 
Isabelle 2017 and, thereafter, the generated theories were then ported
to Isabelle 2021-1.

Since then the theories have been updated to Isabele 2025-1 and a series of theory files have been added to verify the type safety of the formalisation.

## Prerequisites

* The formalization requires [Isabelle 2025-1](https://isabelle.in.tum.de/). 
  Please follow the instructions on the Isabelle home page for your operating 
  system. In the following, we assume that the ``isabelle`` tool is available
  on the command line. This might require to add the Isabelle binary directory
  to the ``PATH`` environment variable of your system. 

## Using the Formalization

The formalization can be loaded into Isabelle/jEdit by executing 

```sh
isabelle jedit TypeSafe.thy
```

on the command line. Alternatively, you can start Isabelle/jEdit by 
clicking on the Isabelle icon and loading the theory 
[Solidity_Main.thy](./TypeSafe.thy) manually. 

To use a command line build that also generates a PDF document,
first add ``path/to/solidity`` to your Isabelle roots file which is
a file called ``ROOTS`` in your Isabelle home directory.
Then, the build can be started by executing:

```sh
isabelle build -D .
```

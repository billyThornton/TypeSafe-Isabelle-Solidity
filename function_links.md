# Solidity Isabelle/HOL Function and Definition Links

This document provides links to key function and definition locations in the Solidity Isabelle/HOL formalization codebase.

## Table of Contents

<!-- State Monad Functions -->
## State Monad Functions

<a name="resultM"></a>

### result - State Monad result type
[`datatype result`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/StateMonad.thy#L7)

<a name="stateMonad"></a>

### state_monad - State Monad Definition
[`type_synonym state_monad`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/StateMonad.thy#L9)

<a name="bindM"></a>

### bind - Bind operator in a State Monad
[`fun bind`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/StateMonad.thy#L32-L35)

<a name="returnM"></a>

### return - Return operation for a Monad
[`fun return`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/StateMonad.thy#L26-L27)

<a name="throwM"></a>

### throw - Throw operation for a Monad
[`fun throw`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/StateMonad.thy#L29-L30)

<a name="applyfM"></a>

### applyfM - Apply Function for a Monad
[`definition applyf`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/StateMonad.thy#L147-149)

<!-- Storage and Memory Types -->
## Storage and Memory Types

<a name="typesD"></a>

### Types - Definition of Types
[`datatype Types`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Valuetypes.thy#L118-L121)

<a name="storeD"></a>

### Store - Definition of a Store
[`record Store`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Storage.thy#L73-L75)

<a name="accSto"></a>

### accessStore - Access Store Definition
[`definition accessStore`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Storage.thy#L77-L78)

<a name="updSto"></a>

### updateStore - Update Store Definition
[`definition updateStore`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Storage.thy#L105-L106)

<a name="hashD"></a>

### hash - Definition of Hash
[`definition hash`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Storage.thy#L10-L11)

<a name="stackvalD"></a>

### StackValue - Definition of Stack Value
[`datatype Stackvalue`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Storage.thy#L126-L129)

<a name="stackD"></a>

### Stack - Definition of Stack
[`type_synonym Stack`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Storage.thy#L131)

<a name="mtypesD"></a>

### MTypes - Definition of Memory Types
[`datatype MTypes`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Storage.thy#L203-L205)

<a name="stypesD"></a>

### STypes - Definition of Storage Types
[`datatype STypes`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Storage.thy#L141-L143)

<a name="memValD"></a>

### MemoryValue - Definition of Memory Values
[`datatype Memoryvalue`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Storage.thy#L195-L197)

<a name="memoryD"></a>

### MemoryT - Definition of Memory Store
[`type_synonym MemoryT`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Storage.thy#L199)

<a name="calldataD"></a>

### CalldataT - Definition of Calldata Store
[`type_synonym CalldataT`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Storage.thy#L201)

<a name="storageD"></a>

### StorageT - Definition of Storage
[`type_synonym StorageT`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Storage.thy#L139)

## Additional Storage Functions

<a name="ivalD"></a>

### ival - Ival Definition
[`fun ival`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Valuetypes.thy#L465-L470)

<a name="accStorD"></a>

### accessStorage - Access Storage Definition
[`fun accessStorage`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Storage.thy#L154-L159)

<a name="cpm2mD"></a>

### cpm2m - Copy Memory to Memory Definition
[`fun cpm2m`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Storage.thy#L272-L274)

<a name="iterpD"></a>

### iter' - Definition of iter'
[`fun iter'`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Valuetypes.thy#L12-L17)

<a name="cpm2mRecD"></a>

### cpm2mRec - Copy Memory to Memory Recursive Definition
[`fun cpm2mrec`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Storage.thy#L259-L270)

## Environment and State

<a name="stateD"></a>

### State - Definition of State
[`type_synonym State`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Contracts.thy#L50-L55)

<a name="typeD"></a>

### type - Definition of  Type
[`datatype Type`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Environment.thy#L12-L15)

<a name="DenvalueD"></a>

### Denvalue - Definition of Denvalue Type
[`datatype Denvalue`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Environment.thy#L17-L18)

<a name="environmentD"></a>

### Environment - Definition of Environment
[`type_synonym Environment`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Environment.thy#L20-L25)

<a name="emptyEnvD"></a>

### emptyEnv - Empty Environment Definition
[`definition emptyEnv`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Environment.thy#L30-L31)

<a name="declD"></a>

### decl - Declaration Definition
[`fun decl`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Environment.thy#L180-L239)

<a name="memberD"></a>

### Member - Member Definition
[`datatype Member`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Contracts.thy#L133-L135)

<a name="contractD"></a>

### Contract - Contract Definition
[`type_synonym Contract`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Contracts.thy#L147)

<a name="envPD"></a>

### envP - Procedural Environment Definition
[`type_synonym Environment\<^sub>P`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Contracts.thy#L149)

<a name="initD"></a>

### init - Contract Procedural Environment Init Definition
[`definition init`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Contracts.thy#L151-L154)

## Expression Components

<a name="bitsD"></a>

### bits - Definition of Bits
[`type_synonym bits`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Valuetypes.thy#L26-L28)

<a name="lD"></a>

### L - Definition of L (used in lexp)
[`datatype L`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Contracts.thy#L8-L9)

<a name="eD"></a>

### E - Definition of E (used in expressions)
[`datatype E`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Contracts.thy#L10-L29)
[`Statement Defintions`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Expressions.thy#L86-L246)

<a name="msel"></a>

### msel - Memory Select Definition
[`function msel`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Expressions.thy#L49-L69)

<a name="ssel"></a>

### sselD - Storage Select Definition
[`function ssel`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Expressions.thy#L70-L85)

<a name="lTypeD"></a>

### lType - LType Definition
[`datatype LType`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Expressions.thy#L32-L34)

<a name="lexpD"></a>

### lexp - Left Expression Definition
[`function lexp`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Statements.thy#L19-L50)

<a name="rexpD"></a>

### rexp - Right Expression Definition
[`function rexp`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Expressions.thy#L270-L339)

<a name="statementsD"></a>

### S - Statements Definition
[`datatype S`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Contracts.thy#L31-L40)
[`Statement Defintions`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Statements.thy#L185-L468)

## Type Safety Components

<a name="sublocD"></a>

### sublocD - LSubPrefL2
*Note: Referenced throughout TypeSafe files but not found as standalone definition*

<a name="typMemSubD"></a>

### typMemSubD - TypedMemSubPrefPtrs Definition
[`definition TypedMemSubPrefPtrs`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/TypeSafe_Memory.thy#L155)

<a name="compMemSubD"></a>

### compMemSubD - CompMemType Definition
[`definition CompMemType`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/TypeSafe_Memory.thy#L204)

<a name="typeStoSubD"></a>

### typeStoSubD - TypedStoSubpred Definition
[`definition TypedStoSubpred`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/TypeSafe_Storage.thy#L129)

<a name="compStoSubD"></a>

### compStoSubD - CompStoType Definition
[`definition CompStoType`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/TypeSafe_Storage.thy#L166)

<a name="typesafeDef"></a>

### typesafeDef - TypeSafe1 Definition
[`definition typesafe1`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/TypeSafe_Statements.thy#L28)

<a name="typeconD"></a>

### typeconD - TypeCon Definition
[`definition typeCon`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/TypeSafe_Expressions.thy#L33)

<a name="mconD"></a>

### mconD - MCon Definition
[`definition MCon`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/TypeSafe_Memory.thy#L70)

<a name="sconD"></a>

### sconD - SCon Definition
[`definition SCon`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/TypeSafe_Storage.thy#L70)

<a name="typecompatD"></a>

### typecompatD - TypeCompat Definition
[`definition typeCompat`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/TypeSafe_Expressions.thy#L113)

<a name="uniqLocD"></a>

### uniqLocD - Unique Locations Definition
[`definition unique_locations`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/TypeSafe_Memory.thy#L113)

<a name="compmemptrsD"></a>

### compmemptrsD - CompMemPtrs
*Note: Referenced in commit history but may have been removed or renamed*

<a name="lesstopD"></a>

### lesstopD - LessThanTopLocs Definition
[`definition LessThanTopLocs`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/TypeSafe_Memory.thy#L135)

<a name="safecontractD"></a>

### safecontractD - Safe Contract
[`definition safecontract`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/TypeSafe_Contracts.thy#L89)

<a name="methodvarsD"></a>

### methodvarsD - MethodVarsNoPref
[`definition methodVarsNoPref`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/TypeSafe_Contracts.thy#L67)

## Accounts and Balance

<a name="baltypesD"></a>

### baltypesD - Balance Types
[`definition balanceTypes`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/TypeSafe_Contracts.thy#L44)

<a name="svalueTypes"></a>

### svalueTypes - SValue Types
[`definition svalueTypes`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/TypeSafe_Contracts.thy#L52)

<a name="accountD"></a>

### accounts - Accounts Definition
[`record account`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Accounts.thy#L17-L20)

<a name="AddressTypesD"></a>

### AddressTypesD - Address Types Definition
[`type_synonym Address`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Valuetypes.thy#L120)

<a name="atypeD"></a>

### atypeD - Account Type Definition
[`datatype atype`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/Accounts.thy#L9-L11)

<a name="fullyInitialisedD"></a>

### fullyInitialisedD - Fully Initialised Definition
[`definition fullyInitialised`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/TypeSafe_Statements.thy#L131)

<a name="memoryLinkageD"></a>

### memoryLinkageD - Memory Linkage Properties
[`definition memoryLinkage`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/TypeSafe_Statements.thy#L144)

## Type Safety Lemmas

<a name="mselTcL"></a>

### mselTcL - Memory Select TypeCon Lemma
[`lemma msel_typeCon`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/TypeSafe_Expressions.thy#L245)

<a name="sselTcL"></a>

### sselTcL - Storage Select TypeCon Lemma
[`lemma ssel_typeCon`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/TypeSafe_Expressions.thy#L312)

<a name="rexpTcL"></a>

### rexpTcL - Right Expression TypeCon Lemma
[`lemma rexp_typeCon`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/TypeSafe_Expressions.thy#L398)

<a name="lexpStorageL"></a>

### lexpStorageL - Left Expression Storage Lemma
[`lemma lexpStorageG`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/TypeSafe_Storage.thy#L245)

<a name="lexpMemL"></a>

### lexpMemL - Left Expression Memory Lemma
[`lemma lexpIndexMem`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/TypeSafe_Memory.thy#L267)

<a name="TSStatementL"></a>

### TSStatementL - TypeSafe Statements Lemma
[`lemma TypeSafe_Statements`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/TypeSafe_Statements.thy#L189)

<a name="exprTcL"></a>

### exprTcL - Expression TypeCon Lemma
[`lemma expr_typeCon`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/TypeSafe_Expressions.thy#L156)

<a name="mcCpm2mL"></a>

### mcCpm2mL - MCon Copy Memory to Memory Lemma
[`lemma MCon_cpm2m`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/TypeSafe_Memory.thy#L322)

<a name="loadTcL"></a>

### loadTcL - Load TypeCon Lemma
[`lemma load_typeCon`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/TypeSafe_Expressions.thy#L289)

<a name="tsDeclL"></a>

### tsDeclL - TypeSafe Declaration Lemma
[`lemma typesafe_decl`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity/blob/main/TypeSafe_Statements.thy#L167)

---

*Note: Replace `REPO_URL` with the actual GitHub repository URL. Some definitions may have variations in naming or location across different versions of the files in the artefact directories.*

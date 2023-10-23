# Transferring Ether can invoke contracts

It's worth noting that transferring ether to a contract, allows that contract to run a function. Depending on the implementation of transfers there can be limited gas available when this occurs. This is the main reason why transfers are considered an "effect" in the [Checks-Effects-Interactions Pattern](CEIP.md).

For more information, see for example [related information for Solidity](https://docs.soliditylang.org/en/v0.8.10/contracts.html?highlight=receive%20function#receive-ether-function).
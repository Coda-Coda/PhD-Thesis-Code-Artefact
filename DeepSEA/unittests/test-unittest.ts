import { Chain } from './chain'
import { padName } from './utils'

export async function runTest(
  chain: Chain, name: string, calls: any[], constructorArgs=[], verbose=false) {

  await chain.deployContract(name, constructorArgs)

  for (const func of calls) {
    let padded = padName(func.name)
    await chain.callMethod(func.name, func.args, func.options)
    .then((result) => {
      if (func.expectValue) {
        if (func.expectValue.ethereum && chain.constructor.name == "EthereumChain") {
          // Specific expected value for Ethereum
          if (result == func.expectValue.ethereum)
            console.log(padded, "pass✅ (with correct value)");
          else
            console.log(padded, "fail❌ (expected "
                                  + func.expectValue.ethereum
                                  + " but got " + result + ")");
        }
        else if (func.expectValue.conflux && chain.constructor.name == "ConfluxChain") {
          // Specific expected value for Conflux
          if (result == func.expectValue.conflux)
            console.log(padded, "pass✅ (with correct value)");
          else
            console.log(padded, "fail❌ (expected "
                                  + func.expectValue.conflux
                                  + " but got " + result + ")");
        }
        else {
          // Same expected value for all chains
          if (result == func.expectValue)
            console.log(padded, "pass✅ (with correct value)");
          else
            console.log(padded, "fail❌ (expected "
                                  + func.expectValue
                                  + " but got " + result + ")");
        }
      }
      else if (func.expectSuccess)
        console.log(padded, "pass✅");
      else
        console.log(padded, "fail❌");

      if (verbose)  console.log(JSON.stringify(result, null, 2));
    }, (error) => {
      if (!func.expectSuccess)
        console.log(padded, "pass✅");
      else
        console.log(padded, "fail❌");

      if (verbose) console.log(JSON.stringify(error, null, 2));
    })
  }
}

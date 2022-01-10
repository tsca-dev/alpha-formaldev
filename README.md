# requirements

1. install mi-cho-coq of `dev` branch (762928b1a9d30e4cd0ce3f13bca51664ff4a53cf).
2. install `coq-mathcomp-ssreflect.1.11.0`.

# contents

currently 4 "families" of contracts are formally verified in this repository
- "*wrapper*", a contract TSCA Broker uses to instantiate actual smart contracts
  according to user requests

- "*graveyard*", a trivial smart contract template to be used with TSCA,
  each instance of which will happily accept any amount of tezzes and hold on it forever.

- "*frozen*", a medium-low-complexity contract template to be used with TSCA,
  each instance of which is a vaulted fund with a maturing date.

- "*crowdfunding*", a medium-high-complexity contract template to be used with TSCA,
  each instance of which is a fundraising contract, where the raiser easily starts
  fundraising campaigns.

# organization

all contract families are authored and mechanically verified with the Mi-cho-coq
framework. for each family (take the example of "frozen"), there are 1 source
file and 1 or 2 derived files:
- `frozen.v` : the Coq source code, containing the contract source code,
   properties asserted, and mechanical verification of those properties
- `frozen.tz` : the Michelson code of the effective smart contract for instances
  of the contract family
- `frozen.ccg` : the TSCA-compatible smart contract template (or better,
  contract generator). `ccg` files are uploaded to TSCA brokers to facilitate
  on-chain smart contract origination.

  Please note that Since "wrapper" is not a contract template, it does not
  have a corresponding `ccg` file.

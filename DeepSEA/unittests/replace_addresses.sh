#!/bin/bash

set -x

# dsc=dsc # If dsc is on the path
dsc=../_build/default/Edsger/edsger.bc
amm='contracts/amm.ds'
amm_basename=$(basename $amm)
amm_with_addresses=${amm_basename%.ds}_with_addresses.ds

addresses=$(</dev/stdin)
addr1=$(echo $addresses | cut -d " " -f 1)
addr2=$(echo $addresses | cut -d " " -f 2)
addr3=$(echo $addresses | cut -d " " -f 3)

sed \
	-e "s/erc20Token0.*=.*address(.*)/erc20Token0 = address($addr1)/" \
	-e "s/erc20Token1.*=.*address([^)]*)/erc20Token1 = address($addr2)/" \
	-e "s/liquidityToken.*=.*address(.*)/liquidityToken = address($addr3)/" \
	"$amm" > "$amm_with_addresses"

"$dsc" "$amm_with_addresses" combined-json > "build/${amm_with_addresses%.ds}.json"

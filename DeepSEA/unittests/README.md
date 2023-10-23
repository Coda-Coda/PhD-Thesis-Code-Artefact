To run the tests:
  1. `npm install` to get Node.js dependencies
  2. `./start_conflux.sh` in a separate terminal, and start Ganache (for Ethereum tests)
    -  Be sure to clone the `conflux-rust` repo, and within `start_conflux.sh`, set `conflux` to the location of your repo clone. You can also pass the location of your conflux repo clone as the first argument to `start_conflux.sh`.
    -  Ganache can be run with `npm run ganache` if `npm install` was used to install dependencies.
  3. `./run_unittests.sh`

Alternatively:
  1. Run `./autorun_unittests.sh` from within this folder.
     - This will carry out the above steps and compare the output with `./expected_output.log`. This automatically installs v1.1.5 of `conflux-rust` if the repo does not already exist at `../../conflux-rust`.
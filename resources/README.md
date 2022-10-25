# Instructions to install Stormpy on Mac

- Ensure you have homebrew setup
- Run `./build_dependencies.sh` to ensure you have the required dependencies for CArL.
- Run `./build_carl.sh master14 release` to install just the lib_carl from master14 branch of carl. The tests, if done seperately will not run as we have not built the whole library.
- Run `./build_carl_parser.sh` to build carl-parser. This will take sometime mostly in the Antlr building phase.
- Run `./build_pycarl.sh master release` to build pycarl. 
- Next we build storm with `./build_storm.sh 1.6.3 release binaries`. You may run into a problem with cudd. Follow [this issue](https://github.com/moves-rwth/storm/issues/104) resolution on their Github.
- For stormpy, run `./build_stormpy.sh 1.6.3 release /Users/oyendriladobe/Documents/Research/setup_for_stormpy/storm/build`

For future installation, we can upadte to 1.6.4 or whatevr is the stable combo.
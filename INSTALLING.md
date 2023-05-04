# Installing H-Intercal

You shouldn't. But if you really want to, see below.

### Packages

H-Intercal requires the following packages:

megaparsec
containers
parser-combinators
split
random
cmdargs

These packages should be installed automatically by stack, but the list is included just in case.

### How to install H-Intercal

Clone the git repository onto our computer and run the following command in the project directory.

```
stack build
```

This should build the project and install the necessary packages.

### Running an Intercal file

The compiler can only interpret Intercal-72 features, so don't try to use files from C-Intercal or other distributions.

Some example files can be found in the [examples](examples/) directory.

To run an intercal file use the following command in the program directory:

```
stack run -- -f=filename
```
The -- is important, because it allows arguments to be passed directly to the haskell program, rather than to the stack run command.

To run the fibonacci example program:

```
stack run -- -f=examples/fib.i -r=False
```

For more information on possible flags:

```
stack run -- --help
```
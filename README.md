# Folderol
Folderol is a toy theorem prover implemented according to the paper [Designing a Theorem Prover](https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-192.pdf).

## Building
[Install OCaml](https://ocaml.org/docs/install.html) and run the following commands:
```
git clone https://github.com/jubnzv/folderol.git
cd folderol
opam install --deps-only .    # first time only
dune build
```

The built binary will be saved in `_build/default/src/bin/folderol.exe`.

## Usage
Run the binary and pass the input file as its first argument, e.g.:
```
_build/default/src/bin/folderol.exe examples/assoc.txt
```

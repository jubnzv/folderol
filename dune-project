(lang dune 2.0)
(using menhir 2.0)

(generate_opam_files true)

(name folderol)
(version 0.0.1)
(authors "Georgiy Komarov")
(license MIT)
(source (github jubnzv/folderol))
(maintainers "Georgiy Komarov <jubnzv@gmail.com>")

(package
  (name folderol)
  (synopsis "Toy theorem prover")
  (depends
        (ocaml (>= 4.14))
        (core :build)
        (menhir (and :build (= 20210929)))
        (menhirLib (and :build (= 20210929)))
        (ppx_inline_test :build)))

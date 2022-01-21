<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# lemonde

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/thery/lemonde/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/thery/lemonde/actions?query=workflow:"Docker%20CI"




Les énigmes du Monde

Une tentative de formaliser en Coq les problèmes proposés par le journal
Le Monde en 2013 comme énigmes mathématiques.

[Les vidéos](http://www-sop.inria.fr/marelle/Laurent.Thery/LeMonde/index.html)

## Meta

- Author(s):
  - Laurent Théry
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.15 or later
- Additional dependencies:
  - [MathComp ssreflect 1.14 or later](https://math-comp.github.io)
  - [MathComp fingroup 1.14 or later](https://math-comp.github.io)
  - [MathComp algebra 1.14 or later](https://math-comp.github.io)
- Coq namespace: `lemonde`
- Related publication(s): none

## Building and installation instructions

The easiest way to install the latest released version of lemonde
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-lemonde
```

To instead build and install manually, do:

``` shell
git clone https://github.com/thery/lemonde.git
cd lemonde
make   # or make -j <number-of-cores-on-your-machine> 
make install
```




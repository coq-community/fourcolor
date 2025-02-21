<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# The Four Color Theorem

[![Docker CI][docker-action-shield]][docker-action-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]

[docker-action-shield]: https://github.com/coq-community/fourcolor/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/coq-community/fourcolor/actions/workflows/docker-action.yml

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237663-coq-community-devs.20.26.20users



This library contains a formal proof of the Four Color Theorem in Coq,
along with the theories needed to support stating and then proving the Theorem.
This includes an axiomatization of the setoid of classical real numbers,
basic plane topology definitions, and a theory of combinatorial hypermaps.

## Meta

- Author(s):
  - Georges Gonthier (initial)
- Coq-community maintainer(s):
  - Yves Bertot ([**@ybertot**](https://github.com/ybertot))
- License: [CeCILL-B](LICENSE)
- Compatible Coq versions: 8.18 or later
- Additional dependencies:
  - [MathComp ssreflect 2.1.0 or later](https://math-comp.github.io)
  - [MathComp algebra](https://math-comp.github.io)
  - [Hierarchy Builder](https://github.com/math-comp/hierarchy-builder) 1.5.0 or later
- Coq namespace: `fourcolor`
- Related publication(s):
  - [Formal Proof—The Four-Color Theorem](https://www.ams.org/notices/200811/tx081101382p.pdf) 
  - [A computer-checked proof of the Four Color Theorem](https://inria.hal.science/hal-04034866/document) 

## Building and installation instructions

The easiest way to install the latest released version of The Four Color Theorem
is via [opam](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-fourcolor
```

If you are only interested in the formalization of real numbers, you can install
it separately:

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-fourcolor-reals
```

To instead build and install the whole project manually from the repository, do:

``` shell
git clone https://github.com/coq-community/fourcolor.git
cd fourcolor
make   # or make -j <number-of-cores-on-your-machine> 
make install
```

## Documentation

The [Four Color Theorem](https://en.wikipedia.org/wiki/Four_color_theorem) (Appel & Haken, 1976) is a landmark result of graph theory.

The formal proof is based on the [Mathematical Components](https://github.com/math-comp/math-comp) library.

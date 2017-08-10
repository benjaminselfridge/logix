# logix (Logic Explorer)
Version 0.2.1
Copyright Ben Selfridge 2017

A customizable proof construction tool for sequent calculi.

## Introduction

logix is a tool for exploring generic sequent calculi. It was inspired by the
book "Structural Proof Theory" by Sara Negri & Jan von Plato (Cambridge
University Press, 2001), and is really a spiritual successor to
[PESCA](https://github.com/alexandrelucchesi/pesca), the proof editor companion
to that book developed by [Aarne
Ranta](http://www.cse.chalmers.se/~aarne/). logix was intended to be like PESCA,
but with more general capabilities and a slightly more intuitive interface.

logix is intended to be very extensible. I tried to take as little for granted as
possible about the target theory; even the primitive connectives are customizable;
for instance, & and | come as components of built-in calculi, but you can extend
logix by defining your own primitive operators and deduction rules in the source code
(src/Calculi.hs). I put a lot of effort into making sure that defining new sequent
calculi was as straightforward and obvious as possible.

### What's the point?

logix is primarily an educational tool for myself. I wanted to learn about structural
proof theory, and the best way to learn how to do math is to make a computer do it
for you. However, I also would like other people to use the tool, so I have tried to
make it as usable as possible by people who actually know something about this
stuff.

## Installation

To install logix, simply type

```
cabal install
```

at the root level. Alternatively, if you have Haskell Stack, you can type

```
stack install
```

Either of these commands will install logix to wherever your default location is
for cabal installations.

## Use

After you install logix, assuming the location of the executable on your path,
you can start it up as follows:

```
$ logix
LogiX (Logic Explorer) v0.2.1
a customizable proof construction tool for sequent calculi
(c) Ben Selfridge 2017

Type "help" for a list of commands.
> 
```

For a full list of commands, type `help`. The only thing you need to know that
isn't in the help listing is the correct format for formulas and sequents. As an
illustrative example, the following command will begin a proof session with the
sequent `a | b => ~(~a & ~b) & (b <-> b)`:

```
> top a | b => ~(~a & ~b) & (b <-> b)
Changing goal to "a ∨ b ⇒ ¬(¬a & ¬b) & (b ↔ b)".
```

The important thing is to remember the special symbols; `=>` is the sequent
separator, which divides the left- and right-hand sides of a sequent. The binary
operators `&`, `|`, `->`, and `<->` are self-explanatory. `~` is unary
negation. `_|_` is bottom, or false. `a <-> b` and `~a` are both just abbreviations
for `(a -> b) & (b -> a)` and `(a -> _|_)`, respectively. Quantifiers are input via
`forall x. P(x)` and `exists x. P(x)`. Below is an illustration of how we would
begin a proof that the classic "Barber's paradox" is unsatisfiable:

```
> top => ~exists x. (Man(x) & forall y. (Man(y) -> (Shaves(x,y) <-> ~Shaves(y,y))))
Changing goal to " ⇒ ¬∃x.(Man(x) & ∀y.(Man(y) ⊃ (Shaves(x, y) ↔ ¬Shaves(y, y))))".
```

By default, logix displays sequents using unicode symbols for all these connectives,
but you can turn that off with the `unicode` command.

If you enter the sequent incorrectly, logix will report a parse error and not give
you any helpful information.

We note here that the logical connectives used in the examples above are specific to
the particular calculi that come with logix in src/Calculi.hs, and are not
built-in. Every calculus in logix is defined completely separately from the core
deduction engine.

## Extending logix

To extend logix with your own sequent calculi, edit the file src/Calculi.hs encode
the calculus using the other calculi as models. It's pretty easy to define your own
connectives and abbreviations, and the examples in there should be straightforward to
imitate. logix is intended to allow encodings of arbitrary sequent calculi, so if you
have something you can't express with the tools provided, please let me know.

## More info & current status

I am currently planning to add a mechanism for theory-building via axioms/assumptions
and theorems. This would enable one to build the theory of groups into a logix
session and prove theorems about groups without having to use cumbersome formulas
every time. Axioms would be top-level assumptions that would be automatically
inserted into the left-hand side of every goal sequent initiated by the `top`
command. Theorems would be similarly inserted. We would abbreviate axioms and
theorems by their names wherever they appear verbatim in a sequent. My goal is to
make working with theories like Group as straightforward and clean as possible; right
now, it's technically possible to do group theory, but I don't want to because I have
to mentally parse the entire set of group axioms every time I want to figure out
which rule to apply.  Abbreviations and top-level axioms/theorems are necessary to do
anything useful, so that is definitely coming.

Please contact me if you have any feedback or questions, and especially if you
discover a bug.

## References

[1] Negri, Sara, Aarne Ranta, and Jan Von Plato. [Structural Proof
Theory](https://www.amazon.com/Structural-Proof-Theory-Professor-Negri/dp/0521068428/). Cambridge:
Cambridge U, 2000. Print.
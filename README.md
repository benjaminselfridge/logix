# logix (Logic Explorer)

An interactive proof assistant for sequent calculi.

## Introduction

logix is a tool for exploring generic sequent calculi. It was inspired by the
book "Structural Proof Theory" by Sara Negri & Jan von Plato (Cambridge
University Press, 2001), and is really a spiritual successor to
[PESCA](https://github.com/alexandrelucchesi/pesca), the proof editor companion
to that book developed by [Aarne
Ranta](http://www.cse.chalmers.se/~aarne/). logix was intended to be like PESCA,
but with more general capabilities and a slightly more intuitive interface.

### Improvements on PESCA

One limitation of PESCA was that it was could only work with sequent calculi
with top-down determinacy. That is, given a rule, and an instantiation of the
conclusion of that rule, there is no ambiguity as to how to instantiate the
premises. This means that any calculus with separate contexts was off the
table. This is a pretty severe limitation, and it's not a fundamental one. It
came from the way calculi were specified in PESCA; a rule is just a *function*
that takes a sequent as an argument and returns a list of sequents as premises,
or additional proof obligations. So, for instance, you could specify a shared
context rule like

```
  A, B, Gamma => Delta
  --------------------- (L&)
  A & B, Gamma => Delta
```

because the (single) premise is a function of the conclusion; that is, given a
fixed conjunctive formula `A & B` in the sequent to be derived, we can generate
the premises with no ambiguity. This forbids, for instance, a rule like

```
  Gamma => A   Delta => B
  ----------------------- (R&)
   Gamma, Delta => A & B
```

because we have two contexts in the conclusion that must be "split" in the two
premises, but there's no deterministic way to tell *how* they should be
split. However, this is easily solved by just listing all possible ways to
separate the antecedent formulas in the conclusion into the separate contexts
`Gamma` and `Delta`. Another example is the following rendering of the law of
excluded middle:

```
  P, Gamma => C   ~P, Delta => C
  ------------------------------ (EM)
        Gamma, Delta => C
```

This rule (and the rule R& above it) are used in the classical single-succeedent
calculus G0ip+Gem-at (from Negri & von Plato, pg. 114). This calculus (and the
intuitionistic version, G0ip) were not available in PESCA, because all rules
with multiple premises used separate contexts, and this law of excluded middle
is even worse -- not only do we have to split up the antecedent formulas
somehow, but we also have to add a *new* atomic formula (`P`) to the premises!
Clearly this cannot be encoded as a simple function of the conclusion.

In logix, we solve these problems by enhancing the expressiveness of the
calculus specification language and querying the user for more feedback when
needed. We also have made several interface improvements from PESCA; it is
easier to pick the "right" rule to use at a given node of the proof tree because
logix lists all available rules and the proof obligations they would generate. A
cursory glance at this list enables the user to easily pick a rule that will
generate obligations she thinks may be provable (and which, hopefully, are
simpler than the current subgoal).

In summary, the improvements on PESCA can be summarized as follows:
* Handles arbitrary calculi cleanly (no top-down determinacy required)
* Easier proof navigation
* Simpler and clearer "applicable rule" listing
* Better ASCII pretty printing

### Extensibility

## Installation

## Use

## More info
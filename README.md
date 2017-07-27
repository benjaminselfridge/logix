# logix (Logic Explorer)
Copyright Ben Selfridge 2017

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
premises. From the appendix on PESCA in Negri & von Plato:

> The domain of sequent calculi allows for indefinitely many variations, which
> are not due to disagreements on what should be provable but to different
> decisions on the fine structure of proofs. In terms of provability, it is
> usually enough to tell whether a calculus is intuitionistic of classical. In
> the properties of proof structure, there are many more choices. The very
> implementation of PESCA precludes most of them, but it still leaves room for
> different calculi ... These calculi can be characterized as having:
>
>    *Shared multiset contexts, no structural rules.*
>
>  ... The fundamental common property of the calculi treated by PESCA is
>  **top-down determinacy**:
>
>    *Given a conclusion and a rule, the premisses are determined.*

This means that any calculus with separate contexts was off the
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

This rule (and the rule `R&` above it) are used in the classical
single-succeedent calculus G0ip+Gem-at (from Negri & von Plato, pg. 114). This
calculus (and the intuitionistic version, G0ip) were not available in PESCA,
because all rules with multiple premises used separate contexts. This law of
excluded middle is actually even worse than that -- not only do we have to split
up the antecedent formulas somehow, but we also have to add a *new* atomic
formula (`P`) to the premises!  Clearly this cannot be encoded as a simple
function of the conclusion.

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

In logix, specification of deduction rules is based on the concept of
*patterns.* Every rule corresponds to a pattern, or a set of patterns, that
match against particular instances of that rule. As an example, the G0ip
calculus (with separate contexts) is specified as follows:

```
p = AtomPat "P"
a = VarPat "A"
b = VarPat "B"
c = VarPat "C"
gamma = SetPat "Gamma"
delta = SetPat "Delta"

g0ip = Calculus {
  name = "g0ip",
  axioms = [("Axiom", [p] ::=> [p])],
  rules =
  [ ("R&", ([ [gamma] ::=> [a], [delta] ::=> [b] ],
              [gamma, delta] ::=> [a $& b]))
  , ("R|1", ([ [gamma] ::=> [a] ],
               [gamma] ::=> [a $| b]))
  , ("R|2", ([ [gamma] ::=> [b] ],
               [gamma] ::=> [a $| b]))
  , ("R->", ([ [a, gamma] ::=> [b] ],
               [gamma] ::=> [a $> b]))
  , ("L&", ([ [a, b, gamma] ::=> [c] ],
              [a $& b, gamma] ::=> [c]))
  , ("L|", ([ [a, gamma] ::=> [c], [b, delta] ::=> [c] ],
              [a $| b, gamma, delta] ::=> [c]))
  , ("L->", ([ [gamma] ::=> [a], [b, delta] ::=> [c] ],
               [a $> b, gamma, delta] ::=> [c]))
  , ("L_|_", ([],
              [botpat] ::=> [c]))
  , ("Wk", ([ [gamma] ::=> [c] ],
              [a, gamma] ::=> [c]))
  , ("Ctr", ([ [a, a, gamma] ::=> [c] ],
               [a, gamma] ::=> [c]))
  ]}
```

This is almost a verbatim translation of the listing of this calculus in
[1]. Other calculi can be specified similarly. Our goal is to have no
limitations on the expressiveness of a calculus. As an example, the `R&` rule
above is represented as a pair

```
("R&", ([ [gamma] ::=> [a], [delta] ::=> [b] ],
          [gamma, delta] ::=> [a $& b]))
```

It's not difficult to decipher the meaning here. If in the course of a
derivation in logix, the `R&` rule applies to the current subgoal, the user will
be presented with every valid instantiation of this rule (in particular, every
possible way to split the antecedents of the subgoal into separate contexts
Gamma and Delta). This may seem like overkill, but if one wants to construct
proofs in a not-very-tractable calculus like G0ip, it's nice to be able to see
every potential instance of an applicable rule.

logix was designed from the start to be maximally extensible. We have ideas for
improving this extensibility, but for now, it's relatively easy to add a
calculus to logix. One merely has to edit the file Calculi.hs, following the
other calculi as an example.

The only built-in limitation is the use of multisets as the underlying
representation; this follows [1], but also prohibits more restrictive kinds of
calculi, for instance Gentzen's original LK system where the contexts were
represented as lists, with a built-in structural rule "Exchange" for reordering
formulas in the list. LK can still be encoded, but not as originally conceived;
the exchange rule would be useless, since multisets are unordered.

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
LogiX (Logic Explorer)
interactive proof assistant for sequent calculi
copyright Ben Selfridge 2017

Type "help" for a list of commands.
>
```

For a full list of commands, type `help`. The only thing you need to know that
isn't in the help listing is the correct format for formulas and sequents. As an
illustrative example, the following command will begin a proof session with the
sequent `a | b => ~(~a & ~b) & (b <-> b)`:

```
> top a | b => ~(~a & ~b) & (b <-> b)
```

If you enter the sequent incorrectly, logix will report a parse error and not
give you any helpful information. This is something that needs to be improved,
but it's still easy enough to figure out what you did wrong. logix can
automatically parenthesize expressions; ~ binds the tightest, then & and |, then
->, and finally <-> binds the loosest. Every binary connective is right
associative, so

```
> top => a -> b -> a
```

gets parsed as `=> a -> (b -> a)` (which is probably what you'd want in this
particular example!)

If you need any help using logix, feel free to contact me at my email address,
benselfridge at gmail dot com.

## More info & current status

Currently, logix only supports propositional calculus because it is still at a
proof-of-concept stage of development. However, I have plans to support full
first-order predicate calculus with equality in the very near future (I want to
do some group theory!). Aside from that (temporary) limitation, logix can pretty
much represent any sequent calculus I know of. The only exceptions from [1] are
the GN, GM, NG and MG calculi, which use patterns like A^n, representing *any
number of appearances* of formula A. This could be added as a new kind of
pattern, but I have not prioritized that at this stage.

Please contact me if you have any feedback or questions.

## References

[1] Negri, Sara, Aarne Ranta, and Jan Von Plato. [Structural Proof
Theory](https://www.amazon.com/Structural-Proof-Theory-Professor-Negri/dp/0521068428/). Cambridge:
Cambridge U, 2000. Print.
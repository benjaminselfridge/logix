# logix (Logic Explorer)
Version 0.2.0
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

One limitation of PESCA was that it could only work with sequent calculi with
top-down determinacy. That is, given a rule, and an instantiation of the conclusion
of that rule, there is no ambiguity as to how to instantiate the premises. From the
appendix on PESCA in Negri & von Plato:

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

This means that any calculus with separate contexts was off the table. This is a
pretty severe limitation (at least in terms of the ability to encode the various
logics in that book), and it's not a fundamental one. It came from the way calculi
were specified in PESCA; a rule is just a *function* that takes a sequent as an
argument and returns a list of sequents as premises, or additional proof
obligations. So, for instance, you could specify a shared context rule like

```
  A, B, Γ => Δ
  ------------- (&)
  A & B, Γ => Δ
```

because the (single) premise is a function of the conclusion; that is, given a
fixed conjunctive formula `A & B` in the sequent to be derived, we can generate
the premises with no ambiguity. This forbids, for instance, a rule like

```
  Γ => A   Δ => B
  --------------- (R&)
   Γ, Δ => A & B
```

because we have two contexts in the conclusion that must be split in the two
premises, but there's no deterministic way to tell *how* they should be
split. However, this is easily solved by just listing all possible ways to
separate the antecedent formulas in the conclusion into the separate contexts
`Γ` and `Δ`. Another example is the following rendering of the law of
excluded middle:

```
  P, Γ => C   ~P, Δ => C
  ---------------------- (EM)
        Γ, Δ => C
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
match against particular instances of that rule. As an example, the G0i
calculus (with separate contexts) is specified as follows:

```
p = PredPat "P"
a = FormPat "A"
b = FormPat "B"
c = FormPat "C"
gamma  = SetPat "Γ"
gamma' = SetPat "Γ'"
delta  = SetPat "Δ"
delta' = SetPat "Δ'"
a_x_y = SubstPat "x" (VarPat "y") "A"
a_x_t = SubstPat "x" (TermPat "t") "A"
forall_x_a = ForallPat "x" a
exists_x_a = ExistsPat "x" a
nofree_y = NoFreePat "y"

g0ip :: Calculus
g0ip = Calculus {
  name = "g0ip",
  axioms = [("Axiom", [a] ::=> [a])],
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
  , ("Lforall", ([ [a_x_t, forall_x_a, gamma] ::=> [c] ],
                 [ forall_x_a, gamma] ::=> [c]))
  , ("Rforall", ([ [gamma] ::=> [a_x_y] ],
                 [nofree_y gamma] ::=> [nofree_y forall_x_a]))
  , ("Lexists", ([ [a_x_y, gamma] ::=> [c] ],
                 [nofree_y exists_x_a, nofree_y gamma] ::=> [nofree_y c]))
  , ("Rexists", ([ [gamma] ::=> [a_x_t] ],
                 [gamma] ::=> [exists_x_a]))
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
Γ and Δ). This may seem like overkill, but if one wants to construct
proofs in a not-very-tractable calculus like G0i, it's nice to be able to see
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
LogiX (Logic Explorer) v. 0.2.0
interactive proof assistant for sequent calculi
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
you any helpful information. logix can automatically parenthesize expressions; ~,
forall and exists bind the tightest, then & and |, then ->, and finally <-> binds the
loosest. Every binary connective is right associative:

```
> top => a -> b & c & d -> a
Changing goal to " ⇒ a ⊃ ((b & (c & d)) ⊃ a)".
```

## More info & current status

Currently, logix supports predicate calculus without equality. However, I have plans
to support term equality in the very near future. Aside from that (temporary)
limitation, logix can pretty much represent any sequent calculus I know of. The only
exceptions from [1] are the GN, GM, NG and MG calculi, which use patterns like A^n,
representing *any number of appearances* of formula A. This could be added as a new
kind of pattern, but I have not prioritized that at this stage.

I am also planning to add a mechanism for theory-building via axioms/assumptions and
theorems. This would enable one to build the theory of groups into a logix session
and prove theorems about groups without having to use cumbersome formulas every
time. Axioms would be top-level assumptions that would be automatically inserted into
the left-hand side of every goal sequent initiated by the `top` command. Theorems
would be similarly inserted. We would abbreviate axioms and theorems by their names
wherever they appear verbatim in a sequent. My goal is to make working with theories
like Group as straightforward and clean as possible; right now, it's technically
possible to do group theory, but I don't want to because I have to parse the entire
set of group axioms every time I want to figure out which rule to apply.
Abbreviations and top-level axioms/theorems are necessary to do anything useful, so
that is definitely coming.

Please contact me if you have any feedback or questions, and especially if you
discover a bug.

## References

[1] Negri, Sara, Aarne Ranta, and Jan Von Plato. [Structural Proof
Theory](https://www.amazon.com/Structural-Proof-Theory-Professor-Negri/dp/0521068428/). Cambridge:
Cambridge U, 2000. Print.
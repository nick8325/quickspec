QuickSpec: equational laws for free!
====================================

QuickSpec takes your Haskell code and, as if by magic, discovers laws about it.
You give QuickSpec a collection of Haskell functions; QuickSpec tests your functions
with QuickCheck and prints out laws which seem to hold.

For example, give QuickSpec the functions `reverse`, `++` and `[]`, and it will
find six laws:

```haskell
reverse [] == []
xs ++ [] == xs
[] ++ xs == xs
reverse (reverse xs) == xs
(xs ++ ys) ++ zs == xs ++ (ys ++ zs)
reverse xs ++ reverse ys == reverse (ys ++ xs)
```

QuickSpec can find equational laws as well as conditional equations. All you
need to supply are the functions to test, as well as `Ord` and `Arbitrary`
instances for QuickSpec to use in testing; the rest is automatic.

For information on how to use QuickSpec, see
[the documentation](http://hackage.haskell.org/package/quickspec/docs/QuickSpec.html).
You can also look in the `examples` directory, for example at
`List.hs`, `IntSet.hs`, or `Parsing.hs`. To read about how QuickSpec works, see
our paper, [Quick specifications for the busy programmer](http://www.cse.chalmers.se/~nicsma/papers/quickspec2.pdf).

QuickSpec: equational laws for free!
====================================

Ever get that nagging feeling that your code must satisfy some equational laws,
but not sure what they are? Want to write some QuickCheck properties, but not
sure where to start? QuickSpec might be for you! QuickSpec takes any set of
Haskell functions and tries to discover laws about those functions.

Give QuickSpec the functions `reverse`, `++` and `[]`, for example, and it will
find six laws:

```haskell
reverse [] == []
xs ++ [] == xs
[] ++ xs == xs
reverse (reverse xs) == xs
(xs ++ ys) ++ zs == xs ++ (ys ++ zs)
reverse xs ++ reverse ys == reverse (ys ++ xs)
```

Despite these limitations, QuickSpec works well on many examples. The
best way to get started with it is to look at the `examples` directory,
for example `Arith.hs`,`ListMonad.hs`, or `Parsing.hs`. You can also
look at our paper,
http://www.cse.chalmers.se/\~nicsma/papers/quickspec2.pdf\[Quick
specifications for the busy programmer\].

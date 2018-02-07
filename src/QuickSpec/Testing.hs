-- A type of test case generators.
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
module QuickSpec.Testing where

import QuickSpec.Prop

class Monad m => Tester testcase term m | m -> testcase term where
  test :: Prop term -> m (Maybe testcase)

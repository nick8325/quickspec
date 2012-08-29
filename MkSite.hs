module Main where

import System.FilePath
import System.Environment
import Data.Function
import Data.List

data Line =
    Include (IO [Line])
  | Bird String
  | Normal String

parse :: FilePath -> IO [Line]
parse file = fmap (map parseLine . lines) (readFile file)
  where
    dir = dropFileName file
    parseLine xs
      | include `isPrefixOf` xs =
        let ys = drop (length include) xs
            ('>':zs) = reverse ys
        in Include (parse (dir </> reverse zs))
      where include = "#include <"
    parseLine ('>':' ':xs) = Bird xs
    parseLine xs = Normal xs

include :: Line -> IO [Line]
include (Include xs) = xs
include x = return [x]

debird :: [Line] -> [String]
debird = concatMap mangle . groupBy ((==) `on` isBird)
  where
    isBird Bird{} = True
    isBird _ = False
    mangle xs@(Bird{}:_) =
      "[source,haskell]":
      "-------":
      [ x | Bird x <- xs ] ++
      ["-------"]
    mangle xs@(Normal{}:_) =
      [ x | Normal x <- xs ]

main = do
  [file] <- getArgs
  parsed <- parse file >>= fmap concat . mapM include
  mapM_ putStrLn (debird parsed)
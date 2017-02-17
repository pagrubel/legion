#!/usr/bin/env runhaskell

import Development.Shake
import Development.Shake.Util
import Development.Shake.FilePath
import Data.Maybe

main = shakeArgs shakeOptions $ do  
  want ["semantics.vo", "typecheck.vo", "lemmas.vo"]
  "//*.vo" %> \out -> do
    let source = out -<.> ".v"
    deps <- cmd $ "coqdep " ++ source 
    need $ fromMaybe [] $ lookup out $ parseMakefile $ fromStdout deps
    cmd $ "coqc -I . " ++ source
  phony "clean" $ removeFilesAfter "." ["//*.vo", "//*.glob"]

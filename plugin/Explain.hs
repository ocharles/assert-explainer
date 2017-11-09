module Explain (explainShow) where

explainShow :: Show a => String -> a -> String
explainShow name a = name ++ " = " ++ show a

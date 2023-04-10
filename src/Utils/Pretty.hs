module Utils.Pretty where 

import Text.PrettyPrint

class Pretty p where
  ppr :: Int -> p -> Doc

  pp :: p -> Doc
  pp = ppr 0

parensIf :: Int -> Doc -> Doc
parensIf i = if i /= 0 then parens else id 

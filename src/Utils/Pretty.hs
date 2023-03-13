module Utils.Pretty where 

import Text.PrettyPrint
import qualified Data.Text as T

class Pretty p where
  ppr :: Int -> p -> Doc

  pp :: p -> Doc
  pp = ppr 0

parensIf :: Int -> Doc -> Doc
parensIf i = if i /= 0 then parens else id 

text' :: T.Text -> Doc
text' = text . T.unpack
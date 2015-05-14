module Ext.Show where

   open import Data.String hiding (show)

   -- Conflicts with a name introduced in the 0.9 standard library.
   record Show (A : Set) : Set where
      field
         show : A → String

-------------------------------------------
-- Names as a simple wrapper around strings
module Name where

import Data.String

newtype Name = Name { unName :: String }

-- Show them without quotes
instance Show Name where
  show = unName

instance IsString Name where
  fromString = Name . fromString

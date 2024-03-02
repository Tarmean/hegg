module Data.Equality.Compiler.Utils where
import qualified Data.IntMap as IM
import Data.Vector.Internal.Check (HasCallStack)

(!!!) :: HasCallStack => IM.IntMap a -> IM.Key -> a
(!!!) m k = case IM.lookup k m of
   Just o -> o
   Nothing -> error ("IntMap key " <> show k <> " is not an element ofthe map. Available keys " <> show (IM.size m, take 20 (IM.keys m)))


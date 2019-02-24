{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Params where {


import qualified Data.ByteString as BS;
import qualified Data.Map as M;

newtype ConsensusValue = ConsensusValue (M.Map BS.ByteString BS.ByteString);
newtype Validator = Validator BS.ByteString

}

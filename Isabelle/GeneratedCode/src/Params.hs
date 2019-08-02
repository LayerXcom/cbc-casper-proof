
import qualified Data.ByteString as BS;
import qualified Data.Map as M;

newtype ConsensusValue = ConsensusValue (M.Map BS.ByteString BS.ByteString);
newtype Validator = Validator (M.Map BS.ByteString BS.ByteString);


import Data.Bits
import Debug.Trace (trace)
import Data.Word
import Text.Printf
import qualified Data.ByteString as B
import Data.Char (ord)
import qualified Data.ByteString.Char8 as BC
import System.IO (hSetEncoding, stdout, utf8)


testMessageSchedule = prepareMessageSchedule [0, 1, 2, 3]

initialHashValues :: [Word32]
initialHashValues = [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

k :: [Word32]
k = [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

ch, maj :: Word32 -> Word32 -> Word32 -> Word32
ch x y z = (x .&. y) `xor` (complement x .&. z)

maj x y z = (x .&. y) `xor` (x .&. z) `xor` (y .&. z)

sigma0, sigma1, sum0, sum1 :: Word32 -> Word32
sigma0 x = rotateR x 2 `xor` rotateR x 13 `xor` rotateR x 22
sigma1 x = rotateR x 6 `xor` rotateR x 11 `xor` rotateR x 25
sum0 x = rotateR x 7 `xor` rotateR x 18 `xor` shiftR x 3
sum1 x = rotateR x 17 `xor` rotateR x 19 `xor` shiftR x 10

stringToUtf8Bytes :: String -> [Word8]
stringToUtf8Bytes = concatMap toUtf8 . map ord
  where
    toUtf8 :: Int -> [Word8]
    toUtf8 c
      | c <= 0x7F = [fromIntegral c]
      | c <= 0x7FF = [fromIntegral (0xC0 .|. (c `shiftR` 6)), fromIntegral (0x80 .|. (c .&. 0x3F))]
      | c <= 0xFFFF = [fromIntegral (0xE0 .|. (c `shiftR` 12)), fromIntegral (0x80 .|. ((c `shiftR` 6) .&. 0x3F)), fromIntegral (0x80 .|. (c .&. 0x3F))]
      | otherwise = [fromIntegral (0xF0 .|. (c `shiftR` 18)), fromIntegral (0x80 .|. ((c `shiftR` 12) .&. 0x3F)), fromIntegral (0x80 .|. ((c `shiftR` 6) .&. 0x3F)), fromIntegral (0x80 .|. (c .&. 0x3F))]

prepareMessageSchedule :: [Word32] -> [Word32]
prepareMessageSchedule ws = extendSchedule ws 16
  where
    extendSchedule ws i
      | i >= 64 = ws
      | otherwise =
        let calculated = sum1 (ws !! (i - 2)) + ws !! (i - 7) + sum0 (ws !! (i - 15)) + ws !! (i - 16)
            ws' = ws ++ [calculated]
        in extendSchedule ws' (i + 1)

processChunk :: [Word32] -> [Word32] -> [Word32]
processChunk state chunk = zipWith (+) state $ foldl process state [0..63]
  where
    ws = prepareMessageSchedule chunk
    process s i =
        let (a:b:c:d:e:f:g:h:_) = s
            w = ws !! i
            t1 = h + sigma1 e + ch e f g + (k !! i) + w
            t2 = sigma0 a + maj a b c
        in [t1 + t2, a, b, c, d + t1, e, f, g]

parse32 :: [Word8] -> Word32
parse32 = foldl (\acc x -> (acc `shiftL` 8) .|. fromIntegral x) 0

chunk32 :: [Word8] -> [[Word8]]
chunk32 [] = []
chunk32 ws = take 4 ws : chunk32 (drop 4 ws)

sha256 :: B.ByteString -> String
sha256 bs = concatMap (printf "%08x") finalHash
  where
    finalHash = foldl processChunk initialHashValues chunks
    chunks = map (parseChunk . take 64) $ chunk512 $ padMessage bs
    padMessage :: B.ByteString -> B.ByteString
    padMessage bs = 
        let len = fromIntegral $ 8 * B.length bs :: Word64
            padLen = 64 - ((B.length bs + 1 + 8) `mod` 64)
            lenBytes = B.reverse $ B.pack $ map (fromIntegral . ((len `shiftR`) . (flip (*) 8))) [0..7] 
        in B.concat [bs, B.pack [0x80], B.replicate padLen 0, lenBytes]


parseChunk :: [Word8] -> [Word32]
parseChunk ws = map parse32 $ take 16 $ chunk32 ws ++ replicate (16 - length (chunk32 ws)) (replicate 4 (0 :: Word8))

chunk512 :: B.ByteString -> [[Word8]]
chunk512 bs 
  | B.null bs = []
  | otherwise = 
    let (chunk, rest) = B.splitAt 64 bs 
    in B.unpack chunk : chunk512 rest

main :: IO ()
main = do
  hSetEncoding stdout utf8
  let testCases = ["Hola Mundo", "¿Por qué decidí hacer esto?", "testcase", "Ya me rindo", "No puedo más"]
  let expectedOutputs = ["c3a4a2e49d91f2177113a9adfcb9ef9af9679dc4557a0a3a4602e1bd39a6f481",
                          "2b9bf86e4a3fa539081ee950ca396dca600439f37996c1687d034de3776b0edf",
                          "5659f2efca07c82f1901d48812fdbec3ee923966c789e7f6e610ffc4c4933d91",
                          "86a4e93966c56a8e6b9c373c7d84c3a9a963a22967d619e19b9c517584b9da4e",
                          "aabbba0c8be7d21eeaffb09079b472eb914274df1e211ef34501db3b0cf20c12"]
  putStrLn "Running Test Cases"
  putStrLn "-----------------"
  runTestCases testCases expectedOutputs

runTestCases :: [String] -> [String] -> IO ()
runTestCases [] [] = return ()
runTestCases (msg:msgs) (expected:expecteds) = do
  let output = sha256 (B.pack $ stringToUtf8Bytes msg)  
  putStrLn $ "Input: " ++ msg
  putStrLn $ "Output: " ++ output
  putStrLn $ "Expected: " ++ expected
  putStrLn $ if output == expected then "Pass" else "Fail"
  putStrLn ""
  runTestCases msgs expecteds
runTestCases _ _ = putStrLn "Mismatch between number of test cases and expected outputs."
{-# LANGUAGE OverloadedStrings #-}

module Bedrock (chat, chatWith, BedrockConfig(..), defaultConfig) where

import qualified Data.Aeson as J
import qualified Data.Aeson.KeyMap as KM
import Data.Aeson ((.=))
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BS8
import qualified Data.ByteString.Lazy as LBS
import qualified Data.ByteString.Base16 as B16
import qualified Data.Text as T
import Crypto.Hash.SHA256 (hash, hmac)
import qualified Data.CaseInsensitive as CI
import Data.CaseInsensitive (mk)
import Data.Char (isSpace, toLower, isAlphaNum)
import Data.List (sort, isPrefixOf, dropWhileEnd, intercalate)
import Numeric (showHex)
import Data.Time.Clock (getCurrentTime, UTCTime)
import Data.Time.Format (formatTime, defaultTimeLocale)
import Network.HTTP.Client
import Network.HTTP.Client.TLS (tlsManagerSettings)
import Network.HTTP.Types (hContentType, hAccept)
import System.Environment (lookupEnv)
import System.Directory (getHomeDirectory)

data BedrockConfig = BedrockConfig
  { bcRegion  :: String
  , bcModelId :: String
  , bcMaxToks :: Int
  } deriving (Show)

defaultConfig :: BedrockConfig
defaultConfig = BedrockConfig
  { bcRegion  = "us-east-1"
  , bcModelId = "us.anthropic.claude-sonnet-4-6"
  , bcMaxToks = 4096
  }

data AwsCreds = AwsCreds
  { awsAccessKey  :: String
  , awsSecretKey  :: String
  , awsSessionTok :: Maybe String
  } deriving (Show)

loadCreds :: IO AwsCreds
loadCreds = do
  envAccess <- lookupEnv "AWS_ACCESS_KEY_ID"
  case envAccess of
    Just ak -> do
      sk <- maybe "" id <$> lookupEnv "AWS_SECRET_ACCESS_KEY"
      st <- lookupEnv "AWS_SESSION_TOKEN"
      return $ AwsCreds ak sk st
    Nothing -> loadCredsFile

loadCredsFile :: IO AwsCreds
loadCredsFile = do
  home <- getHomeDirectory
  contents <- readFile (home ++ "/.aws/credentials")
  let ls = lines contents
      profile = lookupEnv "AWS_PROFILE" >>= \p -> return (maybe "default" id p)
  prof <- profile
  let vals = parseProfile prof ls
      get k = maybe (fail $ "missing " ++ k ++ " in ~/.aws/credentials") return
                     (lookup k vals)
  ak <- get "aws_access_key_id"
  sk <- get "aws_secret_access_key"
  let st = lookup "aws_session_token" vals
  return $ AwsCreds ak sk st

parseProfile :: String -> [String] -> [(String, String)]
parseProfile prof = go False
  where
    header = "[" ++ prof ++ "]"
    go _ [] = []
    go active (l:ls)
      | isPrefixOf "[" trimmed =
          if trimmed == header then go True ls else go False ls
      | active, (k, '=':v) <- break (== '=') trimmed =
          (strip k, strip v) : go True ls
      | otherwise = go active ls
      where trimmed = strip l
    strip = dropWhileEnd isSpace . dropWhile isSpace

chat :: String -> IO String
chat = chatWith defaultConfig

chatWith :: BedrockConfig -> String -> IO String
chatWith cfg prompt = do
  creds <- loadCreds

  let body = J.encode $ J.object
        [ "anthropic_version" .= ("bedrock-2023-05-31" :: T.Text)
        , "max_tokens" .= bcMaxToks cfg
        , "messages" .= [ J.object
            [ "role" .= ("user" :: T.Text)
            , "content" .= T.pack prompt
            ] ]
        ]

  now <- getCurrentTime
  let host = "bedrock-runtime." ++ bcRegion cfg ++ ".amazonaws.com"
      path = "/model/" ++ bcModelId cfg ++ "/invoke"
      bodyBS = LBS.toStrict body

  initReq <- parseRequest $ "https://" ++ host ++ path
  let req0 = initReq
        { method = "POST"
        , requestBody = RequestBodyLBS body
        , requestHeaders =
            [ (hContentType, "application/json")
            , (hAccept, "application/json")
            ]
        }

  let signed = signV4 creds (bcRegion cfg) "bedrock" now host path bodyBS req0

  mgr <- newManager tlsManagerSettings
  resp <- httpLbs signed mgr
  let respBody = responseBody resp
  case J.decode respBody of
    Just (J.Object obj) ->
      case KM.lookup "content" obj of
        Just (J.Array arr) | not (null arr) ->
          case head (toList arr) of
            J.Object block ->
              case KM.lookup "text" block of
                Just (J.String t) -> return (T.unpack t)
                _ -> fail $ "unexpected block: " ++ show block
            other -> fail $ "unexpected content element: " ++ show other
        _ -> fail $ "no content in response: " ++ show respBody
    _ -> fail $ "could not parse response: " ++ show respBody
  where
    toList = foldr (:) []

signV4 :: AwsCreds -> String -> String
       -> UTCTime -> String -> String -> BS.ByteString -> Request -> Request
signV4 creds region service now host path body req =
  req { requestHeaders = authHeader : dateHeader : hostHeader : secTokHeaders
                         ++ otherHeaders }
  where
    dateStamp = formatTime defaultTimeLocale "%Y%m%d" now
    amzDate   = formatTime defaultTimeLocale "%Y%m%dT%H%M%SZ" now
    scope     = dateStamp ++ "/" ++ region ++ "/" ++ service ++ "/aws4_request"

    dateHeader = (mk "x-amz-date", BS8.pack amzDate)
    hostHeader = (mk "host", BS8.pack host)
    secTokHeaders = case awsSessionTok creds of
      Just tok -> [(mk "x-amz-security-token", BS8.pack tok)]
      Nothing  -> []

    otherHeaders = filter (\(k,_) -> k /= mk "host") (requestHeaders req)

    allHeaders = sort (dateHeader : hostHeader : secTokHeaders ++ otherHeaders)

    headerName k = CI.foldedCase k

    signedHeadersStr = BS8.intercalate ";"
      [headerName k | (k, _) <- allHeaders]

    canonicalHeaders = BS8.concat
      [ BS8.concat [headerName k, ":", v, "\n"]
      | (k, v) <- allHeaders
      ]

    payloadHash = B16.encode (hash body)

    encodedPath = "/" ++ intercalate "/" (map uriEncode (filter (not . null) (splitOn '/' path)))

    canonicalRequest = BS8.intercalate "\n"
      [ "POST"
      , BS8.pack encodedPath
      , ""
      , canonicalHeaders
      , signedHeadersStr
      , payloadHash
      ]

    stringToSign = BS8.intercalate "\n"
      [ "AWS4-HMAC-SHA256"
      , BS8.pack amzDate
      , BS8.pack scope
      , B16.encode (hash canonicalRequest)
      ]

    signingKey = foldl (\k s -> hmac k (BS8.pack s))
                       (BS8.pack $ "AWS4" ++ awsSecretKey creds)
                       [dateStamp, region, service, "aws4_request"]

    signature = B16.encode (hmac signingKey stringToSign)

    authValue = BS8.concat
      [ "AWS4-HMAC-SHA256 Credential="
      , BS8.pack (awsAccessKey creds), "/", BS8.pack scope
      , ", SignedHeaders=", signedHeadersStr
      , ", Signature=", signature
      ]

    authHeader = (mk "authorization", authValue)

uriEncode :: String -> String
uriEncode = concatMap encChar
  where
    encChar c
      | isAlphaNum c || c `elem` ("-._~" :: String) = [c]
      | otherwise = '%' : map toUpper' (showHex' (fromEnum c))
    showHex' n = let h = showHex n "" in if length h == 1 then '0':h else h
    toUpper' c | c >= 'a' && c <= 'f' = toEnum (fromEnum c - 32)
               | otherwise = c

splitOn :: Char -> String -> [String]
splitOn _ [] = [""]
splitOn d s = case break (== d) s of
  (w, [])   -> [w]
  (w, _:rest) -> w : splitOn d rest

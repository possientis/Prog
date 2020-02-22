{-# LANGUAGE TemplateHaskell        #-}

module  LensProduct
    (   userId
    ,   userName
    ,   createdTime
    ,   expiryTime
    ,   Session
    ,   UserName
    ,   UserId
    )   where

import Control.Lens
import Control.Lens.Unsound

type UserName = String
type UserId   = String

data Session = Session
    { _userId       :: UserId
    , _userName     :: UserName
    , _createdTime  :: String
    , _expiryTime   :: String
    } deriving (Show, Eq)

makeLenses ''Session

-- This case yields a lawful lense, as data underlying product is disjoint
userInfo :: Lens' Session (UserId, UserName)
userInfo = lensProduct userId userName


session :: Session
session = Session "USER-1234" "Joey Tribbiani" "2019-07-05" "2019-08-05"

ex1 :: (UserId, UserName)
ex1 = view userInfo session

-- This case yields an unlawful lense, as data underlying product is not disjoint
alongsideUserId :: Lens' Session (Session, UserId)
alongsideUserId = lensProduct id userId


newSession :: Session
newSession = session { _userId = "USER-5678" }

ex2 :: (Session, UserId)
ex2 = view alongsideUserId (set alongsideUserId (newSession, "USER-9999") session)

-- False: law is broken: what you now get is not what you had set
law1 :: Bool
law1 = ex2 == (newSession, "USER-9999")

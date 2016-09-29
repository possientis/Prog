module SyslogTypes where

{- | Priorities define how important a log message is. -}

data Priority = DEBUG       -- ^ Debug messages
              | INFO        -- ^ Information
              | NOTICE      -- ^ Normal runtime conditions
              | WARNING     -- ^ General Warnings
              | ERROR       -- ^ General Errors 
              | CRITICAL    -- ^ Severe situations
              | ALERT       -- ^ Take immediate action
              | EMERGENCY   -- ^ System is unusable
              deriving (Eq, Ord, Show, Read, Enum)

{- Facilities are used by the system to determine where messages are sent -}

data Facility = Facility -- TODO


codeOfFac = undefined

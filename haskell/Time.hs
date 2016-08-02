import System.Time
import System.Directory(getModificationTime)

-- data ClockTime = TOD Integer Integer

main = do
  now  <- getClockTime          -- getClockTime :: IO ClockTime
  print now                     -- Tue Aug  2 09:53:35 EEST 2016
  let (TOD sec _) = now
  print sec
  print (TOD 1000 0)            -- 1000 seconds after 1 Jan 1970
  -- toCalendarTime is an IO functions, as output depends on local time zone settings
  nowCal <- toCalendarTime now  -- toCalendarTime :: ClockTime -> IO CalendarTime 
  print nowCal                  -- CalendarTime {ctYear = 2016, ctMonth = August, ctDay = 2, ctHour = 10, 
                                -- ctMin = 16, ctSec = 4, ctPicosec = 755026000000, ctWDay = Tuesday, 
                                -- ctYDay = 214, ctTZName = "EEST", ctTZ = 10800, ctIsDST = True} 
  let nowUTC = toUTCTime now    -- not an IO function, does not depend of local time zone settings
  print nowUTC                  -- toUTCTime :: ClockTime -> CalendarTime
  print nowUTC {ctYear = 1960 } -- easy to modify value
  -- toClockTime :: CalendarTime -> ClockTime
  print $ toClockTime (nowUTC {ctYear = 1960})

  -- hmmm this does not return the right type ClockTime
  time <- getModificationTime "/etc/passwd"
  print time



  

{-
data CalendarTime = CalendarTime
  { ctYear :: Int,        -- Year (post-Gregorian)
    ctMonth :: Month,
    ctDay :: Int,         -- Day of the month (1 to 31)
    ctHour :: Int,        -- Hour of the day (0 to 23)
    ctMin :: Int,         -- Minutes (0 to 59)
    ctSec :: Int,         -- Seconds (0 to 61, allowing for leap seconds)
    ctPicosec :: Integer, -- Picoseconds 
    ctWDay :: Day,        -- Day of the week
    ctYDay :: Int,        -- Day of the year (0 to 364 or 365)
    ctTZName :: String,   -- Name of timezone
    ctTZ :: Int,          -- Variation from UTC in seconds
    ctIsDST :: Bool       -- True if Daylight Saving Time in effect
  }  

data Month  = January | February | March | April | May | June
            | July | August | September | October | November | December

data Day    = Sunday | Monday | Tuesday | Wednesday
            | Thursday | Friday | Saturday

-}

{-
data TimeDiff = TimeDiff
  { tdYear :: Int,
    tdMonth :: Int,
    tdDay :: Int,
    tdHour :: Int,
    tdMin :: Int,
    tdSec :: Int,
    tdPicosec :: Integer}
-}






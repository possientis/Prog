module PodMainGUI where
import PodDownload
import PodDB
import PodTypes
import System.Environment
import Database.HDBC
import Network.Socket(withSocketsDo)

-- GUI Libraries

import Graphics.UI.Gtk hiding (disconnect, add)
import Graphics.UI.Gtk.Builder -- hopefully this wors for Glade

-- Threading

import Control.Concurrent

data GUI = GUI {
  mainWin :: Window,
  mwAddBt :: Button,
  mwUpdateBt :: Button,
  mwDownloadBt :: Button,
  mwFetchBt :: Button,
  mwExitBt :: Button,
  statusWin :: Dialog,
  swOKBt :: Button,
  swCancelBt :: Button,
  swLabel :: Label,
  addWin :: Dialog,
  awOKBt :: Button,
  awCancelBt :: Button,
  awEntry :: Entry}


main :: FilePath -> IO ()
main gladepath = withSocketDo $ handleSqlError $
  do  initGUI  -- initialize GTK+ engine
      -- every so often, we try to run other threads
      timeOutAddFull (yield >> return True)
                     priorityDefaultIdle 100
      -- load the GUI from the Glade file
      gui <- loadGlade gladepath

      -- connect to the database
      dbh <- connect

      -- set up our events
      connectGui gui dbh

      -- run the GTK+ main loop; exit after GUI is done
      mainGUI

      -- disconnect from the database at the end
      disconnect dbh

loadGlade gladepath =
  do  -- Load XML from glade path.
      -- Note: crashes with a runtime error on console if fails!
      Just xml <- xmlNew gladepath
      -- Load main window
      mw <- xmlGetWidget xml castToWindow "mainWindow"

      -- Load all buttons
      [mwAdd, mwUpdate, mwDownload, mwFetch, mwExit, swOK, swCancel,
       auOK, auCancel] <-
        mapM (xmlGetWidget xml castToButton)
        ["addButton", "updateButton", "downloadButton",
         "fetchButton", "exitButton", "okButton", "cancelButton",
         "auOK", "auCancel"]
      sw <- xmlGetWidget xml castToDialog "statusDialog"
      swl <- xmlGetWidget xml castToLabel "statusLabel"
      au <- xmlGetWidget xml castToDialog "addDialog"
      aue <- xmlGetWidget xml castToEntry "auEntry"
      return $ GUI mw mwAdd mwUpdate mwDownload mwFetch mwExit
             sw swOK swCancel swl au auOK auCancel aue

connectGui gui dbh =
  do  -- When the close button is clicked, terminate the GUI loop
      -- by calling GTK mainQuit function
      onDestroy (mainWin gui) mainQuit

      -- Main window buttons
      onClicked (mwAddBt gui) (guiAdd gui dbh)
      onClicked (mwUpdateBt gui) (guiUpdate gui dbh)
      onClicked (mwDownloadBt gui) (guiDownload gui dbh)
      onClicked (mwFetchBt gui) (guiFetch gui dbh)
      onClicked (mwExitBt gui) mainQuit

      -- We leave the status window buttons for later


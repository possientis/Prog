-- HaXml API seems to have changed since book was published
-- Code is currently failing to compile
module PodParser where

import PodTypes
import Text.XML.HaXml
import Text.XML.HaXml.Combinators
import Text.XML.HaXml.Parse
import Text.XML.HaXml.Html.Generate(showattr)
import Data.Char
import Data.List

data PodItem = PodItem { itemtitle :: String, enclosureurl :: String } 
  deriving (Eq, Show, Read)

data Feed = Feed { channeltitle :: String, items :: [PodItem] } 
  deriving (Eq, Show, Read)

{- | Given a podcast and an PodItem, produce an Episode -}
item2ep :: Podcast -> PodItem -> Episode
item2ep pc item =
  Episode { epId = 0,
            epCast = pc,
            epURL = enclosureurl item,
            epDone = False}

{- | Parse the data from a given string, with the given name to use
 - in error messages. -}
parse :: String -> String -> Feed
parse content name =
  Feed {  channeltitle = getTitle doc,
          items = getEnclosures doc}
  where parseResult = xmlParse name (stripUnicodeBOM content)
        doc = getContent parseResult

        getContent :: Document -> Content
        getContent (Document _ _ e _) = CElem e
        {- | Some Unicode documents begin with a binary sequence;
        - strip it off before processing. -}
        stripUnicodeBOM :: String -> String
        stripUnicodeBOM ('\xef':'\xbb':'\xbf':x) = x
        stripUnicodeBOM x = x

{- | Pull out the channel part of the document.
 - Note that HaXml defines CFilter as:
 - > type CFilter = Content -> [Content]
 - -}
channel :: CFilter String
channel = tag "rss" /> tag "channel"

getTitle :: Content String -> String
getTitle doc =
  contentToStringDefault "Untitled Podcast"
    (channel /> tag "title" /> txt $ doc)

getEnclosures :: Content String -> [PodItem]
getEnclosures doc =
  concatMap procPodItem $ getPodItems doc
  where procPodItem :: Content String -> [PodItem]
        procPodItem item = concatMap (procEnclosure title) enclosure
          where title = contentToStringDefault "Untitled Episode"
                          (keep /> tag "title" /> txt $ item)
                enclosure = (keep /> tag "enclosure") item

        getPodItems :: CFilter String
        getPodItems = channel /> tag "item"

        procEnclosure :: String -> Content String -> [PodItem]
        procEnclosure title enclosure =
          map makePodItem (showattr "url" enclosure)
          where makePodItem :: Content String -> PodItem
                makePodItem x = PodItem {itemtitle = title,
                                  enclosureurl = contentToString [x]}


{- | Convert [Content] to a printable String, with a default if the
passed-in [Content] is [], signifying a lack of a match. -}
contentToStringDefault :: String -> [Content String] -> String
contentToStringDefault msg [] = msg
contentToStringDefault _ x = contentToString x


{- | Convert [Content] to a printable string, taking care to unescape it.
 - An implementation without unescaping would simply be:
 - > contentToString = concatMap (show . content)
 - Because HaXml's unescaping works only on Elements, we must make sure that
 - whatever Content we have is wrapped in an Element, then use txt to
 - pull the insides back out. -}

contentToString :: [Content String] -> String
contentToString =
  concatMap procContent
  where procContent x =
          verbatim $ keep /> txt $ CElem (unesc (fakeElem x))

        fakeElem :: Content String-> Element
        fakeElem x = Elem "fake" [] [x]

        unesc :: Element -> Element
        unesc = xmlUnEscape stdXmlEscaper






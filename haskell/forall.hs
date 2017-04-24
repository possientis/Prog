{-# LANGUAGE ExistentialQuantification #-}

data Image
data DisplayRegion

class Widget w where
  render :: DisplayRegion -> w -> Image

data AnyWidget = forall w. Widget w => AnyWidget w

data Text
data Box
data Fill



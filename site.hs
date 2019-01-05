--------------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}

import Data.Monoid (mappend)
import Hakyll
import Text.Pandoc

crunchWithCtx ctx = do
  route   $ setExtension "html"
  compile $ pandocCompiler
            >>= loadAndApplyTemplate "templates/page.html"    ctx
            >>= loadAndApplyTemplate "templates/default.html" ctx 
            >>= relativizeUrls

--------------------------------------------------------------------------------
main :: IO ()
main = hakyll $ do
  match "static/*/*"    $ do route idRoute
                             compile copyFileCompiler
  match (fromList tops) $ crunchWithCtx siteCtx 
  match "lectures/*"    $ crunchWithCtx postCtx 
  match "assignments/*" $ crunchWithCtx postCtx 
  match "templates/*"   $ compile templateCompiler

--------------------------------------------------------------------------------
postCtx :: Context String
postCtx =
    dateField  "date"       "%B %e, %Y"  `mappend`
    -- constField "headerImg"  "Eiffel.jpg" `mappend`
    siteCtx

siteCtx :: Context String
siteCtx =
    constField "baseurl"            "https://ucsd-progsys.github.io/230-wi19-web"     `mappend`
    constField "site_name"          "cse230"                      `mappend`
    constField "site_description"   "UCSD CSE 230"                `mappend`
    constField "site_username"      "Ranjit Jhala"                `mappend`
    constField "twitter_username"   "ranjitjhala"                 `mappend`
    constField "github_username"    "ucsd-progsys/230-wi19-web"   `mappend`
    constField "google_username"    "rjhala@eng.ucsd.edu"         `mappend`
    constField "google_userid"      "u/0/106612421534244742464"   `mappend`
    constField "piazza_classid"     "class/jqk23zupq7a62c"        `mappend`
    defaultContext

tops =
  [ "index.md"
  , "grades.md"
  , "lectures.md"
  , "links.md"
  , "assignments.md"
  , "calendar.md"
  , "contact.md"
  ]

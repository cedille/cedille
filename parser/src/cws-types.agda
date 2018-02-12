module cws-types where

postulate
  string : Set

{-# BUILTIN STRING string #-}

{-# IMPORT CedilleCommentsLexer #-}

posinfo = string

data entity : Set where 
  EntityComment : posinfo → posinfo → entity
  EntityNonws : entity
  EntityWs : posinfo → posinfo → entity
{-# COMPILED_DATA entity CedilleCommentsLexer.Entity CedilleCommentsLexer.EntityComment  CedilleCommentsLexer.EntityNonws CedilleCommentsLexer.EntityWs #-}

data entities : Set where 
  EndEntity : entities
  Entity : entity → entities → entities
{-# COMPILED_DATA entities CedilleCommentsLexer.Entities CedilleCommentsLexer.EndEntity  CedilleCommentsLexer.Entity #-}

data start : Set where 
  File : entities → start
{-# COMPILED_DATA start CedilleCommentsLexer.Start CedilleCommentsLexer.File #-}

postulate
  scanComments  : string → start
  showStart     : start  → string

{-# COMPILED scanComments CedilleCommentsLexer.scanComments #-}
{-# COMPILED showStart    CedilleCommentsLexer.showStart #-}

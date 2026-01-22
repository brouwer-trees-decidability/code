----------------------------------------------------------------------------------------------------
-- Brouwer trees
----------------------------------------------------------------------------------------------------

{-# OPTIONS --cubical --erasure --guardedness #-}

module BrouwerTree.Everything where

{- Definition -}
open import BrouwerTree.Base public

{- Some properties of Brouwer trees -}
open import BrouwerTree.Properties public

{- Characterisation of ≤ for Brouwer trees via a family Code -}
open import BrouwerTree.Code public

{- Some results of using the Code family, e.g. antisymmetry and extensionality -}
open import BrouwerTree.Code.Results public

{- Classifiability -}
open import BrouwerTree.Classifiability public

{- Arithmetic operations -}
open import BrouwerTree.Arithmetic public

{- Properties of arithmetic operations -}
open import BrouwerTree.Arithmetic.Properties public

{- Correctness of arithmetic operations -}
open import BrouwerTree.Arithmetic.Correctness public

{- An alternative definition of Brouwer trees -}
open import BrouwerTree.AlternativeDefinition

{- Decidability and undecidability results -}
open import BrouwerTree.Decidability public
open import BrouwerTree.Decidability.Finite public
open import BrouwerTree.Decidability.Joins public

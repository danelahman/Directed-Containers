module README where

-- Utilities
-- =========

-- standard library for directed containers
open import Utils


-- Basic Category Theory
-- =====================

-- functors, natural transformations
open import Functors

-- comonads, comonad morphisms
open import Comonads


-- Containers
-- ==========

-- containers, container morphisms, interpretation to functors and natural transformations, fully-faithfulness lemmas
open import Containers


-- Directed Containers
-- ===================

-- directed containers,  directed container morphisms
open import DContainers

-- interpretation to comonads and comonad morphisms
open import DContainerExt

-- strict directed containers
open import StrictDirectedContainer

-- coproducts, functions from monoids to strict directed containers
open import DirectedContainerOperations 


-- Directed Containers And Comonads
-- ===============================

-- containers ∩ comonads = directed containers
open import Comonad2DContainer
open import Comonad2DContainerHelper
open import Comonad2DContainerHelper2
open import Comonad2DContainerHelper3

-- containers ∩ comonad morphisms = directed container morphisms
open import ComonadMorph2DContainerMorph
open import ComonadMorph2DContainerMorphHelper

-- fully faithfulness of the interpretation to comonads
open import FullyFaithfulLem1
open import FullyFaithfulLem2

-- lemmas for interpretation to comonads
open import InterpretQuoteLem1
open import InterpretQuoteLem2


-- Examples
-- ========

-- lists as containers
open import Examples.ListContainer

-- different flavours of binary trees as directed containers
open import Examples.BinaryTreeDContainer1
open import Examples.BinaryTreeDContainer2
open import Examples.BinaryTreeDContainer3

-- lists as directed containers
open import Examples.ListDContainer

-- streams as directed containers
open import Examples.StreamDContainer

-- directed container morphisms between lists, streams and trees
open import Examples.Morphisms

-- focussing a container to get a directed container
open import Examples.FocusDContainer
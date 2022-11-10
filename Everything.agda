{-# OPTIONS --guardedness #-}  -- for Test's use of IO

module Everything where

import Show
import HasAlgebra

import Categorical.Object
import Categorical.Equiv
import Categorical.Raw
import Categorical.Laws
import Categorical.Reasoning
import Categorical.Homomorphism
import Categorical.MakeLawful
import Categorical.Subcategory
import Categorical.Comma
import Categorical.Arrow
import Categorical.Free
import Categorical.Product
import Categorical.IdInstances

import Functions
import Equality
import Equality.Homomorphism
import Finite
import StronglyFinite
import Ty
import Primitive
import Routing
import Linearize
import SSA
import Dot

import Samples.Add
import Samples.Add.Properties

import Test

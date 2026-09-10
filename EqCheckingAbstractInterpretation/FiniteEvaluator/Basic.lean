import Mathlib.Data.Finset.Powerset

namespace EqCheckingAbstractInterpretation.FiniteEvaluator

universe u v

/-- Mathematical finite sets, with extensional equality and library support. -/
abbrev FSet (Element : Type u) := Finset Element

/-- Enumerate all Finset subsets of an ordered finite source list. -/
def powerset [DecidableEq Element] (elements : List Element) : List (FSet Element) :=
  elements.foldr (fun element sets => sets ++ sets.map (fun set => insert element set)) [{}]

/-- Enumerate list-valued subsets when their ordering is part of the target syntax. -/
def listPowerset (elements : List Element) : List (List Element) :=
  elements.foldr (fun element sets => sets ++ sets.map (fun set => element :: set)) [[]]

/--
Run an inflationary Boolean fixed-point computation over a finite configuration
space. `contains` may implement an extensional notion of configuration equality.
-/
def saturateStep
    (configs : List Config)
    (contains : Config → List Config → Bool)
    (marks : List Config → Config → Bool)
    (marked : List Config) : List Config :=
  marked ++ configs.filter (fun config => !contains config marked && marks marked config)

def saturateN
    (configs : List Config)
    (contains : Config → List Config → Bool)
    (marks : List Config → Config → Bool) : Nat → List Config
  | 0 => []
  | count + 1 => saturateStep configs contains marks (saturateN configs contains marks count)

def saturate
    (configs : List Config)
    (contains : Config → List Config → Bool)
    (marks : List Config → Config → Bool) : List Config :=
  saturateN configs contains marks configs.length

end EqCheckingAbstractInterpretation.FiniteEvaluator

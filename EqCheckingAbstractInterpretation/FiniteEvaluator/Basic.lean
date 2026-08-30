namespace EqCheckingAbstractInterpretation.FiniteEvaluator

universe u v

/-- Finite sets represented as duplicate-free lists. -/
abbrev Set (Element : Type u) := List Element

/-- Boolean membership in a finite set. -/
def mem [BEq Element] (element : Element) : Set Element → Bool
  | [] => false
  | candidate :: elements => element == candidate || mem element elements

/-- Insert an element if it is not already present. -/
def insert [BEq Element] (element : Element) (elements : Set Element) : Set Element :=
  if mem element elements then elements else element :: elements

/-- Union of finite sets. -/
def union [BEq Element] (left right : Set Element) : Set Element :=
  left.foldl (fun elements element => insert element elements) right

def subset [BEq Element] (left right : Set Element) : Bool :=
  left.all (fun element => mem element right)

def setEq [BEq Element] (left right : Set Element) : Bool :=
  subset left right && subset right left

/-- Enumerate the powerset of a finite list. -/
def powerset (elements : List Element) : List (Set Element) :=
  elements.foldr (fun element sets => sets ++ sets.map (fun set => element :: set)) [[]]

/--
Run an inflationary Boolean fixed-point computation over a finite configuration
space. `contains` may implement an extensional notion of configuration equality.
-/
def saturate
    (configs : List Config)
    (contains : Config → List Config → Bool)
    (marks : List Config → Config → Bool) : List Config :=
  (List.replicate configs.length ()).foldl
    (fun marked _ =>
      marked ++ configs.filter (fun config => !contains config marked && marks marked config))
    []

end EqCheckingAbstractInterpretation.FiniteEvaluator

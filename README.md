# agda-math

An alternative construction of basic algebraic structures other than the Agda standard library

## Motivation

- Instead of parameterizing the structures on certain carriers by equivalence relations, as the Agda standard library does, in this repository are the structures parameterized by not and not only equivalence relations, but an equiality relation and also predicates on the carriers.

- The motivation came when I tried to define Field using the standard library.
  - When defining Field, it is unavoidable to deal with substructures.
  - When we wrap the subtype information into the carriers, we do get rid of defining nor proving closures.
  - However, we will have to explicitly differenciate between the elements of a structure and those of the substructures, with different types and names.

- In the alternative here, every structure is defined over a carrying type, with an equivalence relation and a predicate.
  - Elements under the same carrier share their names , while having different properties with the equivalence and the predicate, which indecates the substructures where they could belong.
  - This simplifies the notations when operating on the elements.
  - However, the subtype information hides into the proof, as the closure properties.

- Basic reasoning for preorders, equivalences, and ordered sets on such definition for structures are also provided.


## Content
- Basic
  - Logic : where basic logical tools are defined or import publiclym which depends on the Agda standart library
  - Properties : basic properties when defining algebraic structures
  - Subtype : basic operations for predicates
  - Setoid (Set) : a type equipped with a predicate and an equality relation
  - Equality : where the proprositional equality is redifined
  - Morphism : basic properties of functions
- Reasoning : alternative reasoning tools under a predicate
- Algebra
  - Semigroup, Monoid, Group : Sets equipped with a binary operation
  - Ring, DivisionRing, Field : Sets equipped with two binary operations
  - Linear.VectorSpace : an AbelianGroup with a Field acting on it
- Analysis
  - OrderedSet : a Set equipped with a total order
  - OrderedField : a Field equipped with a total order. Limits, supremum, and completeness are defined here.
  - CompleteOrderedField : the Real number
- Number : the construction of the number system
  - Natural
  - Cardinality : defines countability, infiniteness, and finiteness

## Dependences on the Agda standard Library
  - Reasoning.Preorder : Relation.Binary.PropositionalEquality
  - Basic.Equality : Relation.Binary.PropositionalEquality
  - Badic.Logic : Data.Sum, Data.Product, Data.Empty, Relation.Nullary, Function
  - Numebr.Natural : Data.Nat

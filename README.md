# algebraic-structures
An alternative construction other than the standard Agda library

- Instead of parameterizing the structures on certain carriers by equivalence relations, as the standard Agda library does, in this repository are the structures parameterized by not only equivalence relations, but also predicates on the carriers.

- The motivation came when I tried to define Field using the standard library.
  - When defining Field, it is unavoidable to deal with substructures.
  - When we wrap the subtype information into the carriers, we do get rid of defining nor proving closures.
  - However, we will have to explicitly differenciate between the elements of a structure and those of the substructures, with different types and names.

- In the alternative here, every structure is defined over a carrying type, with an equivalence relation and a predicate.
  - elements under the same carrier share their names , while having different properties with the equivalence and the predicate, which indecates the substructures where they could belong.
  - This simplifies the notations when operating on the elements.
  - However, the subtype information hides into the proof, as the closure properties.

- Basic reasoning for preorder and equivalence on such definition for structures are also provided.

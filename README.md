# algebraic-structures
An alternative construction other than the standard Agda library

- Instead of parameterizing the structures on certain carriers by equivalence relations, as the standard Agda library does, in this repository are the structures parameterized by not only equivalence relations, but also predicates on the carriers.

- The motivation came when I tried to define Field using the standard library.
  - When defining Field, it is unavoidable to deal with substructures.
  - When we wrap the subset information into the carries, we do get rid of defining nor proving closures.
  - However, we will have to explicitly differenciate between the elements of the structure and those of the substructures, with different names.

- The alternative way here, elements under the same universe share their names , while having different properties, which indecates the substructures where they belong.

- Basic reasoning for preorder and equivalence on such definition for structures are also provided.

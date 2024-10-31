import VersoBlog

open Verso Genre Blog

#doc (Page) "Metatheorems and how to formalize them" =>

# Equational theories project: metatheorems and how to formalize them

Hernán Ibarra Mejia & Anand Rao Tadipatri


## Roadmap

1. What is the Equational Theories project?

2. Metatheorems

3. Metatheorems in Lean


## What is the Equational Theories project?

- Start

- Aims

- Many contributions

## Metatheorems

### Balanced equations

- Example: `x ⋆ ((x ⋆ y ) ⋆ z ) = y ⋆ ( x ⋆ (z ⋆ x ))`

- Metatheorem 1

- Proofs: syntactic vs. semantic.

### Balanced equations modulo n

- Example for n = 2: `(x ⋆ y ) ⋆ x = ((z * x) * (y ⋆ (x ⋆ (y ⋆ y)))) * z`

- Metatheorem 2

- Skip proof


### Equations which agree on the leftmost variable.

- Pattern: `x ⋆ (rubbish) = x ⋆ (other rubbish)`

- Guess metatheorem 3

- Syntactic proof (semantic proof later).

### The metametatheorem

- Category theory disclaimer

- Statement of the metametatheorem

#### Example: associativity

- Guess metatheorem

- Semantic proof: free monoid

#### Example: `x ⋆ y = x`

- Guess metatheorem

- Semantic proof

### Expanding the language: conjunction

- Example: associativity and commutativity

- Guess metatheorem

- Semantic proof

### Expanding the language: constants

- Example: (assoc) and (comm) and (unity) and (`x^n = 1`)

- Guess metatheorem

- Semantic proof

# Cedille Parser [![Build Status](https://travis-ci.org/ernius/cedilleparser.svg?branch=master)](https://travis-ci.org/ernius/cedilleparser)

Dependant typed programming language (called Cedille) parser developed in Haskell.

## Project details

### Source code:
 * Lexer  [src/CedilleLexer.x](src/CedilleLexer.x)
 * Parser [src/CedilleParser.y](src/CedilleParser.y)
 * Comments Lexer  [src/CedilleCommentsLexer.x](src/CedilleCommentsLexer.x)

Some working examples tested in [test](test) project sub folder.

Haskell parser exported to Agda. Haskell AST datatype ([src/CedilleTypes.hs](src/CedilleTypes.agda)) export to Agda AST datatype ([src/cedille-types.agda](src/cedille-types.agda)), and minimal example calling the Haskell's parser from Agda ([src/test.agda](src/test.agda)).

### Makefile/Cabal commands:
 * Build: `cabal build`.
 * Running tests: `cabal test` or `make tests`.
 * Running tests in debug mode: `make tests-debug`.
 * Rebuild parser info file: `make info`.
 * Running agda test: `make agda-test`.

## Must review:

* Reserved words (tokens): 

Description	                 | Reserved Words
-----------------------------|----------
module system				 | import, module, as
projections					 | .0 .1 ... .9
general symbols				 | . , _ : · ≃ > - ◂ = ∀ ● ↑ ➾ ➔ ☆ ★ ( ) { } [ ] 
lifting symbols				 | Π↑ ➔↑
epsilon						 | ε ε- εl εl- εr εr-
theta						 | θ θ+ θ<
rho							 | ρ ρ+
other greek letters			 | β ι Λ λ χ φ Π ς
starting with kappa vars.	 | 𝒌*variable*
span symbols				 | {^ ^}
multi-line comments			 | {- -}
in-line comments			 | --
   
* Syntax Changes: 

Description     | Previous Rule                                           | Updated Rule
----------------|---------------------------------------------------------|----------------
Equality Type   | `Term '≃' Term`                                        | `'{' Term '≃' Term '}'`
Lifting Type    | `'Π' Bvar ':' Type '.' LiftingType`                  | `'Π↑' Bvar ':' Type '.' LiftingType`
Lifting Type    | `LliftingType  '➔' LiftingType`                      | `LliftingType  '➔↑' LiftingType`
Lifting Type    | `Type          '➔' LiftingType`                      | `Type          '➔↑' LiftingType`
Let/in          | `'let' DefTermOrType 'in' Term`                      | `'[' DefTermOrType ']' '-' Term`


* Syntax Updates.

	* Added phi rule: `Lterm -> 'φ' Lterm '-' Lterm '{' Term '}'`
	
	* Changed pair rule: `Pterm -> '[' Term ',' Term ']'` (before `Pterm -> '[' Term ',' Term OptTerm ']'`)
	

* Another grammar change:

	* Allowed greek letters in variables.

	* Changed `Term -> '{' Term '≃' Term '}'` to `AType -> '{' Term '≃' Term '}'`, so now the following term:

```
({ x ≃ x' }) ➔ Q x' ➔ X
```

can be written as:


```
{ x ≃ x' } ➔ Q x' ➔ X
```

and
```
Lte ◂ Nat ➔ Nat ➔ ★ = λ n : Nat . λ m : Nat . Sum · (Lt n m) · ( {n ≃ m} ) .
``

can be written as:

```
Lte ◂ Nat ➔ Nat ➔ ★ = λ n : Nat . λ m : Nat . Sum · (Lt n m) · {n ≃ m}  .
```

However, in this last example emacs navegation gets wrong, we should add position information to TpEq constructor, in the AST.

* Added comments scanner.

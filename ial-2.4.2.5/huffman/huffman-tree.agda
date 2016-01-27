module huffman-tree where

open import lib

data huffman-tree : Set where
  ht-leaf : string → ℕ → huffman-tree
  ht-node : ℕ → huffman-tree → huffman-tree → huffman-tree

-- get the frequency out of a Huffman tree
ht-frequency : huffman-tree → ℕ
ht-frequency (ht-leaf _ f) = f
ht-frequency (ht-node f _ _) = f

-- lower frequency nodes are considered smaller 
ht-compare : huffman-tree → huffman-tree → 𝔹
ht-compare h1 h2 = (ht-frequency h1) < (ht-frequency h2)

{- return (just s) if Huffman tree is an ht-leaf with string s;
   otherwise, return nothing (this is a constructor for the maybe type -- see maybe.agda in the IAL) -}
ht-string : huffman-tree → maybe string
ht-string (ht-leaf s f) = just s
ht-string _ = nothing

-- several helper functions for ht-to-string (defined at the bottom)
private 
  -- helper function for ht-to-stringh
  ht-declare-node : huffman-tree → ℕ → string × string
  ht-declare-node h n = 
    let cur = "n" ^ (ℕ-to-string n) in
      cur , (cur ^ " [label = \"" ^ (help (ht-string h)) ^ (ℕ-to-string (ht-frequency h)) ^ "\"];\n")
    where help : maybe string → string
          help (just s) = s ^ " , "
          help nothing = ""

  -- helper function for ht-to-stringh
  ht-attach : maybe string → string → string
  ht-attach nothing _ = ""
  ht-attach (just c) c' = c ^ " -> " ^ c' ^ ";\n"

  ht-to-stringh : huffman-tree → ℕ → maybe string → ℕ × string
  ht-to-stringh h n prev with ht-declare-node h n 
  ht-to-stringh (ht-leaf _ _) n prev | c , s = suc n , (ht-attach prev c) ^ s 
  ht-to-stringh (ht-node _ h1 h2) n prev | c , s with ht-to-stringh h1 (suc n) (just c) 
  ht-to-stringh (ht-node _ h1 h2) _ prev | c , s | n , s1 with ht-to-stringh h2 n (just c) 
  ht-to-stringh (ht-node _ h1 h2) _ prev | c , s | _ , s1 | n , s2 = n , (ht-attach prev c) ^ s ^ s1 ^ s2

{- turn a Huffman tree into a string in Graphviz format 
   (you can render the output .gv file at http://sandbox.kidstrythisathome.com/erdos/) -}
ht-to-string : huffman-tree → string
ht-to-string h with ht-to-stringh h 0 nothing
ht-to-string h | _ , s = "digraph h {\nnode [shape = plaintext];\n" ^ s ^ "}"

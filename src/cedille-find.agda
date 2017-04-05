module cedille-find where

open import lib

open import cedille-types

occurrence-tuple = var × posinfo × string
occurrences-table = trie (𝕃 occurrence-tuple)


--------------------------
-- helper functions
--------------------------

occurrence-tuple-to-JSON : occurrence-tuple → string
occurrence-tuple-to-JSON (str , pos-info , filename) = "{\"defn\":\"" ^ str ^ "\",\"pos-info\":" ^ pos-info ^ ",\"filename\":\"" ^ filename ^ "\"}"

find-symbols-to-JSON-h : 𝕃 occurrence-tuple → string
find-symbols-to-JSON-h [] = ""
find-symbols-to-JSON-h (x :: []) = (occurrence-tuple-to-JSON x)
find-symbols-to-JSON-h (x :: xs) = (occurrence-tuple-to-JSON x) ^ "," ^ find-symbols-to-JSON-h xs

find-symbols-to-JSON : var → 𝕃 occurrence-tuple → string
find-symbols-to-JSON symb l = "{\"find\":{\"symbol\":\"" ^ symb ^ "\",\"occurrences\":[" ^ (find-symbols-to-JSON-h l) ^ "]}}"

-- updates the value list in the symbol map provided that the key symbol is not being shadowed
trie-append-or-create : occurrences-table → stringset → var → var → string → posinfo → occurrences-table
trie-append-or-create symb-map shadow key defn pos-info filename with (stringset-contains shadow key)
...                                                    | tt = symb-map
...                                                    | ff with (trie-lookup symb-map key)
...                                                         | nothing = trie-insert symb-map key ((defn , pos-info , filename) :: [])
...                                                         | just list = trie-insert symb-map key ((defn , pos-info , filename) :: list)

--------------------------
-- find declarations
--------------------------
find-symbols-cmd : cmd → string → occurrences-table → stringset → occurrences-table

find-symbols-t : Set → Set
find-symbols-t X = X → var → string → occurrences-table → stringset → occurrences-table

find-symbols-checkKind : find-symbols-t checkKind
find-symbols-kind : find-symbols-t kind
find-symbols-liftingType : find-symbols-t liftingType
find-symbols-lterms : find-symbols-t lterms
find-symbols-maybeCheckType : find-symbols-t maybeCheckType
find-symbols-optType : find-symbols-t optType
find-symbols-term : find-symbols-t term
find-symbols-optTerm : find-symbols-t optTerm
find-symbols-tk : find-symbols-t tk
find-symbols-type : find-symbols-t type


--------------------------
-- definitions
--------------------------
find-symbols-checkKind (Kind k) defn filename symb-map shadow = find-symbols-kind k defn filename symb-map shadow

find-symbols-cmd (DefKind _ kvar _ k _) filename symb-map shadow = find-symbols-kind k kvar filename symb-map shadow
find-symbols-cmd (DefTerm _ var mcT t _ _) filename symb-map shadow = find-symbols-maybeCheckType mcT var filename (find-symbols-term t var filename symb-map shadow) shadow
find-symbols-cmd (DefType _ var cK T _ _) filename symb-map shadow = find-symbols-checkKind cK var filename (find-symbols-type T var filename symb-map shadow) shadow
find-symbols-cmd _ _ symb-map _ = symb-map

find-symbols-kind (KndArrow k1 k2) defn filename symb-map shadow = find-symbols-kind k1 defn filename (find-symbols-kind k2 defn filename symb-map shadow) shadow
find-symbols-kind (KndParens _ k _) defn filename symb-map shadow = find-symbols-kind k defn filename symb-map shadow
find-symbols-kind (KndPi _ _ var tk k) defn filename symb-map shadow = find-symbols-tk tk defn filename (find-symbols-kind k defn filename symb-map (stringset-insert shadow var)) shadow
find-symbols-kind (KndTpArrow T k) defn filename symb-map shadow = find-symbols-type T defn filename (find-symbols-kind k defn filename symb-map shadow) shadow
find-symbols-kind (KndVar pos-info kvar) defn filename symb-map shadow = trie-append-or-create symb-map shadow kvar defn pos-info filename
find-symbols-kind _ _ _ symb-map _ = symb-map

find-symbols-liftingType (LiftArrow lT1 lT2) defn filename symb-map shadow = find-symbols-liftingType lT1 defn filename (find-symbols-liftingType lT2 defn filename symb-map shadow) shadow
find-symbols-liftingType (LiftParens _ lT _) defn filename symb-map shadow = find-symbols-liftingType lT defn filename symb-map shadow
find-symbols-liftingType (LiftPi _ var T lT) defn filename symb-map shadow = find-symbols-type T defn filename (find-symbols-liftingType lT defn filename symb-map (stringset-insert shadow var)) shadow
find-symbols-liftingType (LiftTpArrow T lT) defn filename symb-map shadow = find-symbols-type T defn filename (find-symbols-liftingType lT defn filename symb-map shadow) shadow
find-symbols-liftingType _ _ _ symb-map _ = symb-map

find-symbols-lterms (LtermsCons _ t lt) defn filename symb-map shadow = find-symbols-term t defn filename (find-symbols-lterms lt defn filename symb-map shadow) shadow
find-symbols-lterms _ _ _ symb-map _ = symb-map

find-symbols-maybeCheckType (Type T) defn filename symb-map shadow = find-symbols-type T defn filename symb-map shadow
find-symbols-maybeCheckType _ _ _ symb-map _ = symb-map

find-symbols-optType (SomeType T) defn filename symb-map shadow = find-symbols-type T defn filename symb-map shadow
find-symbols-optType _ _ _ symb-map _ = symb-map

find-symbols-optTerm (SomeTerm t _) defn filename symb-map shadow = find-symbols-term t defn filename symb-map shadow
find-symbols-optTerm _ _ _ symb-map _ = symb-map

find-symbols-term (App t1 _ t2) defn filename symb-map shadow = find-symbols-term t1 defn filename (find-symbols-term t2 defn filename symb-map shadow) shadow
find-symbols-term (AppTp t T) defn filename symb-map shadow = find-symbols-term t defn filename (find-symbols-type T defn filename symb-map shadow) shadow
find-symbols-term (Chi _ _ t) defn filename symb-map shadow = find-symbols-term t defn filename symb-map shadow
find-symbols-term (Delta _ t) defn filename symb-map shadow = find-symbols-term t defn filename symb-map shadow
find-symbols-term (Epsilon _ _ _ t) defn filename symb-map shadow = find-symbols-term t defn filename symb-map shadow
--find-symbols-term (Fold _ _ T t) defn filename symb-map shadow = find-symbols-type T defn filename (find-symbols-term t defn filename symb-map shadow) shadow
-- treated as a new top global def
find-symbols-term (InlineDef _ _ var t _) defn filename symb-map shadow = find-symbols-term t var filename symb-map shadow
find-symbols-term (IotaPair _ t1 t2 ot _) defn filename symb-map shadow = find-symbols-term t1 defn filename (find-symbols-term t2 defn filename (find-symbols-optTerm ot defn filename symb-map shadow) shadow) shadow
find-symbols-term (IotaProj t _ _) defn filename symb-map shadow = find-symbols-term t defn filename symb-map shadow
find-symbols-term (Lam _ _ _ var _ t) defn filename symb-map shadow = find-symbols-term t defn filename symb-map (stringset-insert shadow var)
find-symbols-term (Parens _ t _) defn filename symb-map shadow = find-symbols-term t defn filename symb-map shadow
find-symbols-term (PiInj _ _ t) defn filename symb-map shadow = find-symbols-term t defn filename symb-map shadow
find-symbols-term (Rho _ _ t1 t2) defn filename symb-map shadow = find-symbols-term t1 defn filename (find-symbols-term t2 defn filename symb-map shadow) shadow
find-symbols-term (Sigma _ t) defn filename symb-map shadow = find-symbols-term t defn filename symb-map shadow
find-symbols-term (Theta _ _ t lt) defn filename symb-map shadow = find-symbols-term t defn filename (find-symbols-lterms lt defn filename symb-map shadow) shadow
find-symbols-term (Unfold _ t) defn filename symb-map shadow = find-symbols-term t defn filename symb-map shadow
find-symbols-term (Var pos-info var) defn filename symb-map shadow = trie-append-or-create symb-map shadow var defn pos-info filename
find-symbols-term _ _ _ symb-map _ = symb-map

find-symbols-tk (Tkk k) defn filename symb-map shadow = find-symbols-kind k defn filename symb-map shadow
find-symbols-tk (Tkt T) defn filename symb-map shadow = find-symbols-type T defn filename symb-map shadow

find-symbols-type (Abs _ _ _ var tk T) defn filename symb-map shadow = find-symbols-tk tk defn filename (find-symbols-type T defn filename symb-map (stringset-insert shadow var)) shadow
find-symbols-type (Iota _ _ var oT T) defn filename symb-map shadow = find-symbols-optType oT defn filename (find-symbols-type T defn filename symb-map (stringset-insert shadow var)) shadow
find-symbols-type (Lft _ _ var t lT) defn filename symb-map shadow = find-symbols-term t defn filename (find-symbols-liftingType lT defn filename symb-map (stringset-insert shadow var)) shadow
find-symbols-type (Mu _ _ var k T) defn filename symb-map shadow = find-symbols-kind k defn filename (find-symbols-type T defn filename symb-map (stringset-insert shadow var)) shadow
find-symbols-type (NoSpans T _) defn filename symb-map shadow = find-symbols-type T defn filename symb-map shadow
find-symbols-type (TpApp T1 T2) defn filename symb-map shadow = find-symbols-type T1 defn filename (find-symbols-type T2 defn filename symb-map shadow) shadow
find-symbols-type (TpAppt T t) defn filename symb-map shadow = find-symbols-type T defn filename (find-symbols-term t defn filename symb-map shadow) shadow
find-symbols-type (TpArrow T1 _ T2) defn filename symb-map shadow = find-symbols-type T1 defn filename (find-symbols-type T2 defn filename symb-map shadow) shadow
find-symbols-type (TpEq t1 t2) defn filename symb-map shadow = find-symbols-term t1 defn filename (find-symbols-term t2 defn filename symb-map shadow) shadow
find-symbols-type (TpLambda _ _ var tk T) defn filename symb-map shadow = find-symbols-tk tk defn filename (find-symbols-type T defn filename symb-map (stringset-insert shadow var)) shadow
find-symbols-type (TpParens _ T _) defn filename symb-map shadow = find-symbols-type T defn filename symb-map shadow
find-symbols-type (TpVar pos-info var) defn filename symb-map shadow = trie-append-or-create symb-map shadow var defn pos-info filename
find-symbols-type (TpHole pos-info) defn filename symb-map shadow = trie-append-or-create symb-map shadow "hole" defn pos-info filename
--ACG: Not sure this works

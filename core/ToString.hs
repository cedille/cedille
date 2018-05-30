module ToString where
import Types

instance Show PureTerm where
  show = pureTermToString False
instance Show Term where
  show = termToString False
instance ShowBool tm => Show (PrimType tm) where
  show = typeToString False
instance ShowBool tm => Show (PrimKind tm) where
  show = kindToString
instance ShowBool tm => Show (PrimTpKd tm) where
  show = tpKdToString

class Show a => ShowBool a where
  showBool :: Bool -> a -> String
instance ShowBool PureTerm where
  showBool = pureTermToString
instance ShowBool Term where
  showBool = termToString


parensIf True s = "(" ++ s ++ ")"
parensIf False s = s

pureTermIsntApp (PureApp _ _) = False
pureTermIsntApp _ = True

termIsntApp (TmAppTm _ _) = False
termIsntApp (TmAppTp _ _) = False
termIsntApp (TmAppTmE _ _) = False
termIsntApp _ = True

typeIsntApp (TpAppTp _ _) = False
typeIsntApp (TpAppTm _ _) = False
typeIsntApp _ = True


pureTermToString b (PureVar v) = v
pureTermToString b (PureLambda v tm) = parensIf b $ "λ " ++ v ++ " . " ++ show tm
pureTermToString b (PureApp tm tm') = parensIf b $ pureTermToString (pureTermIsntApp tm) tm ++ " " ++ pureTermToString True tm'

termToString b (TmVar v) = v
termToString b (TmLambda v tp tm) = parensIf b $ "λ " ++ v ++ " : " ++ show tp ++ " . " ++ show tm
termToString b (TmLambdaE v tk tm) = parensIf b $ "Λ " ++ v ++ " : " ++ show tk ++ " . " ++ show tm
termToString b (TmAppTm tm tm') = parensIf b $ termToString (termIsntApp tm) tm ++ " " ++ termToString True tm'
termToString b (TmAppTmE tm tm') = parensIf b $ termToString (termIsntApp tm) tm ++ " - " ++ termToString True tm'
termToString b (TmAppTp tm tp) = parensIf b $ termToString (termIsntApp tm) tm ++ " · " ++ typeToString True tp
termToString b (TmIota tm tm' v tp) = "[ " ++ show tm ++ ", " ++ show tm' ++ " @ " ++ v ++ " . " ++ show tp ++ " ]"
termToString b (IotaProj1 tm) = termToString True tm ++ " . 1"
termToString b (IotaProj2 tm) = termToString True tm ++ " . 2"
termToString b (Beta pt pt') = "β < " ++ pureTermToString True pt ++ " > { " ++ show pt' ++ " }"
termToString b (Sigma tm) = "ς " ++ termToString True tm
termToString b (Delta tp tm) = "δ " ++ typeToString True tp ++ " - " ++ termToString True tm
termToString b (Rho tm v tp tm') = "ρ " ++ termToString True tm ++ " @ " ++ v ++ " " ++ typeToString True tp ++ " - " ++ show tm'
termToString b (Phi tm tm' tm'') = "φ " ++ termToString True tm ++ " - " ++ termToString True tm' ++ " { " ++ show tm'' ++ " }"

typeToString b (TpVar v) = v
typeToString b (TpLambda v tk tp) = parensIf b $ "λ " ++ v ++ " : " ++ show tk ++ " . " ++ show tp
typeToString b (TpAll v tk tp) = parensIf b $ "∀ " ++ v ++ " : " ++ show tk ++ " . " ++ show tp
typeToString b (TpPi v tp tp') = parensIf b $ "Π " ++ v ++ " : " ++ show tp ++ " . " ++ show tp'
typeToString b (TpAppTp tp tp') = parensIf b $ typeToString (typeIsntApp tp) tp ++ " · " ++ typeToString True tp'
typeToString b (TpAppTm tp tm) = parensIf b $ typeToString (typeIsntApp tp) tp ++ " " ++ showBool True tm
typeToString b (TpIota v tp tp') = parensIf True $ "ι " ++ v ++ " : " ++ show tp ++ " . " ++ show tp'
typeToString b (TpEq tm tm') = "{ " ++ show tm ++ " ≃ " ++ show tm' ++ " }"

kindToString Star = "★"
kindToString (KdPi v tk kd) = "Π " ++ v ++ " : " ++ show tk ++ " . " ++ show kd

tpKdToString (TpKdTp tp) = show tp
tpKdToString (TpKdKd kd) = show kd

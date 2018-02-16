{-# LANGUAGE RankNTypes #-}

import Data.List (find)

data Term
  = Typ
  | Var String
  | App Term Term
  | Lam String Term Term
  | All String Term Term
  | Ann Term Term Term
  deriving (Eq, Show)

valOf, norOf, typOf :: Term -> Term
valOf (Ann val _ _) = val
norOf (Ann _ nor _) = nor
typOf (Ann _ _ typ) = typ

toString :: Term -> String
toString Typ               = "*"
toString (Var nam)         = nam
toString (App fun arg)     = "$" ++ toString fun ++ " " ++ toString arg
toString (Lam nam typ bod) = "λ" ++ nam ++ " " ++ toString typ ++ " " ++ toString bod
toString (All nam typ bod) = "∀" ++ nam ++ " " ++ toString typ ++ " " ++ toString bod
toString (Ann val nor typ) = "[" ++ toString val ++ " ~> " ++ toString nor ++ " : " ++ toString typ ++ "]"

fromString :: String -> Term
fromString = fst . parseTerm where
  parseName :: String -> (String, String)
  parseName ""          = ("", "")
  parseName (' ' : src) = ("", src)
  parseName (chr : src) = let
    (nam, src') = parseName src
    in (chr : nam, src')
  parseTerm :: String -> (Term, String)
  parseTerm (' ' : src) = parseTerm src
  parseTerm ('*' : src) = (Typ, src)
  parseTerm ('λ' : src) = let
    (nam, src0) = parseName src
    (typ, src1) = parseTerm src0
    (bod, src2) = parseTerm src1
    in (Lam nam typ bod, src2)
  parseTerm ('∀' : src) = let
    (nam, src0) = parseName src
    (typ, src1) = parseTerm src0
    (bod, src2) = parseTerm src1
    in (All nam typ bod, src2)
  parseTerm ('$' : src) = let
    (fun, src0) = parseTerm src
    (arg, src1) = parseTerm src0
    in (App fun arg, src1)
  parseTerm src = let
    (nam, src') = parseName src
    in (Var nam, src')

clean :: Term -> Term
clean Typ               = Typ
clean (Var nam)         = Var nam
clean (App fun arg)     = App (clean fun) (clean arg)
clean (Lam nam typ bod) = Lam nam (clean typ) (clean bod)
clean (All nam typ bod) = All nam (clean typ) (clean bod)
clean (Ann val nor typ) = clean nor

data HTerm
  = HTyp
  | HVar String
  | HApp HTerm HTerm
  | HLam String HTerm (HTerm -> HTerm)
  | HAll String HTerm (HTerm -> HTerm)
  | HAnn HTerm HTerm HTerm

-- Recursivelly annotate every constructor of a term with its type and normal.
annotate :: Term -> Term
annotate = quote . unquote where
  valOf (HAnn val _ _) = val
  norOf (HAnn _ nor _) = nor
  typOf (HAnn _ _ typ) = typ

  quote :: HTerm -> Term
  quote = go 0 where
    go :: Int -> HTerm -> Term
    go d HTyp = Typ
    go d (HVar nam) = Var nam
    go d (HApp fun arg) = App (go d fun) (go d arg)
    go d (HLam nam typ bod) = let n = nam++"_"++show d in Lam n (go d typ) (go (d+1) (bod (HVar n)))
    go d (HAll nam typ bod) = let n = nam++"_"++show d in All n (go d typ) (go (d+1) (bod (HVar n)))
    go d (HAnn val nor typ) = Ann (go d val) (go d nor) (go d typ)

  unquote :: Term -> HTerm
  unquote = go [] where
    go ctx Typ = HAnn HTyp HTyp HTyp
    go ctx (Var nam) = case find ((nam==).fst) ctx of
      Just (nam,(val,typ)) -> HAnn (HVar nam) val typ
      Nothing              -> HAnn (HVar nam) (HVar nam) (HVar nam)
    go ctx (App fun arg) = let
      fun' = go ctx fun
      arg' = go ctx arg
      resVal = HApp fun' arg'
      resNor = case norOf fun' of
        (HLam nam typ bod) -> bod (norOf arg')
        otherwise          -> HApp (norOf fun') (norOf arg')
      resTyp = case typOf fun' of
        (HAll nam typ bod) -> bod (norOf arg')
        otherwise          -> HApp (norOf fun') (norOf arg')
      in HAnn resVal resNor resTyp
    go ctx (Lam nam typ bod) = let
      typ' = go ctx typ
      bod' = \ val -> go ((nam,(val,norOf typ')) : ctx) bod
      resVal = HLam nam typ' bod'
      resNor = HLam nam (norOf typ') (\val -> norOf (bod' val))
      resTyp = HAll nam (norOf typ') (\val -> typOf (bod' val))
      in HAnn resVal resNor resTyp
    go ctx (All nam typ bod) = let
      typ' = go ctx typ
      typType = typOf typ'
      bod' = \ val -> go ((nam,(val,norOf typ')) : ctx) bod
      resVal = HAll nam typ' bod'
      resNor = HAll nam (norOf typ') (\val -> norOf (bod' val))
      resTyp = HTyp
      in HAnn resVal resNor resTyp
    go ctx (Ann val nor typ) = go ctx val

checks :: Term -> Bool
checks (App (Ann fun _ funTyp) (Ann arg _ argTyp))
  =  checks fun
  && checks arg
  && case funTyp of
    (All nam typ bod) -> typ == argTyp
    otherwise         -> False
checks (All nam (Ann typ _ typTyp) (Ann bod _ bodTyp))
  =  checks typ
  && checks bod
  && case (typTyp, bodTyp) of
    (Typ,Typ) -> True
    otherwise -> False
checks Typ = True
checks (Var nam) = True
checks (App fun arg) = checks fun && checks arg
checks (Lam nam typ bod) = checks typ && checks bod
checks (All nam typ bod) = checks typ && checks bod
checks (Ann val nor typ) = checks val

main :: IO ()
main = do
  let nat = "∀P * ∀Z P ∀S ∀p P P P"
  let cZ  = "λP * λZ P λS ∀p P P Z"
  let cS  = "λn "++nat++" λP * λZ P λS ∀p P P $S $$$n P Z S"
  let foo = "$"++cS++" $"++cS++" $"++cS++" "++cZ
  putStrLn . show . checks . annotate . fromString    $ foo
  putStrLn . toString . typOf . annotate . fromString $ foo
  putStrLn . toString . norOf . annotate . fromString $ foo

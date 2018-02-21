module Core where

-- Cedille Core (Aaron's Type Theory)
--
--   Asc   Nam   Hex   Desc                                                 
-- ,-----,-----,-----,------------------------------------------------------,
-- | *   | Typ | 0   | type of types                                        |
-- | +   | Kin | 1   | type of type of types                                |
-- |     | Var | 2   | variable                                             |
-- | @   | All | 3   | forall                                               |
-- | #   | Lam | 4   | lambda                                               |
-- | $   | App | 5   | application                                          |
-- | /   | Let | 6   | local definition                                     |
-- | &   | Dep | 7   | dependent intersection theorem                       |
-- | ^   | Sec | 8   | dependent intersection proof                         |
-- | <   | Fst | 9   | first element of dependent intersection              |
-- | >   | Snd | A   | second element of dependent intersection             |
-- | =   | Eql | B   | equality (t == t') theorem                           |
-- | :   | Rfl | C   | equality (t == t') proof                             |
-- | ~   | Sym | D   | symmetry of equality (t == t' implies t' == t)       |
-- | !   | Cst | E   | if (t == t') and (t' : T'), cast (t : T) to (t : T') |
-- | %   | Rwt | F   | if (t == t'), cast (p : P[t/x]) to (p : P[t'/x])     |
-- '-----'-----'-----'------------------------------------------------------'

-- TODO: get rid of this small import
import Data.List (find)

-- Primitive constructors
data Prim r b
  = Typ
  | Kin
  | Var String
  | All Bool String r (b -> r)
  | Lam Bool String r (b -> r)
  | App Bool r r
  | Let String r (b -> r)
  | Dep String r (b -> r)
  | Sec String (b -> r) r r
  | Fst r
  | Snd r
  | Eql r r
  | Rfl r r
  | Sym r
  | Cst r r r
  | Rwt String r (b -> r) r
  | Err

-- Terms are layers of primitive constructors
newtype Term
  = Term (Prim Term Term)

-- Anns are terms with type, normal-form and context annotations on each constructor
data Ann
  = Ann {
    valOf :: Prim Ann Term,
    norOf :: Term,
    typOf :: Term
  }

-- Converts an ASCII String to a Term
fromString :: String -> Term
fromString src = snd (parseTerm src) [] where
  parseTerm :: String -> (String, [(String,Term)] -> Term)

  -- Whitespace
  parseTerm (' ' : src) =
    parseTerm src

  -- Newlines
  parseTerm ('\n' : src) =
    parseTerm src

  -- Type
  parseTerm ('*' : src) =
    (src, \ ctx -> Term Typ)

  -- Kind
  parseTerm ('+' : src) =
    (src, \ ctx -> Term Kin)

  -- Forall
  parseTerm ('@' : src) = let
    (src0, nam) = parseName src
    (src1, typ) = parseTerm src0
    (src2, bod) = parseTerm src1
    in (src2, \ ctx -> Term (All False nam (typ ctx) (\ var -> bod ((nam,var) : ctx))))

  -- Lambda
  parseTerm ('#' : src) = let
    (src0, nam) = parseName src
    (src1, typ) = parseTerm src0
    (src2, bod) = parseTerm src1
    in (src2, \ ctx -> Term (Lam False nam (typ ctx) (\ var -> bod ((nam,var) : ctx))))

  -- Application
  parseTerm ('$' : src) = let
    (src0, fun) = parseTerm src
    (src1, arg) = parseTerm src0
    in (src1, \ ctx -> Term (App False (fun ctx) (arg ctx)))

  -- Local definition
  parseTerm ('/' : src) = let
    (src0, nam) = parseName src
    (src1, val) = parseTerm src0
    (src2, bod) = parseTerm src1
    in (src2, \ ctx -> Term (Let nam (val ctx) (\ var -> bod ((nam,var) : ctx))))

  -- Dependent intersection
  parseTerm ('&' : src) = let
    (src0, nam) = parseName src
    (src1, fst) = parseTerm src0
    (src2, snd) = parseTerm src1
    in (src2, \ ctx -> Term (Dep nam (fst ctx) (\ var -> snd ((nam,var) : ctx))))

  -- Dependent intersection proof
  parseTerm ('^' : src) = let
    (src0, nam) = parseName src
    (src1, typ) = parseTerm src0
    (src2, fst) = parseTerm src1
    (src3, snd) = parseTerm src2
    in (src3, \ ctx -> Term (Sec nam (\ var -> typ ((nam,var) : ctx)) (fst ctx) (snd ctx)))

  -- First projection
  parseTerm ('<' : src) = let
    (src0, sec) = parseTerm src
    in (src0, \ ctx -> Term (Fst (sec ctx)))

  -- Second projection
  parseTerm ('>' : src) = let
    (src0, sec) = parseTerm src
    in (src0, \ ctx -> Term (Snd (sec ctx)))

  -- Equality
  parseTerm ('=' : src) = let
    (src0, fst) = parseTerm src
    (src1, snd) = parseTerm src0
    in (src1, \ ctx -> Term (Eql (fst ctx) (snd ctx)))

  -- Reflexivity
  parseTerm (':' : src) = let
    (src0, prf) = parseTerm src
    (src1, ret) = parseTerm src0
    in (src1, \ ctx -> Term (Rfl (prf ctx) (ret ctx)))

  -- Symmetry
  parseTerm ('~' : src) = let
    (src0, eql) = parseTerm src
    in (src0, \ ctx -> Term (Sym (eql ctx)))

  -- Cast
  parseTerm ('!' : src) = let
    (src0, eql) = parseTerm src
    (src1, fst) = parseTerm src2
    (src2, snd) = parseTerm src1
    in (src2, \ ctx -> Term (Cst (eql ctx) (fst ctx) (snd ctx)))

  -- Rewrite
  parseTerm ('%' : src) = let
    (src0, nam) = parseName src
    (src1, eql) = parseTerm src0
    (src2, typ) = parseTerm src1
    (src3, ret) = parseTerm src2
    in (src3, \ ctx -> Term (Rwt nam (eql ctx) (\ var -> typ ((nam,var) : ctx)) (ret ctx)))

  -- Error
  parseTerm ('?' : src) =
    (src, \ ctx -> Term Err)

  -- Variables
  parseTerm src = let
    (src', nam) = parseName src
    in (src', \ ctx ->
      case find ((nam ==) . fst) ctx of
        Nothing    -> Term (Var nam)
        Just (_,t) -> t)

  -- Names
  parseName :: String -> (String, String)
  parseName "" = ("", "")
  parseName (' ' : src) = (src, "")
  parseName ('\n' : src) = (src, "")
  parseName (chr : src) = let
    (src0, nam) = parseName src
    in (src0, chr : nam)

-- Converts a Term to an ASCII String
toString :: Term -> String
toString = go 0 where
  go d (Term Typ)                   = "*"
  go d (Term Kin)                   = "+"
  go d (Term (Var nam))             = nam
  go d (Term (All era nam typ bod)) = let n = nam ++ show d in "@" ++ n ++ " " ++ go d typ ++ " " ++ go (d+1) (bod (Term (Var n)))
  go d (Term (Lam era nam typ bod)) = let n = nam ++ show d in "#" ++ n ++ " " ++ go d typ ++ " " ++ go (d+1) (bod (Term (Var n)))
  go d (Term (App era fun arg))     = "$" ++ go d fun ++ " " ++ go d arg
  go d (Term (Let nam val bod))     = let n = nam ++ show d in "/" ++ n ++ " " ++ go d val ++ " " ++ go (d+1) (bod (Term (Var n)))
  go d (Term (Dep nam fst snd))     = let n = nam ++ show d in "&" ++ n ++ " " ++ go d fst ++ " " ++ go (d+1) (snd (Term (Var n)))
  go d (Term (Sec nam typ fst snd)) = let n = nam ++ show d in "^" ++ n ++ " " ++ go d (typ (Term (Var n))) ++ " " ++ go d fst ++ " " ++ go d snd
  go d (Term (Fst sec))             = "<" ++ go d sec
  go d (Term (Snd sec))             = ">" ++ go d sec
  go d (Term (Eql fst snd))         = "=" ++ go d fst ++ " " ++ go d snd
  go d (Term (Rfl prf ret))         = ":" ++ go d prf ++ " " ++ go d ret
  go d (Term (Sym eql))             = "~" ++ go d eql
  go d (Term (Cst eql fst snd))     = "!" ++ go d eql ++ " " ++ go d fst ++ " " ++ go d snd
  go d (Term (Rwt nam eql typ ret)) = let n = nam ++ show d in "%" ++ n ++ " " ++ go d eql ++ " " ++ go d (typ (Term (Var n))) ++ " " ++ go d ret
  go d (Term Err)                   = "?"

-- Recursivelly annotate every constructor of a term with its type and normal form.
annotate :: Term -> Ann
annotate = go [] where
  go :: [(String, (Term, Term))] -> Term -> Ann

  -- Type: (* : +)
  go ctx (Term Typ) =
    Ann Typ (Term Typ) (Term Kin)

  -- Variable
  go ctx (Term (Var nam)) =
    case find ((nam ==) . fst) ctx of
      Just (nam, (nor, typ)) -> Ann (Var nam) nor typ
      Nothing -> Ann (Var nam) (Term (Var nam)) (Term (Var nam))

  -- Forall: (T : s) and (U[(t:T)/x] : s) implies ((@x T U) : *), where (s) is either (*) or (+)
  go ctx (Term (All era nam typ bod)) = let
    typ' = go ctx typ
    bod' = \var -> go ((nam, (var, norOf typ')) : ctx) (bod var)
    rVal = All era nam typ' bod'
    rNor = Term (All era nam (norOf typ') (\val -> norOf (bod' val)))
    rTyp = if isSort (typOf typ') && isSort (typOf (bod' (Term (Var nam))))
      then Term Typ
      else Term Err
    in Ann rVal rNor rTyp

  -- Lambda: (T : *) and (u[(x:T)/x] : U) implies ((λx t u) : (@x T U))
  go ctx (Term (Lam era nam typ bod)) = let
    typ' = go ctx typ
    bod' = ex nam (norOf typ') ctx bod
    rVal = Lam era nam typ' bod'
    rNor = if era
      then norOf (bod' (Term (Var nam)))
      else Term (Lam era nam (Term Typ) (norOf . bod'))
    rTyp = if isSort (typOf typ') && not (isErr (typOf (bod' (Term (Var nam)))))
      then Term (All era nam (norOf typ') (typOf . bod'))
      else Term Err
    in Ann rVal rNor rTyp

  -- Application: (t : (@x T U)) and (u : T) implies (($t u) : U[t/x])
  go ctx (Term (App era fun arg)) = let
    fun' = go ctx fun
    arg' = go ctx arg
    rVal = App era fun' arg'
    rNor = if era 
      then norOf fun'
      else case norOf fun' of
        (Term (Lam era nam typ bod)) -> bod (norOf arg')
        otherwise -> Term (App era (norOf fun') (norOf arg'))
    rTyp = case typOf fun' of
      (Term (All allEra allNam allTyp allBod)) ->
        if equals allTyp (typOf arg') &&
           allEra == era
            then allBod (norOf arg')
            else Term Err
      otherwise -> Term Err
    in Ann rVal rNor rTyp

  -- Local definition
  go ctx (Term (Let nam val bod)) = let
    val' = go ctx val
    bod' = ex nam (typOf val') ctx bod
    res' = bod' (norOf val')
    rVal = Let nam val' bod'
    rNor = norOf res'
    rTyp = typOf res'
    in Ann rVal rNor rTyp

  -- Dependent intersection: (T : *) and (U[(t:T)/x] : *) implies ((&x T U) : *)
  go ctx (Term (Dep nam fst snd)) = let
    fst' = go ctx fst
    snd' = ex nam (norOf fst') ctx snd
    rVal = Dep nam fst' snd'
    rNor = Term (Dep nam fst snd)
    rTyp = case (typOf fst', typOf (snd' (Term (Var nam)))) of
      (Term Typ, Term Typ) -> Term Typ
      otherwise -> Term Err
    in Ann rVal rNor rTyp

  -- Dependent intersection proof: (t : T), (u : U[t/x]), (t equals u) implies ((^x U t u) : (&x T U))
  go ctx (Term (Sec nam typ fst snd)) = let
    fst' = go ctx fst
    snd' = go ctx snd
    typ' = ex nam (typOf fst') ctx typ
    typ0 = norOf (typ' (norOf fst'))
    typ1 = typOf snd'
    rVal = Sec nam typ' fst' snd'
    rNor = Term (Sec nam (norOf . typ') (norOf fst') (norOf snd'))
    rTyp = if not (isErr (typOf fst')) || 
              not (isErr typ0) ||
              equals typ0 typ1 ||
              equals (norOf fst') (norOf snd')
              then Term (Dep nam (typOf fst') (norOf . typ'))
              else Term Err
    in Ann rVal rNor rTyp

  -- First projection: (t : (&x T U)) implies ((< t) : T) 
  go ctx (Term (Fst sec)) = let
    sec' = go ctx sec
    rVal = Fst sec'
    rNor = case norOf sec' of
      (Term (Sec nam typ fst snd)) -> fst
      otherwise -> Term (Fst (norOf sec'))
    rTyp = case typOf sec' of
      (Term (Dep nam fst snd)) -> fst
      otherwise -> Term Err
    in Ann rVal rNor rTyp
  
  -- Second projection: (t : (&x T U)) implies ((> t) : U[t/x]) 
  go ctx (Term (Snd sec)) = let
    sec' = go ctx sec
    rVal = Fst sec'
    rNor = case norOf sec' of
      (Term (Sec nam typ fst snd)) -> snd
      otherwise -> Term (Fst (norOf sec'))
    rTyp = case norOf sec' of
      (Term (Sec nam typ fst snd)) -> typ fst
      otherwise -> Term Err
    in Ann rVal rNor rTyp

  -- Equality: ((= t u) : *)
  go ctx (Term (Eql fst snd)) = let
    fst' = go ctx fst
    snd' = go ctx snd
    rVal = Eql fst' snd'
    rNor = Term (Eql (norOf fst') (norOf snd'))
    rTyp = if not (isErr (typOf fst')) &&
              not (isErr (typOf snd'))
              then Term Typ
              else Term Err
    in Ann rVal rNor rTyp

  -- Reflexivity: ((= t t) : *) implies ((: t u) : (= t t))
  go ctx (Term (Rfl eql ret)) = let
    eql' = go ctx eql
    ret' = go ctx ret
    rVal = Rfl eql' ret'
    rNor = norOf ret'
    rTyp = if not (isErr (typOf ret'))
      then Term (Eql (norOf eql') (norOf eql')) 
      else Term Err
    in Ann rVal rNor rTyp

  -- Symmetry: (t : (= T U)) implies (t : (= U T))
  go ctx (Term (Sym eql)) = let
    eql' = go ctx eql
    rVal = Sym eql'
    rNor = Term (Sym (norOf eql'))
    rTyp = case typOf eql' of
      (Term (Eql fst snd)) -> Term (Eql snd fst)
      otherwise -> Term Err
    in Ann rVal rNor rTyp

  -- Cast: (e : (= t u)) and (t : T) implies ((%e t u) : T)
  go ctx (Term (Cst eql fst snd)) = let
    eql' = go ctx eql
    fst' = go ctx fst
    snd' = go ctx snd
    rVal = Cst eql' fst' snd'
    rNor = norOf snd'
    rTyp = case typOf eql' of
      (Term (Eql fstVal sndVal)) ->
        if equals (norOf fst') fstVal &&
           equals (norOf snd') sndVal
           then typOf fst'
           else Term Err
      otherwise -> Term Err
    in Ann rVal rNor rTyp

  -- Rewrite: (t : (= t u)) and (p : P[t/x]) implies (p : P[u/x])
  go ctx (Term (Rwt nam eql typ ret)) = let
    eql' = go ctx eql
    typ' = ex nam (Term Typ) ctx typ
    ret' = go ctx ret
    rVal = Rwt nam eql' typ' ret'
    rNor = norOf ret'
    rTyp = case typOf eql' of
      (Term (Eql fstVal sndVal)) ->
        if equals (typOf ret') (norOf (typ' fstVal))
           then norOf (typ' sndVal)
           else Term Err
      otherwise -> Term Err
    in Ann rVal rNor rTyp

  ex :: String -> Term -> [(String, (Term, Term))] -> (Term -> Term) -> Term -> Ann
  ex nam typ ctx bod = \var -> go ((nam, (var, typ)) : ctx) (bod (Term (Var nam)))

-- Checks if two terms are syntactically equal
equals :: Term -> Term -> Bool
equals = go 0 where
  go :: Int -> Term -> Term -> Bool

  -- Type
  go d (Term Typ) (Term Typ) =
    True

  -- Kind
  go d (Term Kin) (Term Kin) =
    True

  -- Variable
  go d (Term (Var aNam)) (Term (Var bNam)) =
    aNam == bNam

  -- Forall
  go d (Term (All aEra aNam aTyp aBod)) (Term (All bEra bNam bTyp bBod)) = let
    var = Term (Var (show d))
    in aEra == bEra &&
       go d aTyp bTyp &&
       go (d+1) (aBod var) (bBod var)

  -- Lambda
  go d (Term (Lam aEra aNam aTyp aBod)) (Term (Lam bEra bNam bTyp bBod)) = let
    var = Term (Var (show d))
    in aEra == bEra &&
       go d aTyp bTyp &&
       go (d+1) (aBod var) (bBod var)

  -- Application
  go d (Term (App aEra aFun aArg)) (Term (App bEra bFun bArg)) =
    aEra == bEra &&
    go d aFun bFun &&
    go d aArg bArg

  -- Local definition
  go d (Term (Let aNam aVal aArg)) (Term (Let bNam bVal bArg)) = let
    var = Term (Var (show d))
    in go d aVal bVal &&
       go d (aArg var) (bArg var)

  -- Dependent intersection
  go d (Term (Dep aNam aFst aSnd)) (Term (Dep bNam bFst bSnd)) = let
    var = Term (Var (show d))
    in go d aFst bFst &&
       go d (aSnd var) (bSnd var)

  -- Dependent intersection proof
  go d (Term (Sec aNam aTyp aFst aSnd)) (Term (Sec bNam bTyp bFst bSnd)) = let
    var = Term (Var (show d))
    in go d (aTyp var) (bTyp var) &&
       go d aFst bFst &&
       go d aSnd bSnd

  -- First projection
  go d (Term (Fst aSec)) (Term (Fst bSec)) =
    go d aSec bSec

  -- Second projection
  go d (Term (Snd aSec)) (Term (Snd bSec)) =
    go d aSec bSec

  -- Equality
  go d (Term (Eql aFst aSnd)) (Term (Eql bFst bSnd)) =
    go d aFst bFst && 
    go d bSnd bSnd

  -- Reflexivity
  go d (Term (Rfl aVal aRet)) (Term (Rfl bVal bRet)) =
    go d aVal aRet &&
    go d bVal bRet

  -- Symmetry
  go d (Term (Sym aEql)) (Term (Sym bEql)) =
    go d aEql bEql

  -- Cast
  go d (Term (Cst aEql aFst aSnd)) (Term (Cst bEql bFst bSnd)) =
    go d aEql bEql &&
    go d aFst bFst &&
    go d aSnd bSnd

  -- Rewrite
  go d (Term (Rwt aNam aEql aTyp aVal)) (Term (Rwt bNam bEql bTyp bVal)) = let
    var = Term (Var (show d))
    in go d aEql bEql &&
       go d (aTyp var) (bTyp var) &&
       go d aVal bVal 

  -- Different terms
  go d a b =
    False

-- Checks if a term is either Typ or Kin
isSort :: Term -> Bool
isSort (Term Typ) = True
isSort (Term Kin) = True
isSort _          = False

-- Checks if a term is Err
isErr :: Term -> Bool
isErr (Term Err) = True
isErr _          = False

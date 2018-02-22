module Core where

-- Cedille Core (Aaron's Type Theory)
--
--   Asc   Nam   Hex   Desc                                                 
-- ,-----,-----,-----,------------------------------------------------------,
-- | *   | Typ | 0   | type of types                                        |
-- | +   | Kin | 1   | type of type of types                                |
-- |     | Var | 2   | variable                                             |
-- | @ & | All | 3   | forall                                               |
-- | # % | Lam | 4   | lambda                                               |
-- | / \ | App | 5   | application                                          |
-- | $   | Let | 6   | local definition                                     |
-- | |   | Dep | 7   | dependent intersection theorem                       |
-- | ^   | Bis | 8   | dependent intersection proof                         |
-- | <   | Fst | 9   | first element of dependent intersection              |
-- | >   | Snd | A   | second element of dependent intersection             |
-- | =   | Eql | B   | equality (t == t') theorem                           |
-- | :   | Rfl | C   | equality (t == t') proof                             |
-- | ~   | Sym | D   | symmetry of equality (t == t' implies t' == t)       |
-- | !   | Cst | E   | if (t == t') and (t' : T'), cast (t : T) to (t : T') |
-- | ?   | Rwt | F   | if (t == t'), cast (p : P[t/x]) to (p : P[t'/x])     |
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
  | Bis String r (b -> r) r
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

  -- Forall (erased)
  parseTerm ('&' : src) = let
    (src0, nam) = parseName src
    (src1, typ) = parseTerm src0
    (src2, bod) = parseTerm src1
    in (src2, \ ctx -> Term (All True nam (typ ctx) (\ var -> bod ((nam,var) : ctx))))

  -- Lambda
  parseTerm ('#' : src) = let
    (src0, nam) = parseName src
    (src1, typ) = parseTerm src0
    (src2, bod) = parseTerm src1
    in (src2, \ ctx -> Term (Lam False nam (typ ctx) (\ var -> bod ((nam,var) : ctx))))

  -- Lambda (erased)
  parseTerm ('%' : src) = let
    (src0, nam) = parseName src
    (src1, typ) = parseTerm src0
    (src2, bod) = parseTerm src1
    in (src2, \ ctx -> Term (Lam True nam (typ ctx) (\ var -> bod ((nam,var) : ctx))))

  -- Application
  parseTerm ('/' : src) = let
    (src0, fun) = parseTerm src
    (src1, arg) = parseTerm src0
    in (src1, \ ctx -> Term (App False (fun ctx) (arg ctx)))

  -- Application (erased)
  parseTerm ('\\' : src) = let
    (src0, fun) = parseTerm src
    (src1, arg) = parseTerm src0
    in (src1, \ ctx -> Term (App True (fun ctx) (arg ctx)))

  -- Local definition
  parseTerm ('$' : src) = let
    (src0, nam) = parseName src
    (src1, val) = parseTerm src0
    (src2, bod) = parseTerm src1
    in (src2, \ ctx -> Term (Let nam (val ctx) (\ var -> bod ((nam,var) : ctx))))

  -- Dependent intersection
  parseTerm ('|' : src) = let
    (src0, nam) = parseName src
    (src1, fty) = parseTerm src0
    (src2, sty) = parseTerm src1
    in (src2, \ ctx -> Term (Dep nam (fty ctx) (\ var -> sty ((nam,var) : ctx))))

  -- Dependent intersection proof
  parseTerm ('^' : src) = let
    (src0, nam) = parseName src
    (src1, typ) = parseTerm src0
    (src2, fst) = parseTerm src1
    (src3, snd) = parseTerm src2
    in (src3, \ ctx -> Term (Bis nam (fst ctx) (\ var -> typ ((nam,var) : ctx)) (snd ctx)))

  -- First projection
  parseTerm ('<' : src) = let
    (src0, bis) = parseTerm src
    in (src0, \ ctx -> Term (Fst (bis ctx)))

  -- Second projection
  parseTerm ('>' : src) = let
    (src0, bis) = parseTerm src
    in (src0, \ ctx -> Term (Snd (bis ctx)))

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
  parseTerm ('?' : src) = let
    (src0, nam) = parseName src
    (src1, eql) = parseTerm src0
    (src2, typ) = parseTerm src1
    (src3, ret) = parseTerm src2
    in (src3, \ ctx -> Term (Rwt nam (eql ctx) (\ var -> typ ((nam,var) : ctx)) (ret ctx)))

  -- Error
  parseTerm ('_' : src) =
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

  parseBool :: String -> (String, Bool)
  parseBool ('\'' : src) = (src, True)
  parseBool src = (src, False)

-- Converts a Term to an ASCII String
toString :: Term -> String
toString = go 0 where
  -- Type
  go d (Term Typ)
    = "*"

  -- Kind
  go d (Term Kin)
    = "+"

  -- Variable
  go d (Term (Var nam))
    = nam

  -- Forall
  go d (Term (All era nam typ bod)) = let
    tag' = if era then "&" else "@"
    nam' = nam ++ show d
    typ' = go d typ
    bod' = go (d+1) (bod (Term (Var nam')))
    in tag' ++ nam' ++ " " ++ typ' ++ " " ++ bod'

  -- Lambda
  go d (Term (Lam era nam typ bod)) = let
    tag' = if era then "%" else "#"
    nam' = nam ++ show d
    typ' = go d typ
    bod' = go (d+1) (bod (Term (Var nam')))
    in tag' ++ nam' ++ " " ++ typ' ++ " " ++ bod'

  -- Application
  go d (Term (App era fun arg)) = let
    tag' = if era then "\\" else "/"
    fun' = go d fun
    arg' = go d arg
    in tag' ++ fun' ++ " " ++ arg'

  -- Local definition
  go d (Term (Let nam val bod)) = let
    nam' = nam ++ show d
    val' = go d val
    bod' = go (d+1) (bod (Term (Var nam')))
    in "|" ++ nam' ++ " " ++ val' ++ " " ++ bod'

  -- Dependent intersection
  go d (Term (Dep nam fty sty)) = let
    nam' = nam ++ show d
    fty' = go d fty
    sty' = go (d+1) (sty (Term (Var nam')))
    in "^" ++ nam' ++ " " ++ fty' ++ " " ++ sty'

  -- Dependent intersection rpoof
  go d (Term (Bis nam fst sty snd)) = let
    nam' = nam ++ show d
    fst' = go d fst
    sty' = go d (sty (Term (Var nam')))
    snd' = go d snd
    in "$" ++ nam' ++ " " ++ fst' ++ " " ++ sty' ++ " " ++ snd'

  -- First projection
  go d (Term (Fst bis)) =
    "<" ++ go d bis

  -- Bis projection
  go d (Term (Snd bis)) =
    ">" ++ go d bis
    
  -- Equality
  go d (Term (Eql fst snd)) = let
    fst' = go d fst
    snd' = go d snd
    in "=" ++ fst' ++ " " ++ snd'

  -- Reflexivity
  go d (Term (Rfl prf ret)) = let
    prf' = go d prf
    ret' = go d ret
    in ":" ++ prf' ++ " " ++ ret'

  -- Symmetry
  go d (Term (Sym eql)) = let
    eql' = go d eql
    in "~" ++ eql'

  -- Cast
  go d (Term (Cst eql fst snd)) = let
    eql' = go d eql
    fst' = go d fst
    snd' = go d snd
    in "!" ++ eql' ++ " " ++ fst' ++ " " ++ snd'

  -- Rewrite
  go d (Term (Rwt nam eql typ ret)) = let
    nam' = nam ++ show d
    eql' = go d eql
    typ' = go d (typ (Term (Var nam')))
    ret' = go d ret
    in "?" ++ nam' ++ " " ++ eql' ++ " " ++ typ' ++ " " ++ ret'

  -- Error
  go d (Term Err) =
    "_"

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
    rTyp = if isSort (typOf typ') && not (isErr (typOf (bod' (Term (Var nam)))))
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
  go ctx (Term (Dep nam fty sty)) = let
    fty' = go ctx fty
    sty' = ex nam (norOf fty') ctx sty
    rVal = Dep nam fty' sty'
    rNor = Term (Dep nam fty sty)
    rTyp = case (typOf fty', typOf (sty' (Term (Var nam)))) of
      (Term Typ, Term Typ) -> Term Typ
      otherwise -> Term Err
    in Ann rVal rNor rTyp

  -- Dependent intersection proof: (t : T), (u : U[t/x]), (t equals u) implies ((^x U t u) : (&x T U))
  go ctx (Term (Bis nam fst sty snd)) = let
    fst' = go ctx fst
    sty' = ex nam (typOf fst') ctx sty
    snd' = go ctx snd
    sty0 = norOf (sty' (norOf fst'))
    sty1 = typOf snd'
    rVal = Bis nam fst' sty' snd'
    rNor = Term (Bis nam (norOf fst') (norOf . sty') (norOf snd'))
    rTyp = if
      not (isErr (typOf fst')) || 
      not (isErr sty0) ||
      equals sty0 sty1 ||
      equals (norOf fst') (norOf snd')
      then Term (Dep nam (typOf fst') (norOf . sty'))
      else Term Err
    in Ann rVal rNor rTyp

  -- First projection: (t : (&x T U)) implies ((< t) : T) 
  go ctx (Term (Fst bis)) = let
    bis' = go ctx bis
    rVal = Fst bis'
    rNor = case norOf bis' of
      (Term (Bis nam fst sty snd)) -> fst
      otherwise -> Term (Fst (norOf bis'))
    rTyp = case typOf bis' of
      (Term (Dep nam fty sty)) -> fty
      otherwise -> Term Err
    in Ann rVal rNor rTyp
  
  -- Bis projection: (t : (&x T U)) implies ((> t) : U[t/x]) 
  go ctx (Term (Snd bis)) = let
    bis' = go ctx bis
    rVal = Fst bis'
    rNor = case norOf bis' of
      (Term (Bis nam fst sty snd)) -> snd
      otherwise -> Term (Fst (norOf bis'))
    rTyp = case norOf bis' of
      (Term (Bis nam fst sty snd)) -> sty fst
      otherwise -> Term Err
    in Ann rVal rNor rTyp

  -- Equality: ((= t u) : *)
  go ctx (Term (Eql fst snd)) = let
    fst' = go ctx fst
    snd' = go ctx snd
    rVal = Eql fst' snd'
    rNor = Term (Eql (norOf fst') (norOf snd'))
    rTyp = if
      not (isErr (typOf fst')) &&
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
  go d (Term (Dep aNam aFty aSty)) (Term (Dep bNam bFty bSty)) = let
    var = Term (Var (show d))
    in go d aFty bFty &&
       go d (aSty var) (bSty var)

  -- Dependent intersection proof
  go d (Term (Bis aNam aFst aSty aSnd)) (Term (Bis bNam bFst bSty bSnd)) = let
    var = Term (Var (show d))
    in go d aFst bFst &&
       go d (aSty var) (bSty var) &&
       go d aSnd bSnd

  -- First projection
  go d (Term (Fst aBis)) (Term (Fst bBis)) =
    go d aBis bBis

  -- Bis projection
  go d (Term (Snd aBis)) (Term (Snd bBis)) =
    go d aBis bBis

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

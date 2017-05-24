{-# LANGUAGE TemplateHaskell, FlexibleContexts #-}
module TH where

import Control.Monad (when)
import Data.Monoid
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Data (Data, Fixity(..))
import Data.Generics (everything, mkQ)
import Data.List (nub, nubBy, sortBy, unzip4)
import Control.Monad.State.Strict
import Control.Monad.Writer.Strict
import Language.Haskell.TH

-- |The 'deriveDataGADT' function generates declarations of the
--  'Data.Data' instances for the input name of a data type.
--  
--  Note that, the existential data types are not supported.
--  
--  If the referenced data type is non-GADT, then a normal derivation 
--  is made. 
--  Otherwise, each constructor is grouped with other constructors 
--  whose return type is more general. And a newtype is created 
--  for each group. A 'Data.Data' instance is declared for each 
--  of the newtype. 
--
--  Example:
--  @
--    data S4 a b where
--        S4a :: S4 a b
--        S4b :: a -> S4 a a
--        S4c :: S4 Int Int
--        S4d :: Int -> Int -> S4 Int Int
--  @
--  Three groups are formed:
--  [S4a], [S4b, S4a], [S4c, S4d, S4b, S4a]
--  
--  Therefore, following newtype are crafted:
--  @
--    newtype S4_1 a b = S4_1 (S4 a b)
--    newtype S4_2 a   = S4_2 (S4 a a)
--    newtype S4_3     = S4_3 (S4 Int Int)
--    
--    instance (Data a, Data b) => Data (S4_1 a b)
--    
--    instance Data a => Data (S4_2 a)
--
--    instance Data (S4_3 Int Int)
--  @ 
--
--  Apart from the crafted newtype, a new type class 'ClassDataFromXX'
--  and a closed type family 'DataFromXX' is created, for an easy 
--  convertion from original data to crafted newtype.
--  
--  In the above example for data type S4, 
--  @
--    type family DataFromS4 a where
--        DataFromS4 (S4 Int Int) = S4_3
--        DataFromS4 (S4 a a) = S4_2 a
--        DataFromS4 (S4 a b) = S4_1 a b
--    class ClassDataFromS4 a where
--        dataFromS4 :: a -> DataFromS4 a
--  @
--  
deriveDataGADT :: Name -> DecsQ
deriveDataGADT t = do
    TyConI (DataD cxt dname dtyvbs _ dcons _) <- reify t
    when (not $ null cxt) (fail "datatype with cxt not supported.")

    case groupDCons dname dtyvbs dcons of
      GrUnsupported iv -> fail ("unsupported GADT constructor: " ++ (show $ ppr $ iv))
      GrNormalDerive   -> let typeFromTV (PlainTV  n)   = VarT n
                              typeFromTV (KindedTV n k) = VarT n
                              drvcxt = map (AppT (ConT ''Data) . typeFromTV) dtyvbs
                              gentyp = foldl AppT (ConT dname) (map typeFromTV dtyvbs)
                          in return $ [StandaloneDerivD drvcxt (AppT (ConT ''Data) gentyp)]
      GrAddhoc m       -> do 
        -- sort the groups in ascending order of generality
        -- so that the derived type family can follow
        let variations = sortBy moreGen (Map.keys m)
        -- list of newtypes, each of which corresponds to a subset of constructors
        -- [(made-newtype, made-name, made-type, original type)]
        dt <- forM (zip [1..] variations) $ \(idx, ty) -> do
                let ti = mkName (nameBase t ++ "_" ++show idx)
                    tv = nub (varsOfTypCon ty)
                    tb = map PlainTV tv
                    nt = foldl AppT (ConT ti) (map VarT tv)
                    sv = bangType (bang noSourceUnpackedness noSourceStrictness) (return ty)
                ntd <- newtypeD (return []) ti tb Nothing (normalC ti [sv]) (return [])
                return (ntd, ti, nt, ty)
        
        -- closed type family: DataFromXX
        -- help to decide which newtype should be chosen.
        let tfnm = mkName ("DataFrom" ++ nameBase t)
        tfvr <- newName "a"
        tf <- closedTypeFamilyD tfnm [PlainTV tfvr] noSig Nothing $
                map (\(_, _, dty, sty) -> tySynEqn [return sty] (return dty)) dt
        
        -- derive Data instance for all newtypes
        dr <- mapM (drvInstData m) dt

        -- ClassDataFromXX: the helper class for converting
        -- from orignal type to a newtype, which is instance
        -- of Data.
        dc <- dataFromClass t tfnm dt

        (dt, _, _, _) <- return (unzip4 dt)
        return $ dt ++ [tf] ++ (concat dr) ++ dc

  where
    varsOfTypCon = let isVarT a@(VarT nm) = [nm]
                       isVarT _           = []
                   in everything (++) ([] `mkQ` isVarT)

    moreGen t1 t2 | unifyTo t1 t2 /= NotUnifiable = GT
                  | unifyTo t2 t1 /= NotUnifiable = LT
                  | otherwise = EQ

    drvInstData tbl (ntd, ntn, nty, key) = do
      let cons = tbl Map.! key
          tynt = mkName $ "ty" ++ nameBase ntn
      Just mkConstr   <- lookupValueName "mkConstr"
      Just mkDataType <- lookupValueName "mkDataType"

      -- for each constructure XX, we declare a value
      -- conXX = mkConstr ""
      concook <- forM (zip [1..] cons) (\(idx, con) -> do
          (name,args) <- coninfo con 
          let valname = mkName ("con" ++ nameBase ntn ++ "_" ++ show idx)
              conname = nameBase ntn ++ "_" ++ nameBase name
              conargs = map (litE . StringL . nameBase) args
          decl <- valD (varP valname) (normalB $ 
                    (varE mkConstr) `appE` (varE tynt) `appE` (litE $ StringL conname) `appE` (listE conargs) `appE` (conE 'Prefix)) []
          return (decl, valname))

      let (condelcs, connames) = unzip concook
          convals = map varE connames
      tydecl <- valD (varP tynt) (normalB $ varE mkDataType `appE` litE (StringL (nameBase ntn)) `appE` listE convals) []

      let cxt = forM (nub $ varsOfTypCon key) (appT (conT ''Data) . varT)
          funToConstr   = funD (mkName "toConstr") $ 
                            flip map (zip cons connames) $ (\(con, conval) -> do
                              (name,_) <- coninfo con 
                              clause [conP ntn [recP name []]] (normalB $ varE conval) [])
          funDataTypeOf = funD (mkName "dataTypeOf") $
                            [clause [wildP] (normalB $ varE tynt) []]
          funGfoldl     = funD (mkName "gfoldl") $
                            flip map cons (\con -> do
                              (name,args) <- coninfo con
                              clause [varP argK, varP argZ, conP ntn [conP name (map varP args)]] (normalB $ gfoldlBdy name args) [])
          funGunfold     = funD (mkName "gunfold") $
                            [clause [varP argK, varP argZ, varP argC] (normalB $ gunfoldBdy) []]
          argK = mkName "k"
          argZ = mkName "z"
          argC = mkName "c"
          concomp c1 c2 args = let appargs = conE c1 `appE` foldl appE (conE c2) (map varE args)
                               in case args of
                                    []  -> appargs
                                    [a] -> lam1E (varP a) appargs
                                    _   -> lamE (map varP args) appargs
          gfoldlBdy name args = let mk0 = varE argZ `appE` concomp ntn name args
                                in foldl (\e a -> varE argK `appE` e `appE` varE a) mk0 args
          gunfoldBdy = do Just constrIndex <- lookupValueName "constrIndex"
                          caseE (appE (varE constrIndex) (varE argC)) $
                            flip map (zip [1..] cons) $ (\(idx, con) -> do
                              (name,args) <- coninfo con 
                              let mk0 = varE argZ `appE` concomp ntn name args
                                  mk1 = foldl (\e _ -> varE argK `appE` e) mk0 args
                              match (litP $ IntegerL idx) (normalB mk1) [])
                                   
      indecl <- instanceD cxt (appT (conT ''Data) (return nty)) [funToConstr, funDataTypeOf, funGfoldl, funGunfold]

      return $ condelcs ++ [tydecl, indecl]

    dataFromClass classnm tyfunnm datainfo = do
      tyvarA <- newName "a"
      tyvarB <- newName "b"
      let classNameB    = "ClassDataFrom" ++ nameBase classnm
          className     = mkName classNameB
          className'    = mkName (classNameB ++ "'")
          classFunNameB = "dataFrom" ++ nameBase classnm
          classFunName  = mkName classFunNameB
          classFunName' = mkName (classFunNameB ++ "'")
      c1 <- classD (return []) className [PlainTV tyvarA] []
              [sigD classFunName (arrowT `appT` (varT tyvarA) `appT` (appT (conT tyfunnm) (varT tyvarA)))]
      c2 <- classD (return []) className' [PlainTV tyvarA, PlainTV tyvarB] []
              [sigD classFunName' (arrowT `appT` (varT tyvarA) `appT` (varT tyvarB))]
      i1 <- instanceD 
              (return [ConT className' `AppT` (VarT tyvarA) `AppT` (ConT tyfunnm `AppT` (VarT tyvarA))])
              (conT className `appT` (varT tyvarA))
              [funD classFunName [clause [] (normalB $ varE classFunName') []]]
      i2 <- forM datainfo $ \(_, ntn, _, typ) -> do
              let typ' = foldl AppT (ConT ntn) (map VarT (nub $ varsOfTypCon typ))
              instanceD (return []) (conT className' `appT` (return typ) `appT` (return typ'))
                [funD classFunName' [clause [] (normalB $ conE ntn) []]]
      return $ [c1,c2] ++ [i1] ++ i2

    -- The Con is guaranteed to be a Gadt constructor.
    coninfo :: Con -> Q (Name, [Name])
    coninfo (GadtC [name] args _)    = do let cnt = length args 
                                          let nm  = map (\i -> mkName $ "arg" ++ show i) [1..cnt]
                                          return (name, nm)
    coninfo (RecGadtC [name] args _) = return (name, map (\(n,_,_)->n) args)
    
data GroupResult = GrNormalDerive
                 | GrUnsupported [Con]
                 | GrAddhoc (Map.Map Type [Con])

-- A Gadt Con has its result type, so we group the [Con] into a mapping, where
-- the key is a type
-- the value is [Con] that can result in that type.
groupDCons :: Name -> [TyVarBndr] -> [Con] -> GroupResult
groupDCons name tyvbs cons 
    | isNormal      = GrNormalDerive
    | not (null iv) = GrUnsupported iv

    | otherwise     = GrAddhoc (Map.fromList grpCons)

  where
    isNormal = not $ any isGadt cons
    isGadt (ForallC _ _ t) = isGadt t
    isGadt (GadtC {}) = True
    isGadt (RecGadtC {}) = True
    isGadt _ = False

    iv = filter invalid cons
    invalid (ForallC bnds cxt con) 
      | GadtC    _ _ ty <- con, any (not . appearIn' ty) bnds, easyRetType ty = True
      | RecGadtC _ _ ty <- con, any (not . appearIn' ty) bnds, easyRetType ty = True
    invalid _                    = False

    appearIn' ty (PlainTV n)    = appearIn ty n
    appearIn' ty (KindedTV n _) = appearIn ty n

    easyRetType (ConT cn)   = cn == name
    easyRetType (AppT t1 _) = easyRetType t1
    easyRetType _           = False

    appearIn ty nm
      | ForallT{}  <- ty = error "ForallT may not occur"
      | AppT t0 t1 <- ty = appearIn t0 nm || appearIn t1 nm
      | SigT t0 _  <- ty = appearIn t0 nm
      | VarT vn    <- ty = vn == nm
      | ConT _     <- ty = False
      | ParensT t0 <- ty = appearIn t0 nm 
      | InfixT t0 _ t1  <- ty = appearIn t0 nm || appearIn t1 nm 
      | UInfixT t0 _ t1 <- ty = appearIn t0 nm || appearIn t1 nm
      | _               <- ty = False

    unqCons = let unq (ForallC _ _ con) = unq con
                  unq con               = con
              in map unq cons
    grpCons = let moreGen c1 c2 = unifyTo (typeOfGadtCon c2) (typeOfGadtCon c1) /= NotUnifiable
                  typeOfGadtCon (GadtC _ _ t) = t
                  typeOfGadtCon (RecGadtC _ _ t) = t
                  typ = map typeOfGadtCon unqCons
                  grp = map (flip filter unqCons . moreGen) unqCons
              in nubOn snd $ zip typ grp
    
data UnifyResult = NotUnifiable
                 | UnifyOne Name Type
                 | UnifyMany (Map.Map Name Type)
  deriving (Show, Eq)

instance Monoid UnifyResult where
  mempty = UnifyMany Map.empty
  mappend NotUnifiable _ = NotUnifiable
  mappend _ NotUnifiable = NotUnifiable
  mappend (UnifyOne n1 t1) u2 = mappend (UnifyMany (Map.singleton n1 t1)) u2
  mappend u1 (UnifyOne n2 t2) = mappend u1 (UnifyMany (Map.singleton n2 t2))
  mappend (UnifyMany u1) (UnifyMany u2) = Map.foldrWithKey ins (Map.foldrWithKey ins (UnifyMany Map.empty) u1) u2
    where 
      ins name typ NotUnifiable = NotUnifiable
      ins name typ ret@(UnifyMany m) | Map.member name m = if (m Map.! name) == typ then ret else NotUnifiable
                                     | otherwise = UnifyMany (Map.insert name typ m)

-- Find a subsitution that substitutes type t1 into t2.
unifyTo t1 t2 = execWriter (go Set.empty t1 t2)
  where
    go bounds (VarT v) t | Set.member v bounds, VarT w <- t, w == v = return ()
                         | Set.member v bounds = tell NotUnifiable
                         | otherwise = tell (UnifyOne v t)
    go bounds (AppT t1a t1b) (AppT t2a t2b) = do go bounds t1a t2a
                                                 go bounds t1b t2b
    go bounds (SigT t1 k1) (SigT t2 k2) | k1 == k2  = go bounds t1 t2
                                        | otherwise = tell NotUnifiable
    go bounds (ConT c1) (ConT c2) | c1 == c2  = return ()
                                  | otherwise = tell NotUnifiable
    go bounds (InfixT t1a _ t1b) (InfixT t2a _ t2b) = do go bounds t1a t2a
                                                         go bounds t1b t2b
    go bounds (UInfixT t1a _ t1b) (UInfixT t2a _ t2b) = do go bounds t1a t2a
                                                           go bounds t1b t2b
    go bounds (ParensT t1) (ParensT t2) = go bounds t1 t2
    go bounds (ForallT b1 c1 t1) (ForallT b2 c2 t2)
      | length b1 == length b2 = do let v1 = map nameFromTV b1
                                        v2 = map nameFromTV b2
                                        sp = Map.fromList (zip v2 v1)
                                    forM (zip c1 c2) (\(c1i,c2i) -> go (Set.union bounds (Set.fromList v1)) c1i (substVar sp c2i))                                    
                                    go (Set.union bounds (Set.fromList v1)) t1 (substVar sp t2)
      | otherwise = tell NotUnifiable
    go bounds c1 c2 | c1 == c2  = return ()
                    | otherwise = tell NotUnifiable

    substVar :: Map.Map Name Name -> Type -> Type
    substVar bnds (ForallT b c t)       = let bset = Set.fromList $ map nameFromTV b
                                              bnds' = Map.filterWithKey (\k _ -> k `Set.notMember` bset) bnds
                                              c' = map (substVar bnds') c
                                              t' = substVar bnds' t
                                          in ForallT b c' t'
    substVar bnds (AppT t0 t1)          = AppT (substVar bnds t0) (substVar bnds t1)
    substVar bnds (SigT t0 k)           = SigT (substVar bnds t0) (substVar bnds k)
    substVar bnds (InfixT t0 n t1)      = InfixT (substVar bnds t0) n (substVar bnds t1)
    substVar bnds (UInfixT t0 n t1)     = UInfixT (substVar bnds t0) n (substVar bnds t1)
    substVar bnds (ParensT t0)          = ParensT (substVar bnds t0)
    substVar bnds (VarT v) | Map.member v bnds = VarT (bnds Map.! v)
    substVar bnds t0                    = t0

    nameFromTV (PlainTV  n)   = n
    nameFromTV (KindedTV n _) = n

nubOn prj = nubBy (\a b -> prj a == prj b)
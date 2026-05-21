module Core.Case.CaseTree

import Core.TT

import Data.List
import Data.So
import Data.String
import Idris.Pretty.Annotations

import Libraries.Data.NameMap
import Libraries.Text.PrettyPrint.Prettyprinter
import Libraries.Data.List.SizeOf

import Decidable.Equality

%default covering

public export
data ConTag = DConTag Name Int
            | TConTag Name

export
conName : ConTag -> Name
conName (DConTag n _) = n
conName (TConTag n) = n

export
tagOrder : ConTag -> Maybe Int
tagOrder (DConTag _ i) = Just i
tagOrder (TConTag {}) = Nothing

export
conTagEq : (x, y : ConTag) -> Maybe (x = y)
conTagEq (DConTag n i) (DConTag n' i')
    = do Refl <- nameEq n n'
         case decEq i i' of
              Yes Refl => Just Refl
              No contra => Nothing
conTagEq (TConTag n) (TConTag n') = (\xy => cong TConTag xy) <$> nameEq n n'
conTagEq _ _ = Nothing

export
Eq ConTag where
  DConTag _ i == DConTag _ i' = i == i'
  TConTag n == TConTag n' = n == n'
  _ == _ = False

mutual
  ||| Case trees in A-normal forms
  ||| i.e. we may only dispatch on variables, not expressions
  public export
  data CaseTree : Scoped where
       ||| case x return scTy of { p1 => e1 ; ... }
       Case : (idx : Nat) ->
              (0 p : IsVar name idx vars) ->
              (scTy : Term vars) -> List (CaseAlt vars) ->
              CaseTree vars
       ||| RHS: no need for further inspection
       ||| The Int is a clause id that allows us to see which of the
       ||| initial clauses are reached in the tree
       STerm : Int -> Term vars -> CaseTree vars
       ||| error from a partial match
       Unmatched : (msg : String) -> CaseTree vars
       ||| Absurd context
       Impossible : CaseTree vars

  ||| Case alternatives. Unlike arbitrary patterns, they can be at most
  ||| one constructor deep.
  public export
  data CaseAlt : Scoped where
       ||| Constructor for a data type; bind the arguments and subterms.
       ConCase : ConTag -> (args : List Name) ->
                 CaseTree (Scope.addInner vars args) -> CaseAlt vars
       ||| Lazy match for the Delay type use for codata types
       DelayCase : (ty : Name) -> (arg : Name) ->
                   CaseTree (Scope.addInner vars [ty, arg]) -> CaseAlt vars
                   -- TODO `arg` and `ty` should be swapped, as in Yaffle
       ||| Match against a literal
       ConstCase : Constant -> CaseTree vars -> CaseAlt vars
       ||| Catch-all case
       DefaultCase : CaseTree vars -> CaseAlt vars

export
FreelyEmbeddable CaseTree where

mutual
  public export
  measure : CaseTree vars -> Nat
  measure (Case idx p scTy xs) = sum $ measureAlts <$> xs
  measure (STerm x y) = 0
  measure (Unmatched msg) = 0
  measure Impossible = 0

  measureAlts : CaseAlt vars -> Nat
  measureAlts (ConCase tag args y) = 1 + (measure y)
  measureAlts (DelayCase ty arg x) = 1 + (measure x)
  measureAlts (ConstCase x y) = 1 + (measure y)
  measureAlts (DefaultCase x) = 1 + (measure x)

export
isDefault : CaseAlt vars -> Bool
isDefault (DefaultCase _) = True
isDefault _ = False

mutual
  export
  StripNamespace (CaseTree vars) where
    trimNS ns (Case idx p scTy xs)
        = Case idx p (trimNS ns scTy) (map (trimNS ns) xs)
    trimNS ns (STerm x t) = STerm x (trimNS ns t)
    trimNS ns c = c

    restoreNS ns (Case idx p scTy xs)
        = Case idx p (restoreNS ns scTy) (map (restoreNS ns) xs)
    restoreNS ns (STerm x t) = STerm x (restoreNS ns t)
    restoreNS ns c = c

  export
  StripNamespace (CaseAlt vars) where
    trimNS ns (ConCase tag args t) = ConCase tag args (trimNS ns t)
    trimNS ns (DelayCase ty arg t) = DelayCase ty arg (trimNS ns t)
    trimNS ns (ConstCase x t) = ConstCase x (trimNS ns t)
    trimNS ns (DefaultCase t) = DefaultCase (trimNS ns t)

    restoreNS ns (ConCase tag args t) = ConCase tag args (restoreNS ns t)
    restoreNS ns (DelayCase ty arg t) = DelayCase ty arg (restoreNS ns t)
    restoreNS ns (ConstCase x t) = ConstCase x (restoreNS ns t)
    restoreNS ns (DefaultCase t) = DefaultCase (restoreNS ns t)


public export
data Pat : Type where
     PAs : FC -> Name -> Pat -> Pat
     PCon : FC -> Name -> (tag : Int) -> (arity : Nat) ->
            List Pat -> Pat
     PTyCon : FC -> Name -> (arity : Nat) -> List Pat -> Pat
     PConst : FC -> (c : Constant) -> Pat
     PArrow : FC -> (x : Name) -> Pat -> Pat -> Pat
     PDelay : FC -> LazyReason -> Pat -> Pat -> Pat
     -- TODO: Matching on lazy types
     PLoc : FC -> Name -> Pat
     PUnmatchable : FC -> ClosedTerm -> Pat

export
isPConst : Pat -> Maybe Constant
isPConst (PConst _ c) = Just c
isPConst _ = Nothing

public export
0 isConPat : Pat -> Bool
isConPat (PAs _ _ p) = isConPat p
isConPat (PCon {}) = True
isConPat (PTyCon {}) = True
isConPat (PConst {}) = True
isConPat (PArrow {}) = True
isConPat (PDelay {}) = True
isConPat _ = False

public export
0 IsConPat : Pat -> Type
IsConPat = So . isConPat

showCT : {vars : _} -> (indent : String) -> CaseTree vars -> String
showCA : {vars : _} -> (indent : String) -> CaseAlt vars  -> String

showCT indent (Case idx prf ty alts)
  = "case " ++ show (nameAt prf) ++ "[" ++ show idx ++ "] : " ++ show ty ++ " of"
  ++ "\n" ++ indent ++ " { "
  ++ showSep ("\n" ++ indent ++ " | ")
             (assert_total (map (showCA ("  " ++ indent)) alts))
  ++ "\n" ++ indent ++ " }"
showCT indent (STerm i tm) = "[" ++ show i ++ "] " ++ show tm
showCT indent (Unmatched msg) = "Error: " ++ show msg
showCT indent Impossible = "Impossible"

showCA indent (ConCase tag args sc)
        = showSep " " (map show (conName tag :: args)) ++ " => " ++
          showCT indent sc
showCA indent (DelayCase _ arg sc)
        = "Delay " ++ show arg ++ " => " ++ showCT indent sc
showCA indent (ConstCase c sc)
        = "Constant " ++ show c ++ " => " ++ showCT indent sc
showCA indent (DefaultCase sc)
        = "_ => " ++ showCT indent sc

export
covering
{vars : _} -> Show (CaseTree vars) where
  show = showCT ""

export
covering
{vars : _} -> Show (CaseAlt vars) where
  show = showCA ""

mutual
  export
  eqTree : CaseTree vs -> CaseTree vs' -> Bool
  eqTree (Case i _ _ alts) (Case i' _ _ alts')
      = i == i'
       && length alts == length alts'
       && all (uncurry eqAlt) (zip alts alts')
  eqTree (STerm _ t) (STerm _ t') = eqTerm t t'
  eqTree (Unmatched _) (Unmatched _) = True
  eqTree Impossible Impossible = True
  eqTree _ _ = False

  eqAlt : CaseAlt vs -> CaseAlt vs' -> Bool
  eqAlt (ConCase t args tree) (ConCase t' args' tree')
      = t == t' && eqTree tree tree' -- assume arities match, since name does
  eqAlt (DelayCase _ _ tree) (DelayCase _ _ tree')
      = eqTree tree tree'
  eqAlt (ConstCase c tree) (ConstCase c' tree')
      = c == c' && eqTree tree tree'
  eqAlt (DefaultCase tree) (DefaultCase tree')
      = eqTree tree tree'
  eqAlt _ _ = False

export
covering
Show Pat where
  show (PAs _ n p) = show n ++ "@(" ++ show p ++ ")"
  show (PCon _ n i _ args) = show n ++ " " ++ show i ++ " " ++ assert_total (show args)
  show (PTyCon _ n _ args) = "<TyCon>" ++ show n ++ " " ++ assert_total (show args)
  show (PConst _ c) = show c
  show (PArrow _ x s t) = "(" ++ show s ++ " -> " ++ show t ++ ")"
  show (PDelay _ _ _ p) = "(Delay " ++ show p ++ ")"
  show (PLoc _ n) = show n
  show (PUnmatchable _ tm) = ".(" ++ show tm ++ ")"

export
Pretty IdrisSyntax Pat where
  prettyPrec d (PAs _ n p) = pretty0 n <++> keyword "@" <+> parens (pretty p)
  prettyPrec d (PCon _ n _ _ args) =
    parenthesise (d > Open) $ hsep (pretty0 n :: map (prettyPrec App) args)
  prettyPrec d (PTyCon _ n _ args) =
    parenthesise (d > Open) $ hsep (pretty0 n :: map (prettyPrec App) args)
  prettyPrec d (PConst _ c) = pretty c
  prettyPrec d (PArrow _ _ p q) =
    parenthesise (d > Open) $ pretty p <++> arrow <++> pretty q
  prettyPrec d (PDelay _ _ _ p) = parens ("Delay" <++> pretty p)
  prettyPrec d (PLoc _ n) = pretty0 n
  prettyPrec d (PUnmatchable _ tm) = keyword "." <+> parens (byShow tm)

mutual
  insertCaseNames : SizeOf outer ->
                    SizeOf ns ->
                    CaseTree (outer ++ inner) ->
                    CaseTree (outer ++ (ns ++ inner))
  insertCaseNames outer ns (Case idx prf scTy alts)
      = let MkNVar prf' = insertNVarNames outer ns (MkNVar prf) in
            Case _ prf' (insertNames outer ns scTy)
                (map (insertCaseAltNames outer ns) alts)
  insertCaseNames outer ns (STerm i x) = STerm i (insertNames outer ns x)
  insertCaseNames _ _ (Unmatched msg) = Unmatched msg
  insertCaseNames _ _ Impossible = Impossible

  insertCaseAltNames : SizeOf outer ->
                       SizeOf ns ->
                       CaseAlt (outer ++ inner) ->
                       CaseAlt (outer ++ (ns ++ inner))
  insertCaseAltNames p q (ConCase tag args ct)
      = ConCase tag args
           (rewrite appendAssociative args outer (ns ++ inner) in
                    insertCaseNames (mkSizeOf args + p) q {inner}
                        (rewrite sym (appendAssociative args outer inner) in
                                 ct))
  insertCaseAltNames outer ns (DelayCase tyn valn ct)
      = DelayCase tyn valn
                  (insertCaseNames (suc (suc outer)) ns ct)
  insertCaseAltNames outer ns (ConstCase x ct)
      = ConstCase x (insertCaseNames outer ns ct)
  insertCaseAltNames outer ns (DefaultCase ct)
      = DefaultCase (insertCaseNames outer ns ct)

export
Weaken CaseTree where
  weakenNs ns t = insertCaseNames zero ns t

-- export
-- shrinkCaseTree : Shrinkable CaseTree

-- shrinkCaseAlt : Shrinkable CaseAlt
-- shrinkCaseAlt (ConCase n t args sc) prf
--     = pure $ ConCase n t args !(shrinkCaseTree sc $ keeps args prf)
-- shrinkCaseAlt (DelayCase tyn valn sc) prf
--     = pure $ DelayCase tyn valn !(shrinkCaseTree sc $ Keep $ Keep prf)
-- shrinkCaseAlt (ConstCase c sc) prf = pure $ ConstCase c !(shrinkCaseTree sc prf)
-- shrinkCaseAlt (DefaultCase sc) prf = pure $ DefaultCase !(shrinkCaseTree sc prf)

-- shrinkCaseAlts : Shrinkable (List . CaseAlt)
-- shrinkCaseAlts alts prf = for alts $ flip shrinkCaseAlt prf

-- shrinkCaseTree (Case idx loc scTy alts) prf
--     = do (MkVar loc') <- shrinkIsVar loc prf
--          pure $ Case _ loc' !(shrink scTy prf) !(shrinkCaseAlts alts prf)
-- shrinkCaseTree (STerm i x) prf = pure $ STerm i !(shrink x prf)
-- shrinkCaseTree (Unmatched msg) prf = pure $ Unmatched msg
-- shrinkCaseTree Impossible prf = pure Impossible

export
substCaseTree : Substitutable Var CaseTree

substCaseAlt : Substitutable Var CaseAlt
substCaseAlt sOuter sDropped env (ConCase t args sc)
    = ConCase t args $
        rewrite appendAssociative args outer vars in
          substCaseTree (mkSizeOf args + sOuter) sDropped env $
            rewrite sym $ appendAssociative args outer (dropped ++ vars) in sc
substCaseAlt outer dropped env (DelayCase tyn valn sc)
    = DelayCase tyn valn (substCaseTree (suc $ suc outer) dropped env sc)
substCaseAlt outer dropped env (ConstCase c sc)
    = ConstCase c (substCaseTree outer dropped env sc)
substCaseAlt outer dropped env (DefaultCase sc)
    = DefaultCase (substCaseTree outer dropped env sc)

substCaseAlts : Substitutable Var (List . CaseAlt)
substCaseAlts outer dropped env = map (substCaseAlt outer dropped env)

substCaseTree outer dropped env (Case idx prf scTy alts)
    = do let MkVar p = Subst.find id outer dropped (MkVar prf) env
         Case _ p (substTermVar outer dropped env scTy)
                  (substCaseAlts outer dropped env alts)
substCaseTree outer dropped env (STerm i x)
    = STerm i (substTermVar outer dropped env x)
substCaseTree outer dropped env (Unmatched msg) = Unmatched msg
substCaseTree outer dropped env Impossible = Impossible

total
getNames : (forall vs . NameMap Bool -> Term vs -> NameMap Bool) ->
           NameMap Bool -> CaseTree vars -> NameMap Bool
getNames add ns sc = getSet ns sc
  where
    mutual
      getAltSet : NameMap Bool -> CaseAlt vs -> NameMap Bool
      getAltSet ns (ConCase t args sc) = getSet ns sc
      getAltSet ns (DelayCase t a sc) = getSet ns sc
      getAltSet ns (ConstCase i sc) = getSet ns sc
      getAltSet ns (DefaultCase sc) = getSet ns sc

      getAltSets : NameMap Bool -> List (CaseAlt vs) -> NameMap Bool
      getAltSets ns [] = ns
      getAltSets ns (a :: as) = getAltSets (getAltSet ns a) as

      getSet : NameMap Bool -> CaseTree vs -> NameMap Bool
      getSet ns (Case _ x ty xs) = getAltSets ns xs
      getSet ns (STerm i tm) = add ns tm
      getSet ns (Unmatched msg) = ns
      getSet ns Impossible = ns

export
getRefs : (aTotal : Name) -> CaseTree vars -> NameMap Bool
getRefs at = getNames (addRefs False at) empty

export
addRefs : (aTotal : Name) -> NameMap Bool -> CaseTree vars -> NameMap Bool
addRefs at ns = getNames (addRefs False at) ns

export
getMetas : CaseTree vars -> NameMap Bool
getMetas = getNames (addMetas False) empty

export
mkTerm : (vars : Scope) -> Pat -> Term vars
mkTerm vars (PAs fc x y) = mkTerm vars y
mkTerm vars (PCon fc x tag arity xs)
    = apply fc (Ref fc (DataCon tag arity) x)
               (map (mkTerm vars) xs)
mkTerm vars (PTyCon fc x arity xs)
    = apply fc (Ref fc (TyCon arity) x)
               (map (mkTerm vars) xs)
mkTerm vars (PConst fc c) = PrimVal fc c
mkTerm vars (PArrow fc x s t)
    = Bind fc x (Pi fc top Explicit (mkTerm vars s)) (mkTerm (x :: vars) t)
mkTerm vars (PDelay fc r ty p)
    = TDelay fc r (mkTerm vars ty) (mkTerm vars p)
mkTerm vars (PLoc fc n)
    = case isVar n vars of
           Just (MkVar prf) => Local fc Nothing _ prf
           _ => Ref fc Bound n
mkTerm vars (PUnmatchable fc tm) = embed tm

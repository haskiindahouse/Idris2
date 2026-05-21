module Core.Case.Optimise

import Core.Name.Scoped
import Core.TT.Primitive
import Core.TT.Subst
import Core.TT.Var
import public Core.Case.CaseTree

import Data.Maybe
import Data.List
import Libraries.Data.List.Extra
import Libraries.Data.List.LengthMatch
import Libraries.Data.List.SizeOf

mkSubst : {vars : _} -> (args : List (Var vars)) ->
          (0 _ : LengthMatch args dropped) -> Subst Var dropped vars
mkSubst [] NilMatch = []
mkSubst (x :: xs) (ConsMatch m) = x :: mkSubst xs m

data MatchedPattern : Scoped where
    ConMatched     : ConTag -> List (Var vars) -> MatchedPattern vars
    DelayMatched   : (ty, arg : Var vars) -> MatchedPattern vars
    ConstMatched   : Constant -> MatchedPattern vars

data UnmatchedPattern : Type where
    ConUnmatched   : List ConTag -> UnmatchedPattern
    ConstUnmatched : List Constant -> UnmatchedPattern

data MatchResult : Scoped where
    Matched : MatchedPattern vars -> MatchResult vars
    Unmatched : UnmatchedPattern -> MatchResult vars

Weaken MatchedPattern where
  weakenNs s (ConMatched tag args) = ConMatched tag (weakenNs s <$> args)
  weakenNs s (DelayMatched ty arg) = DelayMatched (weakenNs s ty) (weakenNs s arg)
  weakenNs s (ConstMatched c) = ConstMatched c

Weaken MatchResult where
  weakenNs s (Matched p) = Matched (weakenNs s p)
  weakenNs _ (Unmatched p) = Unmatched p

destructMatchResult : Maybe (MatchResult vars) ->
                      Either (MatchedPattern vars) (Maybe UnmatchedPattern)
destructMatchResult (Just (Matched p)) = Left p
destructMatchResult (Just (Unmatched p)) = Right (Just p)
destructMatchResult Nothing = Right Nothing

addUnmatchedCon : ConTag -> Maybe UnmatchedPattern -> Maybe UnmatchedPattern
addUnmatchedCon tag Nothing = Just $ ConUnmatched [tag]
addUnmatchedCon tag (Just (ConUnmatched cs))
    = toMaybe (not $ tag `elem` cs) $ ConUnmatched (tag :: cs)
addUnmatchedCon _ (Just (ConstUnmatched _)) = Nothing -- shouldn't happen

addUnmatchedConst : Constant -> Maybe UnmatchedPattern -> Maybe UnmatchedPattern
addUnmatchedConst c Nothing = Just $ ConstUnmatched [c]
addUnmatchedConst c (Just (ConstUnmatched cs))
    = toMaybe (not $ c `elem` cs) $ ConstUnmatched (c :: cs)
addUnmatchedConst _ (Just (ConUnmatched _)) = Nothing -- shouldn't happen

export
optimiseTree : {vars : _} -> List (Var vars, MatchResult vars) -> CaseTree vars -> Maybe (CaseTree vars)

optimiseAlts : {vars : _} -> List (Var vars, MatchResult vars) ->
               Var vars -> Maybe UnmatchedPattern -> List (CaseAlt vars) ->
               (List (CaseAlt vars), Maybe (CaseTree vars))
optimiseAlts ps v _ [] = ([], Nothing)
optimiseAlts ps v p (ConCase tag args sc :: alts)
    = do let Just p' = addUnmatchedCon tag p
           | _ => optimiseAlts ps v p alts -- unreachable case
         let sz = mkSizeOf args
         let v' = weakenNs sz v
         let args' = allVarsPrefix sz
         let ps' = map (bimap (weakenNs sz) (weakenNs sz)) ps
         let ps'' = (v', Matched $ ConMatched tag args') :: ps'
         let alt = ConCase tag args <$> optimiseTree ps'' sc
         mapFst (mcons alt) (optimiseAlts ps v (Just p') alts)
optimiseAlts ps v p (DelayCase ty arg sc :: alts)
    = do let sz = mkSizeOf [ty, arg]
         let v' = weakenNs sz v
         let ps' = map (bimap (weakenNs sz) (weakenNs sz)) ps
         let ps'' = (v', Matched $ DelayMatched first (later first)) :: ps'
         let alt = DelayCase ty arg <$> optimiseTree ps'' sc
         mapFst (mcons alt) (optimiseAlts ps v p alts)
optimiseAlts ps v p (ConstCase c sc :: alts)
    = do let Just p' = addUnmatchedConst c p
           | _ => optimiseAlts ps v p alts -- unreachable case
         let ps' = (v, Matched $ ConstMatched c) :: ps
         let alt = ConstCase c <$> optimiseTree ps' sc
         mapFst (mcons alt) (optimiseAlts ps v (Just p') alts)
optimiseAlts ps v p (DefaultCase sc :: _)
    = ([], optimiseTree ((v,) . Unmatched <$> p `mcons` ps) sc)

pickAlt : {vars : _} -> List (Var vars, MatchResult vars) ->
          MatchedPattern vars -> List (CaseAlt vars) -> Maybe (CaseTree vars)
pickAlt _ _ [] = Nothing
pickAlt ps p@(ConMatched t args) (ConCase t' args' sc :: alts)
    = if t == t'
         then do match <- checkLengthMatch args args' -- lengths should always match
                 optimiseTree ps $ substCaseTree zero (mkSizeOf _) (mkSubst args match) sc
         else pickAlt ps p alts
pickAlt ps (DelayMatched ty arg) (DelayCase ty' arg' sc :: _)
    = do let subst : Subst Var [ty', arg'] vars = mkSubst [ty, arg] %search
         optimiseTree ps $ substCaseTree zero (mkSizeOf _) subst sc
pickAlt ps p@(ConstMatched c) (ConstCase c' sc :: alts)
    = if c == c'
         then optimiseTree ps sc
         else pickAlt ps p alts
pickAlt ps _ (DefaultCase sc :: _) = optimiseTree ps sc
pickAlt ps p (_ :: alts) = pickAlt ps p alts

optimiseTree ps (Case idx el ty alts)
    = do let var = MkVar el
         case destructMatchResult $ lookup var ps of
           Left p => pickAlt ps p alts
           Right p => case optimiseAlts ps var p alts of
                           ([], def) => def
                           (alts, Nothing) => Just $ Case idx el ty alts
                           (alts, Just def@(Case idx' _ _ alts')) =>
                               Just $ Case idx el ty $ alts ++
                                 if idx == idx' then alts' else [DefaultCase def]
                           (alts, Just def) =>
                               Just $ Case idx el ty $ alts ++ [DefaultCase def]
optimiseTree _ tm = Just tm

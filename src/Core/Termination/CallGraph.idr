module Core.Termination.CallGraph

import Core.Context.Log
import Core.Env
import Core.Options
import Core.Evaluate.Value
import Core.Evaluate.Normalise
import Core.Evaluate
import Core.Name.CompatibleVars

import Data.String
import Data.SnocList.Quantifiers

import Libraries.Data.SnocList.SizeOf
import Libraries.Data.SparseMatrix
import Data.SortedMap
import Data.Vect

%default covering

-- Drop any non-inf top level laziness annotations
-- Remove all force and delay annotations which are nothing to do with
-- coinduction meaning that all Delays left guard coinductive calls.
dropLazy : Value f vars -> Core (Glued vars)
dropLazy val@(VDelayed _ r t)
    = case r of
           LInf => pure (asGlued val)
           _ => pure t
dropLazy val@(VDelay _ r t v)
    = case r of
           LInf => pure (asGlued val)
           _ => pure v
dropLazy val@(VForce fc r v sp)
    = case r of
           LInf => pure (asGlued val)
           _ => applyAll fc v (cast (map (\ e => (multiplicity e, value e)) sp))
dropLazy val = pure (asGlued val)

scEq : Value f vars -> Value f' vars -> Core Bool

scEqSpine : Spine vars -> Spine vars -> Core Bool
scEqSpine [<] [<] = pure True
scEqSpine (sp :< x) (sp' :< y)
    -- erased (Rig0) spine args (e.g. type parameters) are irrelevant to
    -- size-change, and may legitimately differ structurally (a concrete type
    -- vs a pattern variable), so skip them when comparing for equality
    = if isErased x.multiplicity
         then scEqSpine sp sp'
         else do x' <- value x
                 y' <- value y
                 if !(scEq x' y')
                    then scEqSpine sp sp'
                    else pure False
scEqSpine _ _ = pure False

-- Approximate equality between values. We don't go under binders - we're
-- only checking for size change equality so expect to just see type and
-- data constructors
-- TODO: size change for pattern matching on types
scEq' : Value f vars -> Value f' vars -> Core Bool
scEq' (VApp _ _ n sp _) (VApp _ _ n' sp' _)
    = if n == n'
         then scEqSpine sp sp'
         else pure False
-- Should never see this since we always call with vars = [<], but it is
-- technically possible
scEq' (VLocal _ idx _ sp) (VLocal _ idx' _ sp')
    = if idx == idx'
         then scEqSpine sp sp'
         else pure False
scEq' (VDCon _ _ t a sp) (VDCon _ _ t' a' sp')
    = if t == t'
         then scEqSpine sp sp'
         else pure False
scEq' (VTCon _ n a sp) (VTCon _ n' a' sp')
    = if n == n'
         then scEqSpine sp sp'
         else pure False
scEq' (VMeta _ _ i _ args _) (VMeta _ _ i' _ args' _)
   -- = i == i' && assert_total (all (uncurry scEq) (zip args args'))
   = pure $ i == i' && assert_total !(allM (uncurry scEq) !paired_values)
   where
     paired_values : Core (SnocList (Value Glue vars, Value Glue vars))
     paired_values = traverse (\(a, a') => pure (!a, !a')) (zip (map value args) (map value args'))
scEq' (VAs _ _ a p) p' = pure $ !(scEq p p') || !(scEq p a)
scEq' p (VAs _ _ a p') = pure $ !(scEq p a) || !(scEq p p')
scEq' (VDelayed _ _ t) (VDelayed _ _ t') = scEq t t'
scEq' (VDelay _ _ t x) (VDelay _ _ t' x')
     = if !(scEq t t') then scEq x x'
          else pure False
scEq' (VForce _ _ t [<]) (VForce _ _ t' [<]) = scEq t t'
scEq' (VPrimVal _ c) (VPrimVal _ c') = pure $ c == c'
-- traverse dotted LHS terms
scEq' t (VErased _ (Dotted t')) = scEq t t' -- t' is no longer a pattern
--scEq' (VErased _ _) (VErased _ _) = pure True
scEq' (VErased _ _) (VErased _ _) = pure True
scEq' (VUnmatched _ _) (VUnmatched _ _) = pure True
scEq' (VType _ _) (VType _ _) = pure True
scEq' _ _ = pure False -- other cases not checkable

scEq x y = scEq' !(dropLazy x) !(dropLazy y)

data Guardedness = Toplevel | Unguarded | Guarded | InDelay

Show Guardedness where
  show Toplevel = "Toplevel"
  show Unguarded = "Unguarded"
  show Guarded = "Guarded"
  show InDelay = "InDelay"

knownOr : Core SizeChange -> Core SizeChange -> Core SizeChange
knownOr x y = case !x of Unknown => y; _ => x

plusLazy : Core SizeChange -> Core SizeChange -> Core SizeChange
plusLazy x y = case !x of Smaller => pure Smaller; x => pure $ x |+| !y

-- Return whether first argument is structurally smaller than the second.
sizeCompare : {auto c : Ref Ctxt Defs} ->
              {auto defs : Defs} ->
              Nat -> -- backtracking fuel
              Glued [<] -> -- RHS: term we're checking
              Glued [<] -> -- LHS: argument it might be smaller than
              Core SizeChange

sizeCompareCon : {auto c : Ref Ctxt Defs} -> {auto defs : Defs} -> Nat -> Glued [<] -> Glued [<] -> Core Bool
sizeCompareTyCon : {auto c : Ref Ctxt Defs} -> {auto defs : Defs} -> Nat -> Glued [<] -> Glued [<] -> Core Bool
sizeCompareConArgs : {auto c : Ref Ctxt Defs} -> {auto defs : Defs} -> Nat -> Glued [<] -> List (Glued [<]) -> Core Bool
sizeCompareApp : {auto c : Ref Ctxt Defs} -> {auto defs : Defs} -> Nat -> Glued [<] -> Glued [<] -> Core SizeChange

sizeCompare fuel s (VErased _ (Dotted t)) = sizeCompare fuel s t
sizeCompare fuel _ (VErased _ _) = pure Unknown -- incomparable!
-- for an as pattern, it's smaller if it's smaller than either part
sizeCompare fuel s (VAs _ _ p t)
    = knownOr (sizeCompare fuel s p) (sizeCompare fuel s t)
sizeCompare fuel (VAs _ _ p s) t
    = knownOr (sizeCompare fuel p t) (sizeCompare fuel s t)
-- if they're both metas, let scEq check if they're the same
sizeCompare fuel s@(VMeta _ _ _ _ _ _) t@(VMeta _ _ _ _ _ _) = pure (if !(scEq s t) then Same else Unknown)
-- otherwise try to expand RHS meta
sizeCompare fuel s@(VMeta _ n i args _ _) t = do
  Just gdef <- lookupCtxtExact (Resolved i) (gamma defs) | _ => pure Unknown
  let (Function _ tm _ _) = definition gdef | _ => pure Unknown
  tm <- substMeta (embed tm) !(traverse snd args) zero [<]
  sizeCompare fuel tm t
  where
    substMeta : {0 drop : _} ->
                Term (Scope.addInner Scope.empty drop) -> List (Glued Scope.empty) ->
                SizeOf drop -> Subst Glued drop Scope.empty ->
                Core (Glued Scope.empty)
    substMeta (Bind bfc n (Lam _ c e ty) sc) (a :: as) drop env
        = substMeta sc as (suc drop) (env :< a)
    substMeta (Bind bfc n (Let _ c val ty) sc) as drop env
        = substMeta (subst val sc) as drop env
    substMeta rhs [] drop env = (nf [<] (substs drop !(to_env env) rhs))
      where
        to_env : {0 drop : _} -> Subst Glued drop Scope.empty -> Core (SubstEnv drop Scope.empty)
        to_env [<] = pure [<]
        to_env (as :< a) = pure $ !(to_env as) :< !(quote [<] a)
    substMeta rhs _ _ _ = throw (InternalError ("Badly formed metavar solution \{show n}"))

sizeCompare fuel s t
   = if !(sizeCompareTyCon fuel s t) then pure Same
     else if !(sizeCompareCon fuel s t)
        then pure Smaller
        else knownOr (sizeCompareApp fuel s t) (pure $ if !(scEq s t) then Same else Unknown)

sizeCompareProdConArgs : {auto c : Ref Ctxt Defs} -> {auto defs : Defs} -> Nat -> List (Glued [<]) -> List (Glued [<]) -> Core SizeChange
sizeCompareProdConArgs _ [] [] = pure Same
sizeCompareProdConArgs fuel (x :: xs) (y :: ys) =
  case !(sizeCompare fuel x y) of
    Unknown => pure Unknown
    t => (t |*|) <$> sizeCompareProdConArgs fuel xs ys
sizeCompareProdConArgs _ _ _ = pure Unknown

sizeCompareTyCon fuel s t =
  case t of
    VTCon _ cn _ args => case s of
      VTCon _ cn' _ args' => if cn == cn'
          then (Unknown /=) <$> sizeCompareProdConArgs fuel (toList !(traverseSnocList value args')) (toList !(traverseSnocList value args))
          else pure False
      _ => pure False
    _ => pure False

sizeCompareCon fuel s t
    = case t of
           VDCon _ cn _ _ sp =>
            do
              sp_value <- toList <$> traverseSnocList value sp
              -- if s is smaller or equal to an arg, then it is smaller than t
              if !(sizeCompareConArgs (minus fuel 1) s sp_value) then pure True
               else case (fuel, s) of
                      (S k, VDCon _ cn' _ _ sp') => do
                              -- if s is a matching DataCon, applied to same number of args,
                              -- no Unknown args, and at least one Smaller
                              if cn == cn' && length sp == length sp'
                                then (Smaller ==) <$> sizeCompareProdConArgs k (toList !(traverseSnocList value sp')) sp_value
                                else pure False
                      _ => pure $ False
           _ => pure False

sizeCompareConArgs _ s [] = pure False
sizeCompareConArgs fuel s (t :: ts)
    = case !(sizeCompare fuel s t) of
        Unknown => sizeCompareConArgs fuel s ts
        _ => pure True

sizeCompareApp fuel l@(VApp _ _ n sp _) r@(VApp _ _ n' sp' _)
 = if n == n'
     then if length sp == length sp'
             then do sp_value <- toList <$> traverseSnocList value sp
                     sp_value' <- toList <$> traverseSnocList value sp'
                     sizeCompareProdConArgs fuel sp_value sp_value'
             else do -- TODO: how to compare detected recursion?
                     -- It is a case like: {arg:0} vs {arg:0} {arg:1}
                     pure Same
     else do pure Unknown
sizeCompareApp _ _ t = pure Unknown

sizeCompareAsserted : {auto c : Ref Ctxt Defs} -> {auto defs : Defs} -> Nat -> Maybe (Glued [<]) -> Glued [<] -> Core SizeChange
sizeCompareAsserted fuel (Just s) t
    = pure $ case !(sizeCompare fuel s t) of
        Unknown => Unknown
        _ => Smaller
sizeCompareAsserted _ Nothing _ = pure Unknown

-- Substitute a name with what we know about it.
-- We assume that the name has come from a case pattern, which means we're
-- not going to have to look under binders.
-- We also assume that (despite the 'Glued') it's always a VDCon or VDelay
-- therefore no need to expand apps.
substNameInVal : Name -> Glued vars -> Glued vars -> Core (Glued vars)
-- Only interested in Bound names (that we just made) and so we only need
-- to check the index
substNameInVal (MN _ i') rep tm@(VApp _ Bound (MN _ i) _ _)
    = if i == i' then pure rep else pure tm
substNameInVal n rep (VDCon fc cn t a sp)
    = pure $ VDCon fc cn t a !(substNameInSpine sp)
  where
    substNameInSpine : Spine vars -> Core (Spine vars)
    substNameInSpine [<] = pure [<]
    substNameInSpine (rest :< MkSpineEntry fc c arg)
        = do rest' <- substNameInSpine rest
             -- strict: compute the substituted argument now instead of
             -- stacking a pending-substitution thunk per refinement level
             -- (with deep patterns the stacked layers made every force
             -- re-run the whole stack: part of the ~n^4.5 getSC cliff)
             arg' <- substNameInVal n rep !arg
             pure (rest' :< MkSpineEntry fc c (pure arg'))
substNameInVal n rep (VDelay fc r t v)
    = pure $ VDelay fc r !(substNameInVal n rep t) !(substNameInVal n rep v)
substNameInVal n rep tm = pure tm

replaceInArgs : Name -> Glued [<] ->
                List (Nat, Glued [<]) -> Core (List (Nat, Glued [<]))
replaceInArgs v tm [] = pure []
-- REPLACE the entry with its refined form rather than appending a refined
-- copy: appending grew the pattern list by one entry per case level, which
-- (together with re-scanning and re-comparing every entry per level) made
-- getSC ~n^4.5 in pattern depth — a 'foo 1000 = ()' literal pattern took
-- hours. The relation the stale entry used to provide (RHS call args that
-- still mention the pre-split variable) is preserved instead by recording
-- the split as a forced equation (see findSCscope/findSCalt/Let-As below):
-- findSCcall canonicalises call arguments with those equations, so they are
-- compared in the same refined view as the (replaced) pattern entries.
replaceInArgs v tm ((n, arg) :: args)
    = pure $ (n, !(substNameInVal v tm arg)) :: !(replaceInArgs v tm args)

expandForced : List (Glued [<], Glued [<]) ->
               List (Nat, Glued [<]) -> Core (List (Nat, Glued [<]))
expandForced [] args = pure args
-- Only useful if the equality evaluated to a bound name that we know about
expandForced ((VApp _ Bound n _ _, tm) :: fs) args
    = expandForced fs !(replaceInArgs n tm args)
expandForced (_ :: fs) args = expandForced fs args

data SCVar : Type where

mkvar : Int -> Value f [<]
mkvar i = vRef EmptyFC Bound (MN "scv" i)

nextVar : {auto c : Ref SCVar Int} -> Core (Value f [<])
nextVar
    = do v <- get SCVar
         put SCVar (v + 1)
         pure (mkvar v)

ForcedEqs : Type
ForcedEqs = List (Glued [<], Glued [<])

findVar : Int -> List (Glued vars, Glued vars) -> Maybe (Glued vars)
findVar i [] = Nothing
findVar i ((VApp _ Bound (MN _ i') _ _, tm) :: eqs)
    = if i == i' then Just tm else findVar i eqs
findVar i (_ :: eqs) = findVar i eqs

canonicalise : List (Glued vars, Glued vars) -> Glued vars -> Core (Glued vars)
canonicalise eqs tm@(VApp _ Bound (MN _ i) _ _)
    = case findVar i eqs of
           Nothing => pure tm
           Just val => canonicalise eqs val
canonicalise eqs (VDCon fc cn t a sp)
    = pure $ VDCon fc cn t a !(canonSp sp)
  where
    canonSp : Spine vars -> Core (Spine vars)
    canonSp [<] = pure [<]
    canonSp (rest :< MkSpineEntry fc c arg)
        = do rest' <- canonSp rest
             -- strict, for the same reason as substNameInSpine
             arg' <- canonicalise eqs !arg
             pure (rest' :< MkSpineEntry fc c (pure arg'))
-- for matching on types, convert to the form the case tree builder uses
canonicalise eqs (VPrimVal fc (PrT c))
    = pure $ (VTCon fc (UN (Basic $ show c)) 0 [<])
canonicalise eqs (VType fc _)
    = pure $ (VTCon fc (UN (Basic "Type")) 0 [<])
-- canonicalisation is the only refinement mechanism for pattern views now,
-- so it must see through laziness like the old entry substitution did:
-- refine under Delay, and collapse Force(Delay x) (e.g. an as-pattern over
-- a Lazy field shows up as %Force of the delayed variable)
canonicalise eqs (VDelay fc r t v)
    = pure $ VDelay fc r !(canonicalise eqs t) !(canonicalise eqs v)
canonicalise eqs (VForce fc r v [<])
    = do v' <- canonicalise eqs v
         case v' of
           VDelay _ _ _ val => pure val
           _ => pure $ VForce fc r v' [<]
canonicalise eqs val = pure val

-- Match a constructor pattern whose leaves are fresh pattern variables
-- against an existing refined view of the same value, yielding equations
-- binding those fresh variables to the corresponding subterms of the view.
-- Used when a case tree re-examines an already-refined variable (clause
-- RHS duplication does this), see recordSplit. On constructor clash
-- (unreachable branch) no equations are produced.
matchPat : Glued [<] -> Glued [<] -> Core ForcedEqs
matchPat p (VAs _ _ _ t) = matchPat p t
matchPat p@(VApp _ Bound (MN _ _) [<] _) t = pure [(p, t)]
-- symmetric case: the existing view is still an unrefined variable where the
-- new pattern/reconstruction is deeper: refine the view var (the old entry
-- substitution materialised this refinement into the entry list)
matchPat p t@(VApp _ Bound (MN _ _) [<] _) = pure [(t, p)]
matchPat (VDCon _ _ t a sp) (VDCon _ _ t' a' sp')
    = if t == t' && length sp == length sp'
         then matchSp sp sp'
         else pure []
  where
    matchSp : Spine [<] -> Spine [<] -> Core ForcedEqs
    matchSp [<] [<] = pure []
    matchSp (sp :< e) (sp' :< e')
        = do rest <- matchSp sp sp'
             ms <- matchPat !(value e) !(value e')
             pure (ms ++ rest)
    matchSp _ _ = pure []
matchPat (VDelay _ _ t v) (VDelay _ _ t' v')
    = pure (!(matchPat t t') ++ !(matchPat v v'))
matchPat _ _ = pure []

-- Record a case split (v = pat) in the forced-equation list, so that call
-- arguments mentioning v (or pat's fresh pattern variables) canonicalise to
-- the refined pattern view: this replaces the old stale-entry mechanism
-- (replaceInArgs used to append the refined entry, keeping the pre-split
-- one). On the FIRST split of v, record (v -> pat). If v already has a
-- refined view (the tree re-examines an already-split variable), do NOT
-- shadow it: bind pat's fresh pattern variables against the existing view
-- instead, so the new names canonicalise into the already-refined form.
recordSplit : Name -> Glued [<] -> ForcedEqs -> List (Nat, Glued [<]) ->
              Core (ForcedEqs, List (Nat, Glued [<]))

-- Merge a scope-yielded forced-equality list (dotted/forced matches) into
-- the accumulated equations. Plain (eqsc ++ eqs) let a clause-RHS-duplicate
-- scope re-match SHADOW an already-refined variable with a shallow
-- reconstruction (fresh unrefined vars), losing relations the old
-- materialised-entry mechanism kept (deptycheck Gen <**> with-block SCC:
-- weak duplicate edges broke SCT). Route var-headed equalities through
-- recordSplit: first binding is recorded on the canonical var, re-bindings
-- are matched against the existing view instead of shadowing it.
mergeEqs : ForcedEqs -> ForcedEqs -> List (Nat, Glued [<]) ->
           Core (ForcedEqs, List (Nat, Glued [<]))

-- Append `pat` as an ADDITIONAL entry copy for every pattern-entry position
-- whose stored value is exactly the variable v. Used when a value is
-- RE-matched (clause-RHS duplication walks the same RHS under several case
-- paths): the new pattern view can be structurally unrelated to the already
-- recorded view of v (a different clause's shape), so a single canonical
-- view cannot carry both — the old materialised-entry mechanism kept every
-- refined copy and took relations from whichever view matched. Bounded by
-- re-match events (NOT pattern depth: a first split of v sees a bare
-- canonical view and only records an equation), so the deep-pattern cliff
-- fix is unaffected.
addEntryCopies : Name -> Glued [<] -> List (Nat, Glued [<]) -> List (Nat, Glued [<])
addEntryCopies v pat [] = []
addEntryCopies v pat ((n, e) :: rest)
    = case e of
        VApp _ Bound v' [<] _ =>
          if v' == v
             then (n, e) :: (n, pat) :: addEntryCopies v pat rest
             else (n, e) :: addEntryCopies v pat rest
        _ => (n, e) :: addEntryCopies v pat rest

recordSplit v pat eqs args
    = do cur <- canonicalise eqs (vRef EmptyFC Bound v)
         case cur of
           -- key the eq on the CANONICAL var (the alias-chain end), not on v:
           -- when a case tree re-splits an already-split value (clause RHS
           -- duplication), the new scrutinee var is an alias of the original
           -- (matchPat records new->old); keying on v would leave the OLD var
           -- (the one existing pattern views still mention) unbound, so those
           -- views would dead-end un-refined (e.g. a re-forced lazy tail stuck
           -- at %Delay v: deptycheck positive-nat pickWeighted false not-total).
           -- cur is canonical, hence eq-free: prepending cannot shadow.
           VApp _ Bound _ [<] _ => pure (((cur, pat) :: eqs), args)
           -- re-match: bind the new pattern's fresh leaves against the
           -- existing view, and keep the new view available as an extra
           -- entry copy (see addEntryCopies)
           _ => pure ((!(matchPat pat cur) ++ eqs), addEntryCopies v pat args)

mergeEqs [] eqs args = pure (eqs, args)
mergeEqs ((l, r) :: rest) eqs args
    = do (eqs', args') <- mergeEqs rest eqs args
         case l of
           VApp _ Bound n [<] _ => recordSplit n r eqs' args'
           _ => pure (((l, r) :: eqs'), args')

mutual
  findSC : {auto c : Ref Ctxt Defs} ->
           {auto v : Ref SCVar Int} ->
           Guardedness ->
           ForcedEqs ->
           List (Nat, Glued [<]) -> -- LHS args and their position
           Glued [<] -> -- definition. No expanding to NF, we want to check
                        -- the program as written (plus tcinlines)
           Core (List SCCall)
  -- If we're Guarded and find a Delay, continue with the argument as InDelay
  findSC Guarded eqs args (VDelay _ LInf _ tm)
      = findSC InDelay eqs args tm
  findSC g eqs args (VBind _ _ (Lam _ _ _ _) sc)
      = findSC g eqs args !(sc nextVar)
  findSC g eqs args (VBind _ _ (Let _ erased (VAs _ UseRight (VApp _ Bound n [<] _) as) _) sc)
      = do -- record the alias as an equation: comparisons canonicalise both
           -- call arguments and pattern entries through eqs (see mkChange),
           -- which replaces the old materialised stale-entry mechanism
           (eqs', args') <- recordSplit n as eqs args
           -- No mix the following: $ !(findSC g eqs args as) ++ !(findSC g eqs args' !(sc nextVar))
           -- because `as` came from erased, so, no actual structural decrease
           findSC g eqs' args' !(sc nextVar)
  findSC g eqs args (VBind fc n b sc)
      = do v <- nextVar
           pure $ !(findSCbinder b) ++ !(findSC g eqs args !(sc (pure v)))
    where
        findSCbinder : Binder (Glued [<]) -> Core (List SCCall)
        findSCbinder (Let _ c val ty) = findSC g eqs args val
        findSCbinder _ = pure [] -- only types, no need to look
  findSC g eqs args (VDelay _ _ _ tm)
      = findSC g eqs args tm
  findSC g eqs args (VForce _ _ v sp)
      = do vCalls <- findSC Unguarded eqs args v
           spCalls <- findSCspine Unguarded eqs args sp
           pure (vCalls ++ spCalls)
  findSC g eqs args tm@(VCase fc ct c (VApp _ Bound n [<] _) scTy alts)
      = do logNF "totality.termination.sizechange" 50 "findSC VCase VApp Bound ct=\{show ct} tm" [<] tm
           altCalls <- traverse (findSCalt g eqs args (Just n)) alts
           pure (concat altCalls)
  findSC g eqs args tm@(VCase _ ct c (VApp fc Func fn sp _) scTy alts)
      = do logNF "totality.termination.sizechange" 50 "findSC VCase VApp Func ct=\{show ct} tm" [<] tm
           scCalls <- findSCAppFunc g eqs args fc fn sp

           altCalls <- traverse (findSCalt g eqs args Nothing) alts
           pure (scCalls ++ concat altCalls)

  findSC g eqs args tm@(VCase fc ct c sc scTy alts)
      = do logNF "totality.termination.sizechange" 50 "findSC VCase VApp ? ct=\{show ct} tm" [<] tm
           altCalls <- logDepth $ traverse (findSCalt g eqs args Nothing) alts
           logC "totality.termination.sizechange" 50 $ pure "findSC VCase VApp ? altCalls: \{show altCalls}"
           scCalls <- logDepth $ findSC Unguarded eqs args (asGlued sc)
           logC "totality.termination.sizechange" 50 $ pure "findSC VCase VApp ? scCalls: \{show scCalls}"
           pure (scCalls ++ concat altCalls)
  findSC g eqs args tm = do
    logNF "totality.termination.sizechange" 50 "findSC findSCapp tm g=\{show g}" [<] tm
    findSCapp g eqs args tm

  findSCAppFunc : {auto c : Ref Ctxt Defs} ->
                  {auto v : Ref SCVar Int} ->
                  Guardedness ->
                  ForcedEqs ->
                  List (Nat, Glued [<]) -> -- LHS args and their position
                  FC -> Name -> Spine [<] ->
                  Core (List SCCall)
  findSCAppFunc g eqs args fc fn sp = do
      let False = isAssertTotal !(getFullName fn)
        | _ => pure []

      allg <- allGuarded fn

      logC "totality.termination.sizechange" 50 $ pure "findSCAppFunc \{show !(toFullNames fn)}, g=\{show g}, allg=\{show allg}"
      -- If it has the all guarded flag, pretend it's a data constructor
      -- Otherwise just carry on as normal
      if allg
        then findSCapp g eqs args (VDCon fc fn 0 0 sp)
        else case g of
                -- constructor guarded and delayed, so just check the
                -- arguments
                InDelay => findSCspine Unguarded eqs args sp
                _ => do fn_args <- traverseSnocList value sp
                        findSCcall Unguarded eqs args fc fn (cast fn_args)
    where
      isAssertTotal : Name -> Bool
      isAssertTotal = (== NS builtinNS (UN $ Basic "assert_total"))

      allGuarded : Name -> Core Bool
      allGuarded n
          = do defs <- get Ctxt
               Just gdef <- lookupCtxtExact n (gamma defs)
                    | Nothing => pure False
               pure (AllGuarded `elem` flags gdef)

  findSCapp : {auto c : Ref Ctxt Defs} ->
              {auto v : Ref SCVar Int} ->
              Guardedness ->
              ForcedEqs ->
              List (Nat, Glued [<]) -> -- LHS args and their position
              Glued [<] -> -- dealing with cases where this is an application
                           -- of some sort
              Core (List SCCall)
  findSCapp g eqs pats (VLocal fc _ _ sp)
      = do args <- traverseSnocList value sp
           scs <- traverseSnocList (findSC g eqs pats) args
           pure (concat scs)
  findSCapp g eqs pats (VPrimOp _ _ sp)
      = do scs <- traverse (findSC g eqs pats) (toList sp)
           pure (concat scs)
  findSCapp g eqs pats (VApp fc Bound fn sp _)
      = do args <- traverseSnocList value sp
           logC "totality.termination.sizechange" 50 $ pure "findSCapp VApp Bound \{show !(toFullNames fn)}"
           for_ (toList args) $ \a =>
             logNF "totality.termination.sizechange" 50 "findSCapp VApp Bound arg" [<] a
           scs <- traverseSnocList (findSC g eqs pats) args
           pure (concat scs)
  findSCapp g eqs pats (VApp fc Func fn sp _) = findSCAppFunc g eqs pats fc fn sp
  -- If we're InDelay and find a constructor (or a function call which is
  -- guaranteed to return a constructor; AllGuarded set), continue as InDelay
  findSCapp InDelay eqs pats (VDCon fc n t a sp)
      = findSCspine InDelay eqs pats sp
  findSCapp Guarded eqs pats (VDCon fc n t a sp)
      = do defs <- get Ctxt
           findSCcall Guarded eqs pats fc n (toList !(traverseSnocList value sp))
  findSCapp Toplevel eqs pats (VDCon fc n t a sp)
      = do defs <- get Ctxt
           findSCcall Guarded eqs pats fc n (toList !(traverseSnocList value sp))
  findSCapp g eqs pats tm = pure [] -- not an application (TODO: VTCon)


  findSCscope : {auto c : Ref Ctxt Defs} ->
                {auto v : Ref SCVar Int} ->
                Guardedness ->
                ForcedEqs ->
                List (Nat, Glued [<]) -> -- LHS args and their position
                Maybe Name -> -- variable we're splitting on (if it is a variable)
                FC -> Glued [<] ->
                (args : _) -> VCaseScope args [<] -> -- case alternative
                Core (List SCCall)
  findSCscope g eqs args var fc pat [<] sc
     = do (eqsc, rhs) <- sc
          logC "totality.termination.sizechange" 10 $
              (do tms <- traverse (\ (gx, gy) =>
                              pure (!(toFullNames !(quote [<] gx)),
                                    !(toFullNames !(quote [<] gy)))) eqsc
                  teqs <- traverse (\ (gx, gy) =>
                              pure (!(toFullNames !(quote [<] gx)),
                                    !(toFullNames !(quote [<] gy)))) eqs
                  pure ("Force equalities eqsc=\{show tms}, eqs=\{show teqs}"))
          (eqs', argsm) <- mergeEqs eqsc eqs args
          logC "totality.termination.sizechange" 10 $ do
            pat <- toFullNames !(quote [<] pat)
            pure "findSCscope replaceInArgs for var=\{show !(toFullNames var)}, pat=\{show pat}"
          logC "totality.termination.sizechange" 10 $ do
            args <- traverse (\ (a, b) => pure (a, !(toFullNames !(quote [<] b)))) args
            pure "findSCscope replaceInArgs for args=\{show args}"
          -- Record the split as an equation. Pattern entries stay as the
          -- ORIGINAL argument variables for the whole walk; comparisons
          -- canonicalise entries and call arguments through eqs on demand
          -- (mkChange/findSCcall/asserted). This replaces the old mechanism
          -- of materialising refined copies into the entry list, which grew
          -- one stale entry per case level and made getSC ~n^4.5 in pattern
          -- depth (a 'foo 1000 = ()' literal pattern took hours).
          (eqs'', args'') <- maybe (pure (eqs', argsm)) (\v => recordSplit v pat eqs' argsm) var
          logNF "totality.termination.sizechange" 10 "RHS var=\{show !(toFullNames var)}" [<] rhs
          logDepth $ findSC g eqs'' args'' rhs
  findSCscope g eqs args var fc pat (cargs :< (c, xn)) sc
     = do varg <- nextVar
          pat' <- the (Core (Glued [<])) $ case pat of
                    VDCon vfc n t a sp =>
                        pure (VDCon vfc n t a (sp :< MkSpineEntry fc c (pure varg)))
                    _ => throw (InternalError "Not a data constructor in findSCscope")
          logNF "totality.termination.sizechange" 10 "findSCscope varg=\{show varg} xn=\{show xn} pat" [<] pat
          logNF "totality.termination.sizechange" 10 "findSCscope varg=\{show varg} xn=\{show xn} pat'" [<] pat'
          findSCscope g eqs args var fc pat' cargs (sc (pure varg))

  findSCalt : {auto c : Ref Ctxt Defs} ->
              {auto v : Ref SCVar Int} ->
              Guardedness ->
              ForcedEqs ->
              List (Nat, Glued [<]) -> -- LHS args and their position
              Maybe Name -> -- variable we're splitting on (if it is a variable)
              VCaseAlt [<] -> -- case alternative
              Core (List SCCall)
  findSCalt g eqs args var (VConCase fc n t cargs sc)
      = findSCscope g eqs args var fc (VDCon fc n t (length cargs) [<]) _ sc
  findSCalt g eqs args var (VDelayCase fc ty arg tm)
      = do targ <- nextVar
           varg <- nextVar
           let pat = VDelay fc LUnknown varg targ
           (eqsc, rhs) <- tm (pure targ) (pure varg)
           -- record the split equation (see findSCscope). NOTE: thread the
           -- outer eqs through (the old code dropped them here); equations
           -- are now the only carrier of pattern refinement, so dropping
           -- them loses every relation established before a Delay split
           (eqs0, args0) <- mergeEqs eqsc eqs args
           (eqs', args') <- maybe (pure (eqs0, args0)) (\v => recordSplit v pat eqs0 args0) var
           logDepth $ findSC g eqs' args' rhs
  findSCalt g eqs args var (VConstCase fc c tm)
      = do -- record the split equation (see findSCscope)
           (eqs', args') <- maybe (pure (eqs, args)) (\v => recordSplit v (VPrimVal fc c) eqs args) var
           logDepth $ findSC g eqs' args' tm
  findSCalt g eqs args _ (VDefaultCase fc tm) = logDepth $ findSC g eqs args tm


  findSCspine : {auto c : Ref Ctxt Defs} ->
           {auto v : Ref SCVar Int} ->
           Guardedness ->
           ForcedEqs ->
           List (Nat, Glued [<]) -> -- LHS args and their position
           Spine [<] ->
           Core (List SCCall)
  findSCspine g eqs pats [<] = pure []
  findSCspine g eqs pats (sp :< e)
      = do vCalls <- findSC g eqs pats !(value e)
           spCalls <- findSCspine g eqs pats sp
           pure (vCalls ++ spCalls)



  -- if the argument is an 'assert_smaller', return the thing it's smaller than
  asserted : ForcedEqs -> Name -> Glued [<] -> Core (Maybe (Glued [<]))
  asserted eqs aSmaller (VApp _ nt fn [<_, _, e, _] _)
       = if fn == aSmaller
            then Just <$> canonicalise eqs !(value e)
            else pure Nothing
  asserted _ _ _ = pure Nothing

  -- Calculate the size change for the given argument.
  -- i.e., return the size relationship of the given argument with an entry
  -- in 'pats'; the position in 'pats' and the size change.
  -- Nothing if there is no relation with any of them.
  mkChange : {auto c : Ref Ctxt Defs} ->
             ForcedEqs ->
             Name ->
             (pats : List (Nat, Glued [<])) ->
             (arg : Glued [<]) ->
             Core (List SizeChange)
  mkChange eqs aSmaller pats arg
    = do defs <- get Ctxt
         let fuel = defs.options.elabDirectives.totalLimit
         res <- traverse (\(n, p) =>
                  do -- entries are the original argument variables: bring
                     -- them to the current refined pattern view here
                     p' <- canonicalise eqs p
                     pure (n, !(plusLazy (sizeCompareAsserted fuel !(asserted eqs aSmaller arg) p') (sizeCompare fuel arg p')))) pats
         let squashed = fromListWith (|+|) res
         pure $ toList squashed

  findSCcall : {auto c : Ref Ctxt Defs} ->
               {auto v : Ref SCVar Int} ->
               Guardedness ->
               ForcedEqs ->
               List (Nat, Glued [<]) ->
               FC -> Name -> List (Glued [<]) ->
               Core (List SCCall)
  findSCcall g eqs pats fc fn_in args
          -- Under 'assert_total' we assume that all calls are fine, so leave
          -- the size change list empty
        = do args <- traverse (canonicalise eqs) args
             defs <- get Ctxt
             fn <- getFullName fn_in
             logC "totality.termination.sizechange" 10 $ do pure "Looking under \{show fn}"
             aSmaller <- resolved (gamma defs) (NS builtinNS (UN $ Basic "assert_smaller"))
             logC "totality.termination.sizechange" 10 $
                 do under <- traverse (\ (n, t) =>
                                pure (n, !(toFullNames !(quote [<] t)))) pats
                    targs <- traverse (\t => toFullNames !(quote [<] t)) args
                    pure ("Under " ++ show under ++ "\n" ++ "Args " ++ show targs)
             scs <- traverse (\x => logDepth $ findSC g eqs pats x) args
             pure ([MkSCCall fn
                   (fromListList
                        !(traverse (mkChange eqs aSmaller pats) args))
                   fc] ++ concat scs)

findSCTop : {auto c : Ref Ctxt Defs} ->
            {auto v : Ref SCVar Int} ->
            Nat -> List (Nat, Glued [<]) -> Glued [<] -> Core (List SCCall)
findSCTop i args (VBind _ _ (Lam _ _ _ _) sc)
    = do arg <- nextVar
         findSCTop (i + 1) ((i, arg) :: args) !(sc $ pure arg)
findSCTop i args def = findSC Toplevel [] (reverse args) def

getSC : {auto c : Ref Ctxt Defs} ->
        Defs -> Def -> Core (List SCCall)
getSC defs (Function _ tm _ pats)
   = do logTerm "totality.termination.sizechange" 5 "From term" tm
        logC "totality.termination.sizechange" 5 $ pure "From pats \{show !(toFullNames pats)}"
        ntm <- nfTotality [<] tm
        logNF "totality.termination.sizechange" 5 "From tree" [<] ntm
        v <- newRef SCVar 0
        sc <- findSCTop 0 [] ntm
        pure $ nub sc
getSC defs _ = pure []

export
calculateSizeChange : {auto c : Ref Ctxt Defs} ->
                      FC -> Name -> Core (List SCCall)
calculateSizeChange loc n
    = do logC "totality.termination.sizechange" 5 $ do pure $ "Calculating Size Change: " ++ show !(toFullNames n)
         defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => undefinedName loc n
         r <- getSC defs (definition def)
         log "totality.termination.sizechange" 5 $ "Calculated: " ++ show r
         pure r

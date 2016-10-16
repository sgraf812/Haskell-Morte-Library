{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}

module ClosedWellTyped (
    ClosedWellTyped(..)
    ) where

import Bound (Var(..))
import Bound.Name (Name(..))
import Control.Applicative hiding (Const)
import Control.Arrow ((***))
import Control.Monad (guard)
import Data.Text.Lazy (Text)
import Control.Monad.State.Lazy (MonadState, StateT)
import Control.Monad.Trans.Class (lift)
import Morte.Core hiding (Context)
import Prelude hiding (pi)
import Test.QuickCheck (Arbitrary, Gen)

import qualified Bound
import qualified Control.Monad.State.Lazy as State
import qualified Data.Text.Lazy           as Text
import qualified Test.QuickCheck          as QuickCheck

newtype ClosedWellTyped = ClosedWellTyped { unClosedWellTyped :: Expr X }

instance Show ClosedWellTyped where
    show (ClosedWellTyped expr) = Text.unpack (pretty expr)

data Context var where
    Empty :: Context X
    Extend :: Type var -> Context var -> Context (Var () var)

freeVars :: Context var -> [(var, Type var)]
freeVars ctx = case ctx of
    Empty -> []
    Extend ty ctx' -> (B (), F <$> ty) : map (F *** (F <$>)) (freeVars ctx')

data Env var
    = Env
    { bindings :: Context var
    , uniques :: [Text]
    }

freeVars' :: Env var -> [(var, Type var)]
freeVars' = freeVars . bindings

newtype M var a = M { unM :: StateT (Env var) Gen a }
    deriving (Functor, Applicative, Monad, MonadState (Env var))

liftGen :: Gen a -> M var a
liftGen m = M (lift m)

evalM :: M var a -> Env var -> Gen a
evalM m = State.evalStateT (unM m)

instance Arbitrary ClosedWellTyped
  where
    arbitrary = QuickCheck.sized rndExpr

rndExpr :: Int -> Gen ClosedWellTyped
rndExpr n = fmap (ClosedWellTyped . fst) (evalM closed (initEnv n))

initEnv :: Int -> Env X
initEnv n = Env Empty (map (Text.pack . show) [1..n])

withExtend :: Type var -> M (Var () var) a -> M var a
withExtend ty m = do
  env <- State.get
  liftGen (evalM m (env { bindings = Extend ty (bindings env) }))

select
  :: [(Int, M var (Expr var, Expr var), Env var -> Bool)]
  -> M var (Expr var, Expr var)
select wgps = do
    env <- State.get
    m   <- liftGen (QuickCheck.frequency (do
        (weight, generator, predicate) <- wgps
        guard (predicate env)
        return (weight, return generator) ))
    m

scope :: M var a -> M var a
scope f = do
    env <- State.get
    liftGen (evalM f env)

matching :: (b -> Bool)-> [(a, b)] -> Bool
matching matcher = any (matcher . snd)

moreThan :: Int -> [a] -> Bool
moreThan n = not . null . drop n

piFilter :: Eq var => Expr var -> Expr var -> Bool
piFilter t (Pi _ _A _) = _A == t
piFilter _  _          = False

closed :: M X (Expr X, Expr X)
closed =
    select
        [ (20, typeOrKind                       , \_ -> True          )
        , (50, lam (scope typeOrKind) termOrType, moreThan 0 . uniques)
        , (30, app                              , moreThan 1 . uniques)
        ]

termOrType :: Eq var => M var (Expr var, Expr var)
termOrType =
    select
        [ ( 5, type_                            , moreThan 0 . uniques )
        , (50, lam (scope typeOrKind) termOrType, moreThan 0 . uniques )
        , (25, var                              , moreThan 0 . freeVars')
        , (20, app                              ,
            \e  ->  (null       (freeVars' e) && moreThan 1 (uniques e))
                ||  (moreThan 0 (freeVars' e) && moreThan 0 (uniques e)))
        ]

typeOrKind :: Eq var => M var (Expr var, Expr var)
typeOrKind =
    select
        [ (15, return (Const Star,Const Box)   , \_ -> True                         )
        , (20, varWith (== Const Star)         , matching (== Const Star) . freeVars')
        , (15, pi (scope typeOrKind) typeOrKind, moreThan 0               . uniques )
        ]

varWith :: (Expr var -> Bool) -> M var (Expr var, Expr var)
varWith f = do
    env <- State.get
    liftGen (QuickCheck.elements (do
        (x, y) <- freeVars (bindings env)
        guard (f y)
        return (Var x, y) ))

var :: M var (Expr var, Expr var)
var = varWith (\_ -> True)

type_ :: Eq var => M var (Expr var, Expr var)
type_ =
    select
        [ (20, varWith (== Const Star)     , matching (== Const Star) . freeVars')
        , (15, pi (scope typeOrKind) type_ , moreThan 0               . uniques  )
        ]

fresh :: M var Text
fresh = do
    Env ctx (x:xs) <- State.get
    State.put (Env ctx xs)
    return x

lam :: Eq var
    => M var (Expr var, Expr var)
    -> M (Var () var) (Expr (Var () var), Expr (Var () var))
    -> M var (Expr var, Expr var)
lam _AGen bGen = do
    x <- fresh
    (_A, _) <- _AGen
    withExtend _A (do
        (b, bType) <- bGen
        return (Lam (Name x ()) _A (Bound.toScope b), Pi (Name x ()) _A (Bound.toScope bType)))

pi  :: Eq var
    => M var (Expr var, Expr var)
    -> M (Var () var) (Expr (Var () var), Expr (Var () var))
    -> M var (Expr var, Expr var)
pi _AGen _BGen = do
    x <- fresh
    (_A, _) <- _AGen
    withExtend _A (do
        (_B, Const t) <- _BGen
        return (Pi (Name x ()) _A (Bound.toScope _B), Const t))

app :: Eq var => M var (Expr var, Expr var)
app = do
    (_N, _A       ) <- scope termOrType
    let genA = return (_A, Const Star)
    (f , Pi _ _ _B) <- do
        scope
            (select
                [ (40, lam genA termOrType  , moreThan 0             . uniques  )
                , (20, varWith (piFilter _A), matching (piFilter _A) . freeVars')
                ] )
    return (App f _N, Bound.instantiate1 _N _B)

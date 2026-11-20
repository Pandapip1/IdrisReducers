module Transducers.Core

import Control.Monad.State


--------------------------------------------------------------------------------
-- Core (definition of steps, reducers and transducers)
--------------------------------------------------------------------------------

public export
data Status a = Done a | Continue a

export
unStatus : Status a -> a
unStatus (Done a) = a
unStatus (Continue a) = a

export
implementation Functor Status where
  map f (Done a) = Done (f a)
  map f (Continue a) = Continue (f a)

public export
StatelessStep : (acc, x: Type) -> Type
StatelessStep acc x = acc -> x -> acc

public export
Step : (state, acc, x: Type) -> Type
Step state acc x = acc -> x -> State state (Status acc)

public export
record Reducer st acc x where
  constructor MkReducer
  state : st
  runStep : Step st acc x
  complete : st -> acc -> acc

export
terminal : StatelessStep acc x -> Reducer () acc x
terminal fn = MkReducer () step (const id)
  where
    step : acc -> x -> State () (Status acc)
    step acc x = pure $ Continue (fn acc x)

public export
Transducer : (acc, s1, s2, outer, inner: Type) -> Type
Transducer acc s1 s2 outer inner = Reducer s1 acc inner -> Reducer s2 acc outer


--------------------------------------------------------------------------------
-- Helpers to build stateless Reducers and Transducers
--------------------------------------------------------------------------------

export
statelessTransducer : (Step s acc b -> Step s acc a) -> Transducer acc s s a b
statelessTransducer stepTf next =
  MkReducer (state next) (stepTf (runStep next)) (complete next)

export
makeTransducer :
    s'
    -> (Step s acc b -> Step s (s', acc) a)
    -> (Step s acc b -> s' -> acc -> State s acc)
    -> Transducer acc s (s', s) a b
makeTransducer initialState stepTf onComplete next =
  MkReducer (initialState, state next) stepImpl completeImpl
  where
    completeImpl : (s', s) -> acc -> acc
    completeImpl (s', s) acc =
      let acc' = evalState s (onComplete (runStep next) s' acc)
      in complete next s acc'
    stepImpl : acc -> a -> State (s', s) (Status acc)
    stepImpl acc x = do
      (s1', s1) <- get
      let (s1New, result) = runState (stepTf (runStep next) (s1', acc) x) s1
      case result of
        Done (s2', acc') => do
          put (s2', s1New)
          pure (Done acc')
        Continue (s2', acc') => do
          put (s2', s1New)
          pure (Continue acc')

export
statefulTransducer : s' -> (Step s acc b -> Step s (s', acc) a) -> Transducer acc s (s', s) a b
statefulTransducer initState stepTf = makeTransducer initState stepTf onComplete
  where
    onComplete : Step s acc b -> s' -> acc -> State s acc
    onComplete next _ acc = pure acc

export
withState : s -> Status acc -> Status (s, acc)
withState s = map (\acc => (s, acc))


--------------------------------------------------------------------------------
-- Core (Reductions)
--------------------------------------------------------------------------------

export
runSteps : (Foldable t) => {acc, st, x : Type} -> Step st acc x -> acc -> t x -> State st (Status acc)
runSteps step acc xs = foldr stepImpl (pure . id) xs (Continue acc)
  where
    stepImpl : x -> (Status acc -> State st (Status acc)) -> Status acc -> State st (Status acc)
    stepImpl _ nextIteration (Done acc') = pure (Done acc')
    stepImpl x nextIteration (Continue acc') = step acc' x >>= nextIteration

export
reduce : (Foldable t) => Reducer st acc x -> acc -> t x -> acc
reduce step acc =
  uncurry (complete step)
    . (\(s, status) => (s, unStatus status))
    . runState (state step)
    . runSteps (runStep step) acc

export
transduce : (Foldable t) => Transducer acc () s b a -> (acc -> a -> acc) -> acc -> t b -> acc
transduce xf step = reduce (xf (terminal step))

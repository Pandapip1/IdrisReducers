module Transducers.Algorithms


import Control.Monad.State
import Transducers.Core

--------------------------------------------------------------------------------
-- Basic Transducers (stateless)
--------------------------------------------------------------------------------

export
mapping : (a -> b) -> Transducer acc s s a b
mapping fn = statelessTransducer $ \next, acc, outer => next acc (fn outer)

export
filtering : (a -> Bool) -> Transducer acc s s a a
filtering pf = statelessTransducer $
  \next, acc, a =>
    if pf a
      then next acc a
      else pure (Continue acc)

export
catMapping : (Foldable t) => (a -> t b) -> Transducer acc s s a b
catMapping fn = statelessTransducer $
  \next, acc, a => runSteps next acc (fn a)

export
takingWhile : (a -> Bool) -> Transducer acc s s a a
takingWhile p = statelessTransducer $
  \next, acc, a => do
    if p a
      then next acc a
      else pure (Done acc)


--------------------------------------------------------------------------------
-- Basic Transducers (stateful)
--------------------------------------------------------------------------------

export
dropping : Nat -> Transducer acc s (Nat, s) a a
dropping n = statefulTransducer n dropImpl
  where
    dropImpl : Step s acc a -> Step s (Nat, acc) a
    dropImpl next (S n, acc) _ = pure $ Continue (n, acc)
    dropImpl next (Z, acc) a = withState Z <$> next acc a

export
taking : Nat -> Transducer acc s (Nat, s) a a
taking n = statefulTransducer n takeImpl
  where
    takeImpl : Step s acc a -> Step s (Nat, acc) a
    takeImpl next (Z, acc) a = pure (Done (Z, acc))
    takeImpl next (S k, acc) a = withState k <$> next acc a

export
interspersing : a -> Transducer acc s (Bool, s) a a
interspersing separator = statefulTransducer False stepImpl
  where
    stepImpl : Step s acc a -> Step s (Bool, acc) a
    stepImpl next (False, acc) a = withState True <$> next acc a
    stepImpl next (True, acc) a =
      withState True <$> runSteps next acc [separator, a]

export
indexingFrom : Int -> Transducer acc s (Int, s) a (Int, a)
indexingFrom startIndex = statefulTransducer startIndex stepImpl
  where
    stepImpl : Step s acc (Int, a) -> Step s (Int, acc) a
    stepImpl next (n, acc) x = withState (S n) <$> next acc (n, x)

export
indexing : Transducer acc s (Int, s) a (Int, a)
indexing = indexingFrom 0

export
chunksOf : Nat -> Transducer acc s (List a, s) a (List a)
chunksOf chunkSize = makeTransducer [] nextChunk dumpRemaining
  where
    nextChunk : Step s acc (List a) -> Step s (List a, acc) a
    nextChunk next (remaining, acc) x =
      let remaining' = x :: remaining in
      if length remaining' == chunkSize
        then withState [] <$> next acc (reverse remaining')
        else pure $ Continue (remaining', acc)
    dumpRemaining : Step s acc (List a) -> List a -> acc -> State s acc
    dumpRemaining next [] acc = pure acc
    dumpRemaining next remaining acc = unStatus <$> next acc (reverse remaining)

export
deduplicate : (Eq a) => Transducer acc s (Maybe a, s) a a
deduplicate = statefulTransducer Nothing stepImpl
  where
    stepImpl : Step s acc a -> Step s (Maybe a, acc) a
    stepImpl next (oldVal, acc) x =
      if oldVal == Just x
        then pure $ Continue (oldVal, acc)
        else withState (Just x) <$> next acc x

export
groupingBy : (a -> a -> Bool) -> Transducer acc s (List a, s) a (List a)
groupingBy sameGroup = makeTransducer [] stepImpl dumpRemaining
  where
    stepImpl : Step s acc (List a) -> Step s (List a, acc) a
    stepImpl next (previousVals, acc) x =
      case previousVals of
        [] => pure $ Continue ([x], acc)
        (h :: _) => if sameGroup h x
          then pure $ Continue (x :: previousVals, acc)
          else withState [x] <$> next acc (reverse previousVals)
    dumpRemaining : Step s acc (List a) -> List a -> acc -> State s acc
    dumpRemaining next remaining acc =
      if isNil remaining
        then pure acc
        else unStatus <$> next acc (reverse remaining)


--------------------------------------------------------------------------------
-- Higher order transducers
--------------------------------------------------------------------------------

public export
record Iso a b where
  constructor MkIso
  toIso : a -> b
  fromIso : b -> a

export
under : Iso a b -> Transducer acc s1 s2 b b -> Transducer acc s1 s2 a a
under iso xf = mapping (toIso iso) . xf . mapping (fromIso iso)

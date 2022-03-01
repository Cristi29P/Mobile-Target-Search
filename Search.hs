{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Search where

import ProblemState
import qualified Data.PSQueue as PQ
import Data.Maybe
import Prelude
import qualified Data.Set as S
import Data.List

{-
    *** TODO ***
    Tipul unei nod utilizat în procesul de căutare. Recomandăm reținerea unor
    informații legate de:
    * stare;
    * acțiunea care a condus la această stare;
    * nodul părinte, prin explorarea căruia a fost obținut nodul curent;
    * adâncime;
    * estimarea costului până la starea finală;
    * copiii, ce vor desemna stările învecinate;
-}

data Node s a = TreeNode {
                        state :: s,
                        action :: Maybe a,
                        parent :: Maybe (Node s a),
                        depth :: Int,
                        children :: [Node s a],
                        heuristic :: Float
                        }

{-
    *** TODO ***
    Instanțiați Eq și Ord pe baza stării.
-}

instance Eq s => Eq (Node s a) where
    (TreeNode a _ _ _ _ _) == (TreeNode b _ _ _ _ _) = a == b

instance Ord s => Ord (Node s a) where
    (TreeNode a _ _ _ _ _) <= (TreeNode b _ _ _ _ _) = a <= b

{-
    *** TODO ***
    Gettere folosite pentru accesul la câmpurile nodului
-}

nodeState :: Node s a -> s
nodeState (TreeNode currState _ _ _ _ _) = currState

nodeParent :: Node s a -> Maybe (Node s a)
nodeParent (TreeNode _ _ currParent _ _ _) = currParent

nodeDepth :: Node s a -> Int
nodeDepth (TreeNode _ _ _ currDepth _ _) = currDepth

nodeChildren :: Node s a -> [Node s a]
nodeChildren (TreeNode _ _ _ _ currChildren _) = currChildren

nodeHeuristic :: Node s a -> Float
nodeHeuristic (TreeNode _ _ _ _ _ currHeuristic) = currHeuristic

nodeAction :: Node s a -> Maybe a
nodeAction (TreeNode _ currAction _ _ _ _) = currAction

{-
    *** TODO ***
    Generarea întregului spațiu al stărilor.
    Primește starea inițială și creează nodul corespunzător acestei stări,
    având drept copii nodurile succesorilor stării curente, și așa mai
    departe, recursiv.
-}

recursiveChildren :: (ProblemState s a, Eq s) => (a, s) -> Node s a -> Node s a
recursiveChildren (actiune, stare) parinte = 
    let
        newChild = TreeNode stare (Just actiune) (Just parinte) ((depth parinte) + 1) nextKids (h stare)
        nextKids = [(recursiveChildren sucs newChild) | sucs <- (successors stare)]
    in newChild

createStateSpace :: (ProblemState s a, Eq s) => s -> Node s a
createStateSpace initialState = 
    let
        node = TreeNode initialState Nothing Nothing 0 nextChildren (h initialState)
        nextChildren = [(recursiveChildren sucs node) | sucs <- (successors initialState)]
    in node
{-
    Funcție ce primește o coadă de priorități și întoarce o pereche
    formată din cheia cu prioritatea minimă și coada din care a fost ștearsă
    aceasta.
    Hint: O puteți folosi pentru a extrage și a șterge un nod din frontieră.
-}

deleteFindMin :: (Ord k, Ord p) => (PQ.PSQ k p) -> (k, (PQ.PSQ k p))
deleteFindMin pq = (minK, pq')
    where minK = PQ.key $ fromJust $ PQ.findMin pq
          pq' = PQ.deleteMin pq

{-
    *** TODO ***
    Primește nodul curent și mulțimea stărilor vizitate și întoarce
    o listă cu nodurile succesor nevizitate, care ar putea fi introduse
    în frontieră.
-}

suitableSuccs :: (ProblemState s a, Ord s) => Node s a -> (S.Set s) -> [Node s a]
suitableSuccs node visited =
    let firstList = map createStateSpace (S.toList visited)
        secondList = nodeChildren node
    in  secondList \\ firstList

{-
    *** TODO ***
    Primește o frontieră (o coadă de priorități) și un nod ce trebuie inserat în aceasta,
    întorcând o nouă frontieră.
    ATENȚIE: Dacă la introducerea unui nod există deja în frontieră un alt nod cu aceeași
    stare, dar cu cost mai mare, nodul nou, cu cost mai mic îl va înlocui pe cel vechi.
    
    Hints:
    1. Vedeți funcția insertWith din pachetul PSQueue.
        (https://hackage.haskell.org/package/PSQueue-1.1.0.1/docs/Data-PSQueue.html#v:insertWith)
    2. Costul se calculează ca suma dintre adâncime și euristică.
-}

insertSucc :: (ProblemState s a, Ord s) => (PQ.PSQ (Node s a) Float) -> Node s a -> PQ.PSQ (Node s a) Float
insertSucc frontier node = 
    let newFrontier = PQ.insertWith min node cost frontier
        cost = (nodeHeuristic node) + depthFloat
        depthFloat = (fromIntegral $ (nodeDepth node)) :: Float
    in newFrontier

{-
    *** TODO ***
    Primește nodul curent, frontiera și mulțimea stărilor vizitate, întorcând noua
    frontieră (coadă de priorități) în care au fost adăugate nodurile succesor validate
    de suitableSuccs.
-}

insertSuccs :: (ProblemState s a, Ord s) => (Node s a) -> (PQ.PSQ (Node s a) Float) -> (S.Set s) -> (PQ.PSQ (Node s a) Float)
insertSuccs node frontier visited = foldl insertSucc frontier (suitableSuccs node visited)

{-
    *** TODO ***
    Funcție helper care implementează A-star.
    Primește o mulțime de noduri vizitate și o coadă de priorități (aka frontiera) și
    întoarce starea finală.
    Se procedează astfel până la întâlnirea unei stări scop:
        - se extrage un nod adecvat din frontieră
        - se marchează starea acestuia ca fiind vizitată
        - se introduc succesorii în frontieră
-}

astar' :: (ProblemState s a, Ord s) => (S.Set s) -> (PQ.PSQ (Node s a) Float) -> Node s a
astar' visited frontier = 
    let newQueue = snd (deleteFindMin frontier)
        nodeExtracted = fst (deleteFindMin frontier)
        visitedNew = S.insert (nodeState nodeExtracted) visited
        newFrontier = insertSuccs nodeExtracted newQueue visitedNew
    in  if isGoal (nodeState nodeExtracted) then nodeExtracted else astar' visitedNew newFrontier

{-
    *** TODO ***
  
    Primește starea inițială și întoarce starea finală pentru o singură aplicare
    a algoritmului.
    Asigură parametrii inițiali corecți pentru aplicarea funcției astar'.
-}

astar :: (ProblemState s a, Ord s) => Node s a -> Node s a
astar initialNode = let frontier = PQ.insert initialNode 0 PQ.empty in astar' S.empty frontier
       
{-
    *** TODO ***
    Pornind de la un nod, reface parțial calea către nodul inițial, urmând legăturile
    către părinți.
    Întoarce o listă de perechi (acțiune, stare), care pornește de la starea următoare
    stării inițiale și se încheie la starea finală.
    ATENȚIE: Nodul inițial este singurul exclus!
-}

getNextParent :: Node s a -> Node s a
getNextParent node = fromJust (nodeParent node)

extractPath :: Node s a -> [(a, s)]
extractPath goalNode = 
    let infList = iterate getNextParent goalNode
        parents = takeWhile (\x -> nodeDepth x > 0) infList
        way = map (\x -> (fromJust (nodeAction x), (nodeState x))) parents
    in reverse way

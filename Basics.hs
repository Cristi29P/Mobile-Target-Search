{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE EmptyDataDecls, MultiParamTypeClasses,
             TypeSynonymInstances, FlexibleInstances,
             InstanceSigs #-}

module Basics where
{-
    Expune funcțiile necesare reprezentării jocului.
-}

import ProblemState
import Data.List
import Data.Maybe

{-
    Sinonim tip de date pentru reprezetarea unei perechi (Int, Int)
    care va reține coordonatele celulelor de pe tabla de joc.
    Colțul stânga-sus este (0, 0).
-}
type Position = (Int, Int)

{-
    Tip de date pentru reprezentarea Target-urilor.
    Acestea conțin informații atât despre poziția curentă a
    Target-ului cât și despre comportamentul acestuia.
    Tipul Behavior este definit mai jos.
-}
data Target = Target {
    position :: Position,
    behavior :: Behavior
}

instance Eq Target where
    Target p1 _ == Target p2 _ = p1 == p2

instance Ord Target where
    Target p1 _ <= Target p2 _ = p1 <= p2

{-
    Tip de date pentru reprezentarea comportamentului unui Target.
    Tipul Behavior este utilizat pentru a modela tranziția Target-urilor
    din starea curentă în starea următoare. Primul parametru este poziția
    actuală a target-ului, iar al doilea, starea curentă a jocului.
    Tipul Game este definit mai jos.
    
    Observați că, din moment ce un Behavior produce un Target nou,
    acesta din urmă ar putea fi caracterizat de un alt Behavior
    decât cel anterior.
-}
type Behavior = Position -> Game -> Target

{-
    Direcțiile de deplasare pe tablă
-}
data Direction = North | South | West | East
    deriving (Eq, Show)

{-
    *** TODO ***
    
    Tip de date pentru reprezentarea stării jocului, la un anumit
    moment. Completați-l cu orice informație aveți nevoie pentru
    stocarea stării jocului (hunter, target, obstacole, gateways).
-}
data Game = Game
    {
        noOfLines :: Int,
        noOfColumns :: Int,
        hunter :: Position,
        targets :: [Target],
        obstacles :: [Position],
        gateways :: [(Position, Position)]
    }
    deriving (Eq, Ord)
{-
    *** Optional *** 
  
    Dacă aveți nevoie de o funcționalitate particulară,
    instantiați explicit clasele Eq și Ord pentru Game.
    În cazul acesta, eliminați deriving (Eq, Ord) din Game.
-}

{-
    *** TODO ***

    Reprezentați starea jocului ca șir de caractere, pentru afișarea
    la consolă.
    
    Atenție! Fiecare linie, mai puțin ultima, este urmată de \n.
    Celule goale vor fi reprezentate ca ' '.
    Hunter-ul va fi reprezentat ca '!'.
    Target-urile vor fi reprezentate ca '*'
    Gateways-urile vor fi reprezentate ca '#'.
    Obstacolele vor fi reprezentate de '@'.

    Hint: S-ar putea să vă fie utile list comprehensions,
    precum și funcțiile elem, any și intercalate din Data.List.
-}
targetExistence :: Position -> [Target] -> Bool
targetExistence pos targetList = if ((filter (\x -> (position x) == pos) targetList) == []) then False else True

gatewayExistence :: Position -> [(Position, Position)] -> Bool
gatewayExistence pos gates = if ((filter (\x -> (((fst x) == pos) || ((snd x) == pos))) gates) == []) then False else True

gateReturnPair :: Position -> [(Position, Position)] -> (Position, Position)
gateReturnPair pos gateList = head (filter (\x -> (((fst x) == pos) || ((snd x) == pos))) gateList)

determineType :: Game -> (Int, Int) -> Char
determineType (Game _ _ hunt targetList obstacl gateList) x
    | x == hunt = '!'
    | elem x obstacl = '@'
    | targetExistence x targetList = '*'
    | gatewayExistence x gateList = '#'
    | otherwise = ' '

gameAsString :: Game -> String
gameAsString (Game linez columnz hunter_aux targets_aux obstacles_aux gateways_aux) = 
    let x = (Game linez columnz hunter_aux targets_aux obstacles_aux gateways_aux)
    in intercalate ['\n']  (transpose $ take (linez * columnz)  [[determineType x (i,j) | i <- [0..(linez - 1)]] | j <- [0..(columnz - 1)]])



instance Show Game where
    show = gameAsString

{-
    *** TODO ***
    
    Primește numărul de linii și numărul de coloane ale tablei de joc.
    Intoarce un obiect de tip Game în care tabla conține spații goale în interior, fiind
    împrejmuită de obstacole pe toate laturile. Implicit, colțul din stânga sus este (0,0),
    iar Hunterul se găsește pe poziția (1, 1).
-}
emptyGame :: Int -> Int -> Game
emptyGame noLines noColumns = Game {
                            noOfLines = noLines,
                            noOfColumns = noColumns,
                            hunter = (1, 1),
                            targets = [],
                            gateways = [],
                            obstacles =  [(i,j) | i <- [0..(noLines - 1)], j <- [0..(noColumns - 1)]] \\ [(i,j) | i <- [1..(noLines - 2)], j <- [1..(noColumns - 2)]] 
                        }

checkHunterPos :: Position -> Game -> Bool
checkHunterPos pos (Game height width _ _  obstacles_aux _)
            | (fst pos) < 1 = False
            | (fst pos) > height - 2 = False
            | (snd pos) < 1 = False
            | (snd pos) > width - 2 = False
            | elem pos obstacles_aux = False
            | otherwise = True

{-
    *** TODO ***    

    Primește o poziție și un joc și întoarce un nou joc, cu Hunter-ul pus
    pe poziția specificată.
    Parametrul Position reprezintă poziția de pe hartă la care va fi adaugat Hunter-ul
    Daca poziția este invalidă (ocupată sau în afara tablei de joc) se va întoarce
    același joc.
-}
addHunter :: Position -> Game -> Game
addHunter pos game = if (checkHunterPos pos game) then game {hunter = pos}
                                                  else game

{-
    *** TODO ***

    Primește un comportament, o poziție și un joc și întoarce un nou joc, în care a fost
    adăugat Target-ul descris de comportament și poziție.
    Parametrul Behavior reprezintă comportamentul Hunter-ului care va fi adăugat.
    Parametrul Position reprezintă poziția de pe hartă la care va fi adăugat Target-ul.
-}
addTarget :: Behavior -> Position -> Game -> Game
addTarget beh pos game = game {
        targets = (Target {position = pos, behavior = beh}):(targets game)
}

{-
    *** TODO ***

    Primește o pereche de poziții și un joc și întoarce un nou joc, în care au fost adăugate
    cele două gateway-uri interconectate.
    Parametrul (Position, Position) reprezintă pozițiile de pe hartă la care vor fi adăugate 
    cele două gateway-uri interconectate printr-un canal bidirecțional.
-}
addGateway :: (Position, Position) -> Game -> Game
addGateway aux game= game {
        gateways = aux:(gateways game)
}

{-
    *** TODO ***

    Primește o poziție și un joc și întoarce un nou joc, în care a fost adăugat un obstacol
    la poziția specificată.
    Parametrul Position reprezintă poziția de pe hartă la care va fi adăugat obstacolul.
-}
addObstacle :: Position -> Game -> Game
addObstacle  obs game = game {
    obstacles = obs:(obstacles game)
}

{-
    *** TODO ***
    
    Primește o poziție destinație înspre care vrea să se deplaseze o entitate (Hunter sau Target)
    și verifică daca deplasarea este posibilă, întorcând noua poziție, luând în considerare
    și Gateway-urile.
    Avem următoarele cazuri:
    - dacă poziția corespunde unui spațiu gol, se întoarce acea poziție;
    - dacă poziția corespunde unui gateway, se întoarce poziția gateway-ului pereche;
    - dacă poziția corespunde unui obstacol, se întoarce Nothing.
    Parametrul Position reprezintă poziția destinație.
-}
makeMove :: Position -> Game -> Position
makeMove pos game 
    | (gatewayExistence pos (gateways game)) = (let x = (gateReturnPair pos (gateways game)) in (if (fst x == pos) then (snd x) else (fst x)))
    | otherwise = pos

attemptMove :: Position -> Game -> Maybe Position
attemptMove pos game 
    | (gatewayExistence pos (gateways game)) = (let x = (gateReturnPair pos (gateways game)) in (if (fst x == pos) then Just (snd x) else Just (fst x)))
    | (checkHunterPos pos game) = Just pos
    | otherwise = Nothing

{-
    *** TODO ***

    Comportamentul unui Target de a se deplasa cu o casuță înspre est. 
    Miscarea se poate face doar daca poziția este validă (se află pe tabla de
    joc) și nu este ocupată de un obstacol. In caz contrar, Target-ul va rămâne 
    pe loc.
    
    Conform definiției, tipul Behavior corespunde tipului funcție
    Position -> Game -> Target.
    
    Având în vedere că cele patru funcții definite în continuare (goEast, goWest,
    goNorth, goSouth) sunt foarte similare, încercați să implementați o funcție
    mai generală, pe baza căreia să le definiți apoi pe acestea patru.
-}
goEast :: Behavior
goEast pos game 
    | ((attemptMove new game == Nothing) && (gatewayExistence pos (gateways game))) = Target (makeMove pos game) goEast
    | (attemptMove new game /= Nothing) = Target (makeMove new game) goEast
    | otherwise = Target pos goEast
    where new = ((fst pos), (snd pos + 1)) 
{-
    *** TODO ***

    Comportamentul unui Target de a se deplasa cu o casuță înspre vest. 
    Miscarea se poate face doar daca poziția este validă (se află pe tabla de
    joc) și nu este ocupată de un obstacol. In caz contrar, Target-ul va rămâne 
    pe loc.
-}
goWest :: Behavior
goWest pos game
    | ((attemptMove new game == Nothing) && (gatewayExistence pos (gateways game))) = Target (makeMove pos game) goWest
    | (attemptMove new game /= Nothing) = Target (makeMove new game) goWest
    | otherwise = Target pos goWest
    where new = ((fst pos), (snd pos - 1)) 
{-
    *** TODO ***

    Comportamentul unui Target de a se deplasa cu o casuță înspre nord. 
    Miscarea se poate face doar daca poziția este validă (se află pe tabla de
    joc) și nu este ocupată de un obstacol. In caz contrar, Target-ul va rămâne 
    pe loc.
-}
goNorth :: Behavior
goNorth pos game
    | ((attemptMove new game == Nothing) && (gatewayExistence pos (gateways game))) = Target (makeMove pos game) goNorth
    | (attemptMove new game /= Nothing) = Target (makeMove new game) goNorth
    | otherwise = Target pos goNorth
    where new = ((fst pos - 1), (snd pos)) 

{-
    *** TODO ***

    Comportamentul unui Target de a se deplasa cu o casuță înspre sud. 
    Miscarea se poate face doar daca poziția este validă (se află pe tabla de
    joc) și nu este ocupată de un obstacol. In caz contrar, Target-ul va rămâne 
    pe loc.
-}
goSouth :: Behavior
goSouth pos game
    | ((attemptMove new game == Nothing) && (gatewayExistence pos (gateways game))) = Target (makeMove pos game) goSouth
    | (attemptMove new game /= Nothing) = Target (makeMove new game) goSouth
    | otherwise = Target pos goSouth
    where new = ((fst pos + 1), (snd pos)) 

{-
    *** TODO ***

    Comportamentul unui Target de a-și oscila mișcarea, când înspre nord, când înspre sud. 
    Mișcarea se poate face doar dacă poziția este validă (se află pe tablă de
    joc) și nu este ocupată de un obstacol. In caz contrar, Target-ul iși va schimba
    direcția de mers astfel:
    - daca mergea inspre nord, își va modifica direcția miscării înspre sud;
    - daca mergea inspre sud, își va continua mișcarea înspre nord.
    Daca Target-ul întâlneste un Gateway pe traseul său, va trece prin acesta,
    către Gateway-ul pereche conectat și își va continua mișcarea în același sens la ieșire
    din acesta.
    Puteți folosit parametrul Int pentru a surprinde deplasamentul Target-ului (de exemplu,
    1 pentru sud, -1 pentru nord).
-}
bounce :: Int -> Behavior
bounce displacement (x, y) game = 
    let dest = attemptMove (x + displacement, y) game
        revDest = attemptMove (x - displacement, y) game
    in if (dest == Nothing) then Target (fromJust revDest) (bounce (-displacement))
                            else Target (fromJust dest) (bounce displacement)

    

{-
    *** TODO ***
    Funcție care mută toate Target-urile din Game-ul dat o poziție, în functie
    de behavior-ul fiecăreia și întoarce noul Game în care pozițiile Target-urilor
    sunt actualizate.
    
-}
moveTargets :: Game -> Game
moveTargets game = game {
                   targets = map (\x -> (behavior x) (position x) game) (targets game)
}

{-
    *** TODO ***

    Verifică dacă Targetul va fi eliminat de Hunter.
    Un Target este eliminat de Hunter daca se află pe o poziție adiacentă
    cu acesta.
    Parametrul Position reprezintă poziția Hunterului pe tabla
    de joc.
    Parametrul Target reprezintă Targetul pentru care se face verificarea.
-}
distance :: (Float, Float) -> (Float, Float) -> Float
distance (x1 , y1) (x2 , y2) = 
    let x' = x1 - x2
        y' = y1 - y2
    in sqrt (x'*x' + y'*y')


isTargetKilled :: Position -> Target -> Bool
isTargetKilled (x, y) target =
    let a = fromIntegral x :: Float
        b = fromIntegral y :: Float
        c = fromIntegral $ fst (position target) :: Float
        d = fromIntegral $ snd (position target) :: Float
    in  (distance (a, b) (c,d)) == 1

{-
    *** TODO ***

    Avansează starea jocului curent, rezultând starea următoare a jocului.
    Parametrul Direction reprezintă direcția în care se va deplasa Hunter-ul.
    Parametrul Bool specifică dacă, după mutarea Hunter-ului, vor fi
    mutate și Target-urile sau nu, și dacă vor fi eliminate din joc sau nu.
    Este folosit pentru a distinge între desfășurarea reală a jocului (True)
    și planificarea „imaginată” de hunter (False) în partea a doua a temei.

    Avansarea stării jocului respectă următoarea ordine:
    1. Se deplasează Hunter-ul.
    2. În funcție de parametrul Bool, se elimină Target-urile omorâte de către Hunter.
    3. In funcție de parametrul Bool, se deplasează Target-urile rămase pe tablă.
    4. Se elimină Targeturile omorâte de către Hunter și după deplasarea acestora.
    
    Dubla verificare a anihilării Target-urilor, în pașii 2 și 4, îi oferă Hunter-ului
    un avantaj în prinderea lor.
-}

moveHunter :: Direction -> Position -> Game -> Position
moveHunter direction pos game =  
    let semafor = attemptMove futurePosition game
        futurePosition
            | direction == North = ((fst pos) - 1, snd pos)
            | direction == South = ((fst pos) + 1, snd pos)
            | direction == East = (fst pos, (snd pos) + 1)
            | otherwise = (fst pos, (snd pos) - 1)
    in if semafor == Nothing then pos else fromJust semafor


remainingAlive :: Game -> Position -> [Target]
remainingAlive game pos = 
    let first = game {targets = filter (\x -> not $ isTargetKilled pos x) (targets game)}
        second = moveTargets first
    in filter (\x -> not $ isTargetKilled pos x) (targets second)


advanceGameState :: Direction -> Bool -> Game -> Game
advanceGameState dir check game = 
    let futurePos = moveHunter dir (hunter game) game
        newGame = game { hunter = futurePos}
    in if (check == False) then newGame else game {hunter = futurePos,
                                                   targets = remainingAlive game futurePos}
        


{-
    ***  TODO ***

    Verifică dacă mai există Target-uri pe table de joc.
-}
areTargetsLeft :: Game -> Bool
areTargetsLeft game = (targets game) == []

{-
    *** BONUS TODO ***

    Comportamentul unui Target de a se deplasa în cerc, în jurul unui Position, având
    o rază fixată.
    Primul parametru, Position, reprezintă centrul cercului.
    Parametrul Int reprezintă raza cercului.
    Puteți testa utilizând terenul circle.txt din directorul terrains, în conjuncție
    cu funcția interactive.
-}
circle :: Position -> Int -> Behavior
circle = undefined

instance ProblemState Game Direction where
    {-
        *** TODO ***
        
        Generează succesorii stării curente a jocului.
        Utilizați advanceGameState, cu parametrul Bool ales corespunzător.
    -}

    
    successors :: Game -> [(Direction, Game)]
    successors game =  
        let firstElem = advanceGameState West False game
            secondElem = advanceGameState North False game
            thirdElem = advanceGameState East False game
            fourthElem = advanceGameState South False game
        in [(West, firstElem), (North, secondElem), (East, thirdElem), (South, fourthElem)]


    {-
        *** TODO ***
        
        Verifică dacă starea curentă este un în care Hunter-ul poate anihila
        un Target. Puteți alege Target-ul cum doriți, în prezența mai multora.
    -}
    isGoal :: Game -> Bool
    isGoal game = 
        let copyLista = targets game
            filteredList = filter (isTargetKilled (hunter game)) (targets game)
            diff = copyLista \\ filteredList
        in if (length diff /= length copyLista) then True else False

    {-
        *** TODO ***
        
        Euristica euclidiană (vezi hEuclidian mai jos) până la Target-ul ales
        de isGoal.
    -}
    h :: Game -> Float
    h game = 
        let reachableTargets = filter (isTargetKilled (hunter game)) (targets game)
        in hEuclidean (hunter game) (position (head reachableTargets))

{-
     ** NU MODIFICATI **
-}
hEuclidean :: Position -> Position -> Float
hEuclidean (x1, y1) (x2, y2) = fromIntegral $ ((x1 - x2) ^ pow) + ((y1 - y2) ^ pow)
  where
    pow = 2 :: Int

{-
    *** BONUS ***

    Acesta reprezintă un artificiu necesar pentru testarea bonusului,
    deoarece nu pot exista două instanțe diferite ale aceleiași clase
    pentru același tip.

    OBSERVAȚIE: Testarea bonusului pentru Seach este făcută separat.
-}

newtype BonusGame = BonusGame Game
    deriving (Eq, Ord, Show)

{-
    *** BONUS TODO ***

    Folosind wrapper-ul peste tipul Game de mai sus instanțiați
    ProblemState astfel încât să fie folosită noua euristică. 
-}
instance ProblemState BonusGame Direction where
    {-
        *** BONUS TODO ***

        Pentru a ne asigura că toțî succesorii unei stări sunt de tipul
        BonusGame și folosesc noua euristică trebuie să aplicăm wrapper-ul
        definit mai sus peste toți succesorii unei stări.

        Hint: Puteți să folosiți funcția fmap pe perechi pentru acest lucru.
        https://wiki.haskell.org/Functor
    -}
    successors = undefined

    {-
        *** BONUS TODO ***

        Definiți funcția isGoal pentru BonusGame.

        Hint: Folosiți funcția isGoal deja implementată pentru tipul Game.
    -}
    isGoal = undefined

    {-
        *** BONUS TODO ***

        Definiți o funcție euristică care este capabilă să găsească un drum mai scurt
        comparativ cu cel găsit de euristica implementată pentru Game.

        ATENȚIE: Noua euristică NU trebuie să fie una trivială.

        OBSERVAȚIE: Pentru testare se va folosi fișierul terrains/game-6.txt.
    -}
    h = undefined

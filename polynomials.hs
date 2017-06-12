-- polynomials: basic polynomial manipulation tools
-- author: umut isik
---

import Data.Complex
import Data.Matrix
import qualified Data.Vector             as V
import qualified Data.Vector.Mutable     as MV
import Control.Monad.State
import Control.Monad
import System.Random
import System.Environment
import Debug.Trace 			 as Deb
-- numbers
type RR = Double
type CC = Complex RR

customShow :: CC -> String
customShow x = "(" ++ (cshow $ realPart x ) ++ " + " ++ (cshow $ imagPart x) ++ "*I)" where cshow a = if a == 0 then "0.0" else show a
	
-- the base field
type K = CC

-- monomials, polynomials etc
data Monom = Monom [Integer]

instance Show Monom where
	show (Monom []) = "1"
	show (Monom (x:xs)) = let pp x n =  "x" ++ (show n) ++ "^" ++ (show x) 
				  ss (0:xs) n first = ss xs (n+1) first 
				  ss [] _ first = if first then "1" else ""
				  ss (x:xs) n first = (if first then "" else "*") ++ pp x (n) ++ ss xs (n+1) False 
			      in ss (x:xs) 0 True 

instance Eq Monom where
	(==) (Monom []) m = if isZero m then True else False
	(==) m (Monom []) = (==) (Monom []) m
	(==) (Monom (m:ms)) (Monom (n:ns)) = if m /= n then False else (Monom ms) == (Monom ns)


isZero :: Monom -> Bool
isZero (Monom []) = True
isZero (Monom (x:xs)) = if x/=0 then False else isZero (Monom xs)

mMult :: Monom -> Monom -> Monom
mMult (Monom a) (Monom b) = let (l1,l2) = if (length a) > (length b) then (a,b) else (b,a) 
			    in Monom $ zipWith (+) l1 (l2 ++ [0,0..])

data Poly = Poly [(K, Monom)]
instance Show Poly where
	show (Poly []) = ""
	show (Poly (x:xs)) = let pp (coeff,monom) n = customShow coeff ++ "*" ++ show monom 
				 ss [] _ isFirst = if isFirst then "0" else ""
				 ss ((coeff,monom):xs) n isFirst 
						| (coeff == 0)                       = ss xs (n+1) isFirst
				       		| otherwise                          = (if isFirst then "" else " + ") ++ (pp (coeff,monom) (n+1)) ++ (ss xs (n+1) False)
		      	     in ss (x:xs) 0 True

instance Num Poly where 
	(+) (Poly a) (Poly b) = Poly (a ++ b)
	(*) (Poly [(a,b)]) (Poly [(c,d)]) = Poly [(a*c, b `mMult` d)]
	(*) (Poly a) (Poly b) = foldl1 (+) [ ((Poly [x]) * (Poly [y])) | x <- a, y <- b ]
	negate a = (Poly [(-1, Monom [0])]) * a 	
	abs a = a
	signum a = fromInteger 1
	fromInteger n = (Poly [(fromInteger n, Monom [0])])

delOverDel :: Int -> Poly -> Poly
delOverDel k (Poly a) = let n :: [Integer] -> Integer
			    n m = ((m ++ [0,0..]) !! k)
			in Poly $ foldl1 (++) [ [((fromInteger $ n m) * coeff, Monom $ (take k m) ++ [(if (n m) > 0 then ((n m) - 1) else 0)] ++ (drop (k+1) m))] | (coeff,Monom m) <- a]

del2OverDel k1 k2 = delOverDel k1 . (delOverDel k2) 

--polyCompose (Poly a) b

polyCompose ::  Poly -> [Poly] -> Poly
polyCompose (Poly []) _ = fromInteger 0
polyCompose (Poly [(coeff, Monom mm)]) [] = fromInteger 0
polyCompose (Poly [(coeff, Monom mm)]) pols = let fun :: [Integer] -> [Poly] -> Poly 
						  fun [] _ = fromInteger 1 
						  fun _ [] = fromInteger 1 	
						  fun (x:xs) (p:ps) = (p `toPow` x) * (fun xs ps)
					      in (Poly [(coeff, Monom [0])]) * (fun mm pols)
polyCompose (Poly (p:ps)) pols = (polyCompose (Poly [p]) pols) + (polyCompose (Poly ps) pols) 

toPow :: Poly -> Integer -> Poly	
toPow f 0 = fromInteger 1
toPow f n = f * (f `toPow` (n-1))
 
plugXAtKInto :: K -> Int -> Poly -> Poly
plugXAtKInto x k (Poly [(coeff, Monom m)]) = let n = (m ++ [0,0..]) !! k 
					     in Poly [( coeff*(x^n) , Monom $ (take k m) ++ [0] ++ (drop (k+1) m) )]
plugXAtKInto x k a = foldl (+) (fromInteger 0) $ [ plugXAtKInto x k (Poly [pp]) | pp <- termsOf a]

listVarsAppearingInPoly :: Poly -> [Int]
listVarsAppearingInPoly (Poly a) = let rr [] = []
				       rr ((coeff, m):xs) = (if coeff /= 0 then listVarsAppearingInMonom m else []) ++ rr xs
				   in removeDuplicates $ rr a

listVarsAppearingInMonom (Monom b) = let recu [] _ = []
				       	 recu (x:xs) i = (if x /= 0 then [i] else []) ++ recu xs (i+1)
          			     in recu b 0

-- the number of vars, including lower indices that may not appear
numberOfVarsAppearingInPoly :: Poly -> Int
numberOfVarsAppearingInPoly f = (foldl1 max $ listVarsAppearingInPoly f) + 1

removeDuplicates :: Eq a => [a]->[a]
removeDuplicates [] = []
removeDuplicates (x:xs) = [x] ++ (removeDuplicates $ filter (/= x) xs)

matrixOfVariables :: Int -> Matrix Poly
matrixOfVariables n = matrix n n (\(i,j) -> (xi (n*(i-1) + (j-1)))) 

cleanUp :: Poly -> Poly
cleanUp (Poly []) = Poly []
cleanUp (Poly ((coeff, po):ts)) = let filterAndAdd :: Monom -> Poly -> (Poly, K)
				      filterAndAdd _ (Poly []) = (Poly [],0)
				      filterAndAdd m (Poly ((co, mo):rest)) = if (mo == m) then (fst $ filterAndAdd m (Poly rest) ,co + (snd $ filterAndAdd m (Poly rest)))
					    					         else ((Poly ([(co,mo)] ++ (termsOf (fst $ filterAndAdd m (Poly rest))))) , (snd $ filterAndAdd m ( Poly rest)))
				      fdrest = filterAndAdd po (Poly ts)
				  in ((Poly [(coeff + (snd $ fdrest), po)]) + (cleanUp $ fst fdrest))


xi ::  Int -> Poly
xi i = Poly $ [(1, Monom ((take i [0,0..]) ++ [1]))]

xitod ::  Int -> Int -> Poly
xitod i d = Poly $ [(1, Monom ((take i [0,0..]) ++ [fromIntegral d]))]

termsOf :: Poly -> [(K,Monom)]
termsOf (Poly a) = a

permanent :: Num a => Matrix a -> a
permanent m 
	| (nrows m, ncols m) == (1,1)        = (m ! (1,1)) 
	| otherwise        		     = foldl1 (+) [ (m ! (i,1)) * permanent (minorMatrix i 1 m) | i <- [1 .. nrows m] ]
 
determinant :: Num a => Matrix a -> a
determinant m 
	| (nrows m, ncols m) == (1,1)        = (m ! (1,1)) 
    	| otherwise 			     = foldl1 (+) [ (-1)^(i-1) * m ! (i,1) * determinant (minorMatrix i 1 m) | i <- [1 .. nrows m] ]

main :: IO ()
main = do putStrLn "Polys. version 0.0.0 -- -- \n"
--	  putStrLn $ show testpoly3
--	  putStrLn $ show $ plugXAtKInto 2 1 testpoly3
--	  putStrLn " "
--	  putStrLn $ show $ plugXAtKInto 4 1 thePermanent 
--	  putStrLn " "
--	  putStrLn $ show $ delOverDel 0 thePermanent 
--	  putStrLn $ show $ delOverDel 4 $ delOverDel 0 thePermanent 
--	  putStrLn " "
--	  putStrLn $ show $ theDeterminant 
	  args <- getArgs
	  case args of  
	         		[f]         -> argsmain f
		 		otherwise   -> noargsmain 

argsmain :: FilePath -> IO ()
argsmain f = do let outputFermat3 = (bertiniInputForDegreeOfDualOfHypersurface fermatCubic 3)
		    outputFermatInc = (bertiniInputForSingularIncidence (randomCoordChange $ fermatCubicn 4) 4)
		    outputFermat3Rand = (bertiniInputForDegreeOfDualOfHypersurface (randomCoordChange $ fermatCubic) 3)
                    outputFermat n = (bertiniInputForDegreeOfDualOfHypersurface (fermatCubicn n) n)
	            outputPerm = bertiniInputForDegreeOfDualOfHypersurface thePermanent (theN^2)
	            outputDet = bertiniInputForDegreeOfDualOfHypersurface theDeterminant (theN^2)
	            outputDetInc = bertiniInputForSingularIncidence (theDeterminant) (theN^2)
		    outputFRan n d = (bertiniInputForDegreeOfDualOfHypersurface (evalState (randomPoly n d) (randomGenerator 435)) n)
		    outputConeOfRandom = (bertiniInputForSingularIncidence (polyCompose (evalState (randomPoly 3 3) (randomGenerator 74747)) [xitod 1 1, xitod 2 1, xitod 3 1]) 4)
                writeFile f $ outputPerm

noargsmain :: IO ()
noargsmain = do putStrLn ""
		--putStrLn $ "Random Polynomial f = " ++ (show $ fran)
                --putStrLn $ show $ cleanUp $ polyCompose fermatCubic [fromInteger 1, (xitod 1 4) + ((fromInteger 2) * (xitod 1 3)), xitod 4 4] 
		--let mm = foldr1 (+) (evalState (sequence ([(randomPoly 3 3), (randomPoly 3 3)])) (randomGenerator 132))
		--putStrLn $ show $ cleanUp $ polyCompose mm [fromInteger 1, fromInteger 1, fromInteger 1] 
		-- putStrLn $ show $ cleanUp $ polyCompose fermatCubic (evalState (sequence (take 3 $ repeat (randomPoly 3 1))) (randomGenerator 9129) )
		putStrLn $ show $ cleanUp $ (xi 0)*(xi 1) 
		putStrLn $ unlines ((map (show . cleanUp)) (gradOfNorm (fermatCubic) 3))
                putStrLn "\n\n"

theN = 3
theDeterminant = determinant $ matrixOfVariables theN
thePermanent = permanent $ matrixOfVariables theN

randomCoordChange f = cleanUp $ polyCompose f (evalState (sequence (take vrs $ repeat (randomPoly vrs 1))) (randomGenerator 23428)) where vrs = numberOfVarsAppearingInPoly f

fermatCubicn n = Poly $ zip (repeat 1) ([ Monom ((take i $ (repeat 0)) ++ [3] ) | i<-[0..(n-1)]])
fermatCubic = Poly [(1, Monom [3]), (1, Monom [0,3]), (1, Monom [0,0,3])]

testpoly1 = Poly [(3 ,Monom [1,2,0,0]), (5, Monom [0,7])]
testpoly3 = Poly [(1, Monom [0,7])]
testpoly2 = Poly [(1, Monom [1]), (1,Monom [0,1])]




-- dim is the number of variables to be considered, indices start from 0
bertiniInputForSingularIncidence f dim = let partials = [ (delOverDel i (plugXAtKInto 1 0 f)) | i <- [0..(dim-1)]] 
					 in "% a basic computation of the degree of a projective dual\n% author: umut isik.\n"
						       ++ "CONFIG\n" ++ "\nTRACKTYPE: 1;\n"
						       ++ "%MPTYPE: 2;\n"
						       ++ "%FINALTOL: 1e-14;\nEND;\nINPUT\n\n"
						       ++ "% coordinates of projective space, and the line\n"
						       ++ "variable_group "
						       -- these start from 1 not 0 since we are setting x0=1
						       ++ let removeZero xs = filter (\x -> x /= 0) xs
						          in (foldl (++) "" $ zipWith (\s1 -> \s2 -> s1 ++ s2 ++ ", ") (repeat "x") (map show (removeZero $ listVarsAppearingInPoly f)))
						       ++ "" -- ys are variables for the dual space 
						       ++ let removeZero xs = filter (\x -> x /= 0) xs
						          in (init . init) (foldl (++) "" $ zipWith (\s1 -> \s2 -> s1 ++ s2 ++ ", ") (repeat "y") (map show (removeZero $ listVarsAppearingInPoly f)))
						       ++ ";\n" 
						       ++ "x0 = 1;\ny0 = 1;\n"
						       ++ "\n" 
						       ++ "% names of all equations to solve: \n" 
						       ++ let lenn = round ((d*(d-1)/2)) 
							      d = fromIntegral (dim-1)
						       	  in "function f, " ++ (foldl1 (\x -> \y -> x ++ ", " ++ y) ([ "LD" ++ (show i) | i<-[1..lenn]]) ) 
						       ++ ", HH;"
						       ++ "\n\n" 
						       ++ "% equation of the hypersurface"
						       ++ "\n" 
						       ++ "f = " ++ show f ++ ";"
						       ++ "\n\n" 
						       ++ "% the partial derivatives of f\n"
						       ++ (foldl1 (++) $ zipWith (\x -> \y -> x ++ y ++ ";") [ ("\nDf" ++ (show i) ++ " = ") | i <- [0..(dim-1)] ]  
						       				      			     (map show partials))
						       ++ "\n\n"
						       ++ "% the lines\n" 
						       ++ (map (\x -> if x == 'x' then 'y' else x) $ foldl1 (++) $ zipWith (\x -> \y -> x ++ y ++ ";") [ ("\nL" ++ (show i) ++ " = ") | i <- [0..(dim-1)] ]  
						       				      [show (xitod i 1) | i <- [0..(dim-1)]] )
						       ++ "\n\n" 
						       ++ "% equation of the hyperplane corresponding to the point in the dual space\n"	 
						       ++ "HH = " ++ ( drop 2 $ foldl1 (++) $ let lst = [ show k | k<-[0..(dim-1)]]
						       		  	                      in zipWith (\i -> \j -> "+ L" ++ i ++ "*x" ++ j ++ " ") lst lst ) ++ ";"
						       ++ "\n\n" 
						       ++ "% equations for checking non-smooth intersection - ignore LD0\n"
						       -- ++ let jacob = fromLists [[show j | j<- [0..(dim-1)]] | i<-[0..(dim-1)]] 
						       ++ let mkeqlst [] _ = []
						              mkeqlst (pr:prs) k = let i = show $ fst pr
							      			       j = show $ snd pr
										   in ( ("LD" ++ (show k) ++ " = " ++ "Df" ++ i ++ "*L" ++ j ++ " - " ++ "Df" ++ j ++ "*L" ++ i ++ ";"  ) : (mkeqlst prs (k+1)) ) 
							  in (foldl1 (\x -> \y -> x ++ "\n" ++ y) (mkeqlst (pairList dim) 1))
						       ++ "\n\n"
						       ++ "END;"

-- dim is the number of variables to be considered, indices start from 0
bertiniInputForDegreeOfDualOfHypersurface f dim = let partials = [ (delOverDel i (plugXAtKInto 1 0 f)) | i <- [0..(dim-1)]] 
						  in "% a basic computation of the degree of a projective dual\n% author: umut isik.\n"
						       ++ "CONFIG\n" ++ "\nTRACKTYPE: 0;\n"
						       ++ "MPTYPE: 2;\n"
						       ++ "FINALTOL: 1e-14;\nEND;\nINPUT\n\n"
						       ++ "% coordinates of projective space, and the line\n"
						       ++ "variable_group "
						       -- these start from 1 not 0 since we are setting x0=1
						       ++ let removeZero xs = filter (\x -> x /= 0) xs
						          in (foldl (++) "" $ zipWith (\s1 -> \s2 -> s1 ++ s2 ++ ", ") (repeat "x") (map show (removeZero $ listVarsAppearingInPoly f)))
						       
						       ++ "t1;\n" -- variable for the line 
						       ++ "x0 = 1;\nt0 = 1;\n"
						       ++ "\n" 
						       ++ "% names of all equations to solve: \n" 
						       ++ let lenn = round ((d*(d-1)/2)) 
							      d = fromIntegral (dim-1)
						       	  in "function f, " ++ (foldl1 (\x -> \y -> x ++ ", " ++ y) ([ "LD" ++ (show i) | i<-[1..lenn]]) ) 
						       ++ ", HH;"
						       ++ "\n\n" 
						       ++ "% equation of the hypersurface"
						       ++ "\n" 
						       ++ "f = " ++ show f ++ ";"
						       ++ "\n\n" 
						       ++ "% the partial derivatives of f\n"
						       ++ (foldl1 (++) $ zipWith (\x -> \y -> x ++ y ++ ";") [ ("\nDf" ++ (show i) ++ " = ") | i <- [0..(dim-1)] ]  
						       				      			     (map show partials))
						       ++ "\n\n"
						       ++ "% the lines\n" 
						       ++ (map (\x -> if x == 'x' then 't' else x) $ foldl1 (++) $ zipWith (\x -> \y -> x ++ y ++ ";") [ ("\nL" ++ (show i) ++ " = ") | i <- [0..(dim-1)] ]  
						       				      ( evalState (sequence [ (liftM show $ randomLineInTwoVars) | i <- [0..(dim-1)] ]) (randomGenerator 21) ))
						       ++ "\n\n" 
						       ++ "% equation of the hyperplane corresponding to the point in the dual space\n"	 
						       ++ "HH = " ++ ( drop 2 $ foldl1 (++) $ let lst = [ show k | k<-[0..(dim-1)]]
						       		  	                      in zipWith (\i -> \j -> "+ L" ++ i ++ "*x" ++ j ++ " ") lst lst ) ++ ";"
						       ++ "\n\n" 
						       ++ "% equations for checking non-smooth intersection - ignore LD0\n"
						       -- ++ let jacob = fromLists [[show j | j<- [0..(dim-1)]] | i<-[0..(dim-1)]] 
						       ++ let mkeqlst [] _ = []
						              mkeqlst (pr:prs) k = let i = show $ fst pr
							      			       j = show $ snd pr
										   in ( ("LD" ++ (show k) ++ " = " ++ "Df" ++ i ++ "*L" ++ j ++ " - " ++ "Df" ++ j ++ "*L" ++ i ++ ";"  ) : (mkeqlst prs (k+1)) ) 
							  in (foldl1 (\x -> \y -> x ++ "\n" ++ y) (mkeqlst (pairList dim) 1))
						       ++ "\n\n"
						       ++ "END;"




-- gradient descent
grDes :: [Poly] -> [K] -> [K] 
grDes p x = undefined
--snd (rec 0 x) where rec n v = (n+1, snd (rec (n+1) (grStep p v)))  

realPo :: Poly -> Poly
realPo f = polyCompose f [ ((xi (2*j)) + (Poly [(0 :+ 1,Monom [0])])*(xi (2*j+1))) | j<-[0,1..]]

poRealPart (Poly (t:ts)) = (ss t) + (poRealPart (Poly ts)) where ss (c, m) = Poly [(realPart c :+ 0,m)]
poRealPart p = p;

poImagPart (Poly (t:ts)) = (ss t) + (poImagPart (Poly ts)) where ss (c, m) = Poly [(imagPart c :+ 0,m)]
poImagPart p = p

grDesStepLength = 0.1;

-- gradient of the norm function
gradOfNorm f = gradient $ (poRealPart f)^2 + (poImagPart f)^2

gradient :: Poly -> Int -> [Poly]
gradient f n = [ delOverDel i f | i<-[0..n]]

-- list of choose pairs 0..dim
pairList :: Int -> [(Int,Int)]
pairList n = [ (i,j) | i<-[1..(n-1)], j<-[1..(n-1)], i<j ]
--pairList n = [(1,j) | j<- [2..(n-1)]]		


-- randomness
--

-- random homogeneous polynomial on n variables of degree d
randomPoly :: Int -> Int -> GeneratorState Poly
randomPoly n d = let allMonoms _ 0 = fromInteger 1
		     allMonoms 0 d = (xitod 0 d)
		     allMonoms n d = foldl1 (+) [ (((xitod n i)) * (allMonoms (n-1) (d-i))) | i<- [0..d]]
		     number = (length $ (termsOf $ allMonoms n d))
		     mon = allMonoms (n-1) d
		     rec [] _ = []
		     rec (x:xs) (c:cs) = ((c,snd x):rec xs cs)
		 in (liftM Poly (liftM (rec $ termsOf mon) (getRandomCCs number) ))


randomLines :: Int -> GeneratorState [Poly]
randomLines dim = undefined
--randomLines dim = [ rL | x <- [1..dim]]

randomLineInTwoVars :: GeneratorState Poly
randomLineInTwoVars = liftM Poly $ sequence [sequencePair (getRandomCC, return $ Monom [1]), sequencePair (getRandomCC, return $ Monom [0,1])] 
			
sequencePair :: Monad m => (m a, m b) -> m (a,b) 			
sequencePair pr = do xx <- fst pr
		     yy <- snd pr
		     return (xx,yy)  
				       

randomGenerator n = mkStdGen n
type GeneratorState = State StdGen 

getRandomRR :: GeneratorState RR
getRandomRR =
  get >>= \gen ->
  let (val, gen') = randomR ((-1*maxMod),maxMod) gen in
  put gen' >>
  return val

maxMod = 1

getRandomCC :: GeneratorState CC
getRandomCC = liftM2 (:+) getRandomRR getRandomRR 

getRandomCCs :: Int -> GeneratorState [CC]
getRandomCCs k = sequence $ [getRandomCC | i <- [1..k]]






-- % solving these equations for all the above variables
-- function f, LD1, LD2 , LL;
-- 
-- 
-- % equation of the hypersurface
-- f = x0^3 + x1^3 + x2^3;
-- 
-- % the partial derivatives of f
-- F0 = 3*x0^2;
-- F1 = 3*x1^2;
-- F2 = 3*x2^2;
-- 
-- % the parametrization of the line in the dual space
-- A00 = 12.123;
-- A01 = 23.123232;
-- A10 = 34.34344434;
-- A11 = 0.2343;
-- A20 = 9.545454;
-- A21 = -12.88738;
-- 
-- L0 = A00*t0 + A01*t1;
-- L1 = A10*t0 + A11*t1;
-- L2 = A20*t0 + A21*t1;
-- 
-- % the equation of the hyperplane defined by a point on the line
-- LL = L0*x0 + L1*x1 + L2*x2;
-- 
-- % linear dependence relations (minors)
-- %LD0 = F0*L1 - F1*L0; 
-- LD1 = F0*L2 - F2*L0;
-- LD2 = F1*L2 - F2*L1;
-- 
-- END;






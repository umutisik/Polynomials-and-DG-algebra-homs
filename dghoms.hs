{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE InstanceSigs #-}
import System.IO
import Control.Monad
import Data.Complex

--main = let Homomorphism ph = phi
--       in print $ ph (1,2)

--main = print $ applyhom phi a12
--

-- manual checking that Yanki's phi respects the differentials
{-
main = let check1 = cleanup $ (applydifferential bigD (applyhom yanphi s1))-((applyhom yanphi (applydifferential lild s1)))
           check2 = cleanup $ (applydifferential bigD (applyhom yanphi s2))-((applyhom yanphi (applydifferential lild s2)))
           check3 = cleanup $ (applydifferential bigD (applyhom yanphi s3))-((applyhom yanphi (applydifferential lild s3)))
           check4 = cleanup $ (applydifferential bigD (applyhom yanphi s4))-((applyhom yanphi (applydifferential lild s4)))
       in do print check1 
             print check2
             print check3
             print check4 
-}


--main = let check1 = cleanup $ (applydifferential bigD (applyhom phi s1))-((applyhom phi (applydifferential lild s1)))
--       in do print check1 


main = do print $ cleanup $ applydifferential (phi2 `diffCompose` phi2) s1
            where phi2 = freePhik 2





-- numbers ------------------------------
type RR = Double
type CC = Complex RR

type K = RR      -- base field
type KK = Poly

-- this computation ----

s1  = fromPure $ PureTensor [(1,1)]::Tensor KK
s2  = fromPure $ PureTensor [(2,2)]::Tensor KK
s3  = fromPure $ PureTensor [(3,3)]::Tensor KK
s4  = fromPure $ PureTensor [(4,4)]::Tensor KK

a12 = fromPure $ PureTensor [(1,2)]::Tensor KK
a21 = fromPure $ PureTensor [(2,1)]::Tensor KK
a31 = fromPure $ PureTensor [(3,1)]::Tensor KK
a13 = fromPure $ PureTensor [(1,3)]::Tensor KK
a41 = fromPure $ PureTensor [(4,1)]::Tensor KK
a14 = fromPure $ PureTensor [(1,4)]::Tensor KK

lild = Differential d 
         where d (1,1) = (-1)*(a12*a21) + (-1)*(a13*a31) + (-1)*(a14*a41) 
               d (2,2) = a21*a12
               d (3,3) = a31*a13
               d (4,4) = a41*a14
               d _ = fromInteger 0

bigD = Differential d
       --where d (1,1) = (-1)*(a12*a21) + (-1)*(a13*a31) + (-1)*(a14*a41) + 2*(a12*a21*a13*a31)
         where d (1,1) = (-1)*(a12*a21) + (-1)*(a13*a31) + (-1)*(a14*a41) + (a12*a21*a13*a31)
               d (2,2) = a21*a12
               d (3,3) = a31*a13
               d (4,4) = a41*a14
               d _ = fromInteger 0

freePhik k = Differential phik
        where startendas i j depth varstart = foldl1 (+) (zipWith (*) (lotsovarsfrom varstart) $ startendaslist i j depth) 
              startendaslist i j depth= (levelgen i j depth)
              phik (i,j) =  if i/=j
                            then (startendas i j (k+1) ((if i>j then 5000 else 0)+1000*i ))
                            else (philevel (k+1) 100)
                              where [s] = sselect i
                                    philevellist :: Int -> [Tensor KK]
                                    philevellist l = if l==1 then sselect i else
                                        [ z1*zz*z2 | pl<-[1], ii <- [i], z1<-(startendaslist i ii (pl-1)), z2<-(startendaslist ii i (l-pl)),zz<-(sselect ii)] ++
                                        [ z1*zz*z2 | pl<-[2,3..(l-1)], ii <- [1,2,3,4], z1<-(startendaslist i ii (pl-1)), z2<-(startendaslist ii i (l-pl)),zz<-(sselect ii)] ++
                                        [ z1*zz*z2 | pl<-[l], ii <- [i], z1<-(startendaslist i ii (pl-1)), z2<-(startendaslist ii i (l-pl)),zz<-(sselect ii)] 
                                    philevel:: Int -> Int -> Tensor KK
                                    philevel l varstart = foldl1 (+) (zipWith (*) (lotsovarsfrom (10000*i+2500*(j-1)+varstart)) (philevellist l) )


phi :: Homomorphism Poly
phi = Homomorphism ph
        where startendas i j depth varstart = foldl1 (+) (zipWith (*) (lotsovarsfrom varstart) $ startendaslist i j depth) 
              startendaslist i j depth= (levelgen i j depth)
              ph (i,j) = if i /= j 
                         then len1 + len3 + len5 + len7 
                         else (philevel 1 0) + (philevel 3 2) + (philevel 5 13) + (philevel 7 60)
                             where -- for a's, the then case
                                   len1 = (startendas i j 1 0)
                                   len3 = (startendas i j 3 10)
                                   len5 = (startendas i j 5 200)
                                   len7 = (startendas i j 7 500)
                                   -- for s's, the else case 
                                   [s] = sselect i
                                   philevellist :: Int -> [Tensor KK]
                                   philevellist l = if l==1 then sselect i else
                                       [ z1*zz*z2 | pl<-[1], ii <- [i], z1<-(startendaslist i ii (pl-1)), z2<-(startendaslist ii i (l-pl)),zz<-(sselect ii)] ++
                                       [ z1*zz*z2 | pl<-[2,3..(l-1)], ii <- [1,2,3,4], z1<-(startendaslist i ii (pl-1)), z2<-(startendaslist ii i (l-pl)),zz<-(sselect ii)] ++
                                       [ z1*zz*z2 | pl<-[l], ii <- [i], z1<-(startendaslist i ii (pl-1)), z2<-(startendaslist ii i (l-pl)),zz<-(sselect ii)] 
                                   philevel:: Int -> Int -> Tensor KK
                                   philevel l varstart = foldl1 (+) (zipWith (*) (lotsovarsfrom (1000*i+250*(j-1)+varstart)) (philevellist l) )

yanphi :: Homomorphism Poly
yanphi = Homomorphism ph
           where fnum x = fromScalar $ constantPoly x  -- fromnum
                 ph (1,1) = s1 + (fnum 0.25)*(a12*a21*s1*a14*a41 + a12*s2*a21*a14*a41 + a12*a21*a14*s4*a41 - a12*s2*a21*a13*a31*a14*a41)
                 ph (2,2) = s2 + (fnum 0.5)*(a21*a12*s2 + a21*s1*a12 - s2*a21*a13*a31*a12) 
                 ph (3,3) = s3 + (fnum 0.5)*(a31*a13*s3 + a31*s1*a13 - a31*a12*a21*a13*s3) - (fnum 0.25)*(a31*a14*a41*s1*a13 + a31*a14*s4*a41*a13 + a31*a14*a41*a13*s3 - a31*a14*a41*a12*a21*a13*s3) 
                 ph (4,4) = s4 - (fnum 0.5)*(s4*a41*a14 + a41*s1*a14 + a41*s1*a13*a31*a14 + a41*a13*s3*a31*a14 + s4*a41*a13*a31*a14 - a41*a12*a21*a13*s3*a31*a14) 
                 ph (1,2) = a12
                 ph (2,1) = a21 - (fnum 0.5)*(a21*a13*a31 + a21*a14*a41)
                 ph (1,3) = a13 - (fnum 0.5)*a12*a21*a13
                 ph (3,1) = a31 - (fnum 0.5)*a31*a14*a41
                 ph (1,4) = a14 + (fnum 0.5)*(a12*a21*a14 + a13*a31*a14)
                 ph (4,1) = a41 
                 ph _ = 0




applyhom :: Homomorphism k -> Tensor k -> Tensor k
applyhom (Homomorphism ph) (Tensor [(_,PureTensor [])]) =  fromScalar 0
applyhom (Homomorphism ph) (Tensor [(c, UnitPureTensor)]) =  fromScalar c
applyhom (Homomorphism ph) (Tensor [(c,PureTensor [(t1,t2)])]) = (fromScalar c)*(ph (t1,t2))
applyhom (Homomorphism ph) (Tensor [(c,PureTensor (x:xs))]) = (fromScalar c)*(ph x)*(applyhom (Homomorphism ph) (Tensor [(1,PureTensor xs)]))
applyhom phi (Tensor (x:xs)) = (applyhom phi (Tensor [x]))+(applyhom phi (Tensor xs))

applydifferential :: Differential k -> Tensor k -> Tensor k
applydifferential (Differential d) (Tensor [(_,PureTensor [])]) =  fromScalar 0
applydifferential (Differential d) (Tensor [(c, UnitPureTensor)]) =  fromScalar 0
applydifferential (Differential d) (Tensor [(c,PureTensor [(t1,t2)])]) = (fromScalar c)*(d (t1,t2))
applydifferential (Differential d) (Tensor [(c,PureTensor (x:xs))]) = (d x)*(Tensor [(c,PureTensor xs)]) 
                                                                            +  (Tensor [(c,PureTensor [x])])*(applydifferential (Differential d) (Tensor [(1,PureTensor xs)]))
applydifferential (Differential d) (Tensor (x:xs)) = (applydifferential (Differential d) (Tensor [x])) + (applydifferential (Differential d) (Tensor xs))

cleanup :: Tensor Poly -> Tensor Poly
cleanup (Tensor []) = Tensor [] 
cleanup (Tensor [(p,x)]) = if isPolyZero p then (Tensor []) else Tensor [(p,x)] 
cleanup (Tensor ls) = let firstterm = head ls
                          firstpure = snd firstterm
                          samepure (_,t1) (_,t2) = (t1==t2) 
                          filteredsame = filter (samepure firstterm) ls 
                          filteredother = filter (not . (samepure firstterm)) ls
                          sumcoeff = cleanUpPoly $ sum $ map fst filteredsame 
                      in (if isPolyZero sumcoeff then (Tensor []) else (Tensor [(sumcoeff,firstpure)])) + cleanup (Tensor filteredother)

lotsovarsfrom k = map fromScalar [xi (k+i) | i<-[1,2..]]
--lotsofvariables = map (fromScalar . Symbolic) $ zipWith (++) (repeat "c") (map show [1,2..])

levelgen i j 0 = [fromScalar 1]
levelgen i j 1 = [ z | z<-aselect i j ]
levelgen i j k = [ z*z' | l<-[1,2,3,4], z <- aselect i l, z'<-levelgen l j (k-1)]

{-levelgen :: Int -> Int -> [Tensor K]
levelgen i 0 = []::[Tensor k]
levelgen i 1 = [ z | j <- [1,2,3,4], z<-(aselect i j) ]
levelgen i k = [ z*x | j <- [1,2,3,4], x<-(levelgen j (k-1)), z<-(aselect i j) ]
---}
sselect :: Int -> [Tensor KK]
sselect 1 = [s1]
sselect 2 = [s2]
sselect 3 = [s3]
sselect 4 = [s4]
aselect 1 2 = [a12]
aselect 2 1 = [a21]
aselect 1 3 = [a13]
aselect 3 1 = [a31]
aselect 1 4 = [a14]
aselect 4 1 = [a41]
aselect _ _ = []

-- tensors ------------------------------

-- underlying set of generators for the tensor algebra
type S = (Int,Int)


data PureTensor = PureTensor [S] | UnitPureTensor 
    deriving (Eq)
instance Show PureTensor where
    show UnitPureTensor = "unitpuretensor"
    show (PureTensor []) = "emptypuretensor!!! (something's weird)"
    show (PureTensor [(i,j)]) = if i/=j then "a"++(show i)++(show j) else "s"++ (show i)
    show (PureTensor (x:xs)) = (show (PureTensor [x])) ++ " _ " ++ (show (PureTensor xs)) 
mult :: PureTensor -> PureTensor -> PureTensor
mult a UnitPureTensor = a
mult UnitPureTensor b = b
mult (PureTensor x) (PureTensor y) = PureTensor $ x ++ y

data Tensor k where
   Tensor :: (Num k) => [(k,PureTensor)] -> Tensor k        
instance (Num k) =>  Num (Tensor k) where
       (+) (Tensor a) (Tensor b) = Tensor $ a ++ b
       (*) (Tensor [(c1,a)]) (Tensor [(c2,b)]) = Tensor [(c1*c2, a `mult` b)]
       (*) (Tensor a) (Tensor b) = foldl1 (+) [ (Tensor [x])*(Tensor [y]) |  x<- a, y<-b  ]
       negate a = (fromScalar (-1))*a
       abs a = a
       signum a = fromInteger 1
       fromInteger n = Tensor [(fromIntegral n, UnitPureTensor)] 
instance (Show k) => Show (Tensor k) where
       show (Tensor []) = "_0_"
       show (Tensor (x:xs)) = (show x) ++ "\n+ " ++ (show $ Tensor xs)

splitToTerms :: Tensor k -> [Tensor k] 
splitToTerms (Tensor lst) = (map fromPair lst)  
fromPair :: (Num k) => (k,PureTensor) -> Tensor k
fromPair x = Tensor [x]
 
-- tensor should be a functor, this should be fmap
-- but Num stuff complicates things
tenmap :: (Num a, Num b) => (a -> b) -> Tensor a -> Tensor b  
tenmap f (Tensor [(x,y)]) = Tensor [(f x, y)]  
tenmap f t = foldl1 (+) (map (tenmap f) $ splitToTerms t)

fromScalar :: (Num k) => k -> Tensor k 
fromScalar c = (Tensor [(c,UnitPureTensor)]) 

fromPure :: (Num k) => PureTensor -> Tensor k
fromPure x = Tensor [(fromInteger 1, x)]

(.*) :: (Num k) => k -> Tensor k-> Tensor k
(.*) c t =  (fromScalar c)*t

-- differentials, you can add them
data Differential k = Differential (S -> Tensor k)
(diffAdd) (Differential d1) (Differential d2) = Differential (\x -> (d1 x) + (d2 x)) 
(diffCompose) dd1 (Differential d2) = Differential (\x -> applydifferential dd1 (d2 x))


data Homomorphism k = Homomorphism (S -> Tensor k)
(homAdd) (Homomorphism f1) (Homomorphism f2) = Homomorphism (\x -> (f1 x) + (f2 x)) 


----------------------
--
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


isPolyZero x = isPolyZero' $ cleanUpPoly x
isPolyZero' (Poly []) = True
isPolyZero' (Poly ((coeff, po):ts)) = if coeff /= 0 then False else isPolyZero' (Poly ts)

customShow = show
--customShow :: CC -> String
--customShow x = "(" ++ (cshow $ realPart x ) ++ " + " ++ (cshow $ imagPart x) ++ "*I)" where cshow a = if a == 0 then "0.0" else show a
        
xi ::  Int -> Poly
xi i = Poly $ [(1, Monom ((take i [0,0..]) ++ [1]))]

cleanUpPoly :: Poly -> Poly
cleanUpPoly (Poly []) = Poly []
cleanUpPoly (Poly ((coeff, po):ts)) = let filterAndAdd :: Monom -> Poly -> (Poly, K)
                                          filterAndAdd _ (Poly []) = (Poly [],0)
                                          filterAndAdd m (Poly ((co, mo):rest)) = if (mo == m) then (fst $ filterAndAdd m (Poly rest) ,co + (snd $ filterAndAdd m (Poly rest)))
                                                                                               else ((Poly ([(co,mo)] ++ (termsOf (fst $ filterAndAdd m (Poly rest))))) , (snd $ filterAndAdd m ( Poly rest)))
                                          fdrest = filterAndAdd po (Poly ts)
                                      in ((Poly [(coeff + (snd $ fdrest), po)]) + (cleanUpPoly $ fst fdrest))
 
termsOf :: Poly -> [(K,Monom)]
termsOf (Poly a) = a

constantPoly x = Poly [(x,Monom [])]



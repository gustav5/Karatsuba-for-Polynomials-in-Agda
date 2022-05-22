{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
import Test.QuickCheck

xs = [1,2,3,4,5,6,7]
ys = [1,2,3,4,5,6,7]
a= [4,5,6,7]
b = [1,2,3]
d = [2,2,2]
c=[2,2,2,2,2,2,2]
addPoly :: [Integer] -> [Integer] -> [Integer]
addPoly [] ys = ys
addPoly xs [] = xs
addPoly (x:xs) (y:ys) = x + y : addPoly xs ys 



subPoly :: [Integer] -> [Integer] -> [Integer]
subPoly xs ys = addPoly xs (negPoly ys)

negPoly :: [Integer] -> [Integer]
negPoly [] = []
negPoly (x:xs) = (-x) : negPoly xs  

shiftRight :: Integer-> [Integer] -> [Integer]
shiftRight 0 xs = xs
shiftRight n xs = 0 : (shiftRight (toInteger  (n - 1)) xs)


mulPoly :: [Integer] -> [Integer] -> [Integer]
mulPoly [] ys = []
mulPoly xs [] = []
mulPoly (x:xs) ys = addPoly (map (x*) ys) (0:mulPoly xs ys)


min_len :: [Integer] -> [Integer] -> (([Integer],[Integer]), ([Integer],[Integer]))
min_len xs ys = let m = min (div (length xs) 2) (div (length ys) 2) in 
    ((take m xs,drop m xs), (take m ys,drop m ys))
        

ab_cd_simple :: [Integer] -> [Integer] -> [Integer]
ab_cd_simple xs ys = (a `mulPoly` d) `addPoly` (b `mulPoly` c)
                where
                    m = min (div (length xs) 2) (div (length ys) 2)
                    b = take m xs
                    a = drop m xs
                    d = take m ys
                    c = drop m ys

ab_cd :: [Integer] -> [Integer] -> [Integer]
ab_cd xs ys = (((a `addPoly` b) `mulPoly` (c `addPoly` d)) `subPoly` (a `mulPoly` c)) `subPoly` (b `mulPoly` d)
                where
                    m = min (div (length xs) 2) (div (length ys) 2)
                    b = take m xs
                    a = drop m xs
                    d = take m ys
                    c = drop m ys
-----------------------------------------

------------------- Karatsuba

karatsuba :: [Integer] -> [Integer] -> [Integer]
karatsuba xs ys = if length xs <= 2 || length ys <= 2
    then mulPoly xs ys
    else ((shiftRight (toInteger (2 * m)) ac) `addPoly` (shiftRight (toInteger m) ad_plus_bc)) `addPoly`  bd
        where
        m = min (div (length xs) 2) (div (length ys) 2)
        b = take m xs
        a = drop m xs
        d = take m ys
        c = drop m ys
        ac = karatsuba a c
        bd = karatsuba b d
        a_plus_b = addPoly a b
        c_plus_d = addPoly c d
        ad_plus_bc = ((karatsuba a_plus_b c_plus_d) `subPoly` ac) `subPoly` bd 
-----------------------------------------
------------------- Test

dropZeroes :: [Integer] -> [Integer]
dropZeroes xs = reverse $ dropWhile (==0) $ reverse xs

prop :: [Integer] -> [Integer] -> Bool
prop a b =   karatsuba a b == mulPoly a b
-- quickCheck (withMaxSuccess 1000 prop)

prop2 :: [Integer] -> [Integer] -> Bool
prop2 xs ys = ab_cd xs ys == ab_cd_simple xs ys
-- quickCheck (verbose prop2)


prop3 :: [Integer] -> [Integer] -> Bool
prop3 a b =   mulPoly a b == mulPoly b a
-- quickCheck (withMaxSuccess 1000 prop)

prop4 :: [Integer] -> [Integer] -> Property
prop4 xs ys = (xs /= []) && (ys /= []) ==> length (xs `mulPoly` ys) == length xs + length ys - 1
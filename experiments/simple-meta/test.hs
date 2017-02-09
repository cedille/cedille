test :: (Integer -> [Integer]) -> [Integer -> Integer]
test f = if null (f 0) then []
         else (headf f : test (tailf f))
  where headf f n = head (f n)
        tailf f n = tail (f n)


example :: Integer -> [Integer]
example x = [1 + x, 2 + x , 3 + x]

evall :: [Integer -> Integer] -> [Integer]
evall (f : fs) = (f 10) : (evall fs)
evall [] = []

f n = case quotRem n 2 of
            (k, 0) -> (3*k)+1
            (k, 1) -> (3*k)+2

t = take 30 $ iterate f 0
t1 = take 30 $ iterate f 1

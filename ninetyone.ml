contract mc91 = {n | true} -> {z | if n <=101 then z = 91 else z = n- 10}
let rec mc91 x = 
  if x > 100 then x - 10 
  else mc91 (mc91 (x + 11))

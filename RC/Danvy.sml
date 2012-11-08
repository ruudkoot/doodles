datatype mobile = OBJ of int
                | BAR of int * mobile * mobile

fun equil7 m
    = SMLofNJ.Cont.callcc (fn k => let fun visit (OBJ n)
                                            = n
                                        | visit (BAR (n, m1, m2))
                                            = let val n1 = visit m1
                                                  val n2 = visit m2
                                              in if n1 = n2
                                                 then n + n1 + n2
                                                 else SMLofNJ.Cont.throw k false
                                              end
                                  in let val _ = visit m
                                     in true 
                                     end
                                  end)

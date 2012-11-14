
(*if you define the type of streams of units:*)

CoInductive Stream : Set :=
 | cons : Stream -> Stream.

CoFixpoint ones : Stream := cons ones.


Goal 1=1. 

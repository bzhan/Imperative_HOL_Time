chapter Imperative_HOL_Time

session SepLogicTime_Base = HOL +
  sessions
    Auto2_Imperative_HOL
    Berlekamp_Zassenhaus
    Akra_Bazzi
    Amortized_Complexity
  theories [document = false]
    "Berlekamp_Zassenhaus.Karatsuba_Multiplication"
    "Akra_Bazzi.Akra_Bazzi_Method"
    "Amortized_Complexity.Splay_Tree_Analysis"
    "Amortized_Complexity.Skew_Heap_Analysis"

session SepLogicTime_Fun = SepLogicTime_Base +
  description \<open>
    Functional algorithms
\<close>
  sessions
    Auto2_HOL
  theories
    "SepLogicTime/BinarySearch"
    "SepLogicTime/MergeSort"
    "SepLogicTime/Select"
    "SepLogicTime/Karatsuba"
    "SepLogicTime/Knapsack"

session SepLogicTime_Impl = SepLogicTime_Fun +
  description \<open>
    Separation logic with time.
\<close>
  sessions
    Auto2_HOL
  theories
    "SepLogicTime/Sep_Time_Examples"

session SepLogicTime_RBTreeBasic = SepLogicTime_Base +
  sessions
    Auto2_HOL
  theories
    "SepLogicTime/RBTree_Impl"
    "SepLogicTime/LinkedList"
    "SepLogicTime/DynamicArray2"
    "Asymptotics/Asymptotics_2D"
    "SepLogicTime/MergeSort_Impl"
                      

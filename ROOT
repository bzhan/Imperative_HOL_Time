chapter Imperative_HOL_Time

session SepLogicTime_Base = HOL +
  sessions
    Berlekamp_Zassenhaus
    Akra_Bazzi
    Amortized_Complexity
  theories [document = false]
    "Berlekamp_Zassenhaus.Karatsuba_Multiplication"
    "Akra_Bazzi.Akra_Bazzi_Method"
    "Amortized_Complexity.Splay_Tree_Analysis"
    "Amortized_Complexity.Skew_Heap_Analysis"

session SepLogicTime_Fun = SepLogicTime_Base +
  description {*
    Functional algorithms
  *}
  sessions
    Auto2_HOL DataStrs
  theories
    "SepLogicTime/BinarySearch"
    "SepLogicTime/MergeSort"
    "SepLogicTime/Select"
    "SepLogicTime/Karatsuba"
    "SepLogicTime/Knapsack"

session SepLogicTime_Impl = SepLogicTime_Fun +
  description {*
    Separation logic with time.
  *}
  sessions
    SepLogic
  theories
    "SepLogicTime/Sep_Time_Examples"

session SepLogicTime_RBTreeBasic = SepLogicTime_Base +
  sessions
    SepLogic DataStrs
  theories
    "SepLogicTime/RBTree_Impl"
    "SepLogicTime/DynamicArray2"
    "SepLogicTime/Asymptotics_2D"
                      

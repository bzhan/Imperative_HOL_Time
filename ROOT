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
  theories
    "SepLogicTime/Asymptotics_Test"
    "SepLogicTime/LinkedList"
    "SepLogicTime/BinarySearch_Impl"
    "SepLogicTime/MergeSort_Impl"
    "SepLogicTime/Select_Impl"
    "SepLogicTime/Karatsuba_Impl"
    "SepLogicTime/SimpleExample"
    "SepLogicTime/Knapsack_Impl"
    "SepLogicTime/Skew_Heap_Impl"
    "SepLogicTime/Splay_Tree_Impl"

chapter Imperative_HOL_Time


session SepLogicTime_Prereq in "SepLogicTime_Prereq" = HOL +
  sessions
    Auto2_Imperative_HOL
    Berlekamp_Zassenhaus
    Akra_Bazzi
    Amortized_Complexity
    Median_Of_Medians_Selection
  theories [document = false]
    "Berlekamp_Zassenhaus.Karatsuba_Multiplication"
    "Akra_Bazzi.Akra_Bazzi_Method"
    "Amortized_Complexity.Splay_Tree_Analysis"
    "Amortized_Complexity.Skew_Heap_Analysis"
    "Median_Of_Medians_Selection.Median_Of_Medians_Selection"

(* Session with all the Examples in Imperative HOL Time *)
session Imperative_HOL_Time = SepLogicTime_Prereq +
  description \<open>
    Separation logic with time.
\<close>
  sessions
    "HOL-Imperative_HOL"
    "HOL-Library"
  directories
    "Examples"
    "Asymptotics"
    "SepLogicTime"
    "Functional"
  theories
    "IHT_Examples"
    "SLTC_Main"

(* smaller sessions *)
session Imperative_HOL_Time_Base in "Imperative_HOL_Time_Base" = HOL +
  sessions
    "Imperative_HOL_Time"
  theories
    "Imperative_HOL_Time.Imperative_HOL_Time"

session SepLogicTime_Base in "SepLogicTime_Base" =  Imperative_HOL_Time_Base +
  sessions
    Imperative_HOL_Time
  theories
    "Imperative_HOL_Time.SLTC_Main"

session SepLogicTime_Asymptotics in "SepLogicTime_Asymptotics" = Akra_Bazzi +
  sessions
    Imperative_HOL_Time
  theories
    "Imperative_HOL_Time.Asymptotics_Test"

session SepLogicTime_Fun in "SepLogicTime_Fun" = SepLogicTime_Prereq +
  description \<open>
    Functional algorithms
\<close>
  sessions
    Imperative_HOL_Time
  theories
    "Imperative_HOL_Time.BinarySearch"
    "Imperative_HOL_Time.MergeSort"
    "Imperative_HOL_Time.Select"
    "Imperative_HOL_Time.Karatsuba"
    "Imperative_HOL_Time.Knapsack"

(* Session with a limited number of Data Structures and simple Algorithms.
    Does not contain all the examples
    Serves as entry point for Separation Logic for Imperative-HOL-Time. *)
session Imperative_HOL_Time_Entry in "SepLogicTime_Entry" = SepLogicTime_Fun +
  sessions
    Imperative_HOL_Time
  theories
    "Imperative_HOL_Time.SLTC_Main"
    "Imperative_HOL_Time.IHT_Red_Black_Tree"
    "Imperative_HOL_Time.IHT_Linked_List"
    "Imperative_HOL_Time.IHT_Dynamic_Array_More"
    "Imperative_HOL_Time.Asymptotics_2D"
    "Imperative_HOL_Time.IHT_Mergesort"
                      

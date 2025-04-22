CoInductive stream (A : Type) : Type :=
    str : A -> stream A -> stream A.
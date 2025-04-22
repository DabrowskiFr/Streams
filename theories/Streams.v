
Declare Scope stream_scope.

Open Scope stream_scope.

CoInductive stream (A : Type) : Type :=
    str : A -> stream A -> stream A.

Arguments str [A].

Infix "⋅" := str (at level 60, right associativity): stream_scope.    

Definition unfold {A : Type} (s : stream A) : stream A :=
    match s with str a s => str a s end.

Lemma unfoldEq : 
    forall (A : Type) (s : stream A), s = unfold s.
Proof.
    destruct s; reflexivity.
Qed.

Section Op.
    
    Context {A : Type}.

    Definition current (s : stream A) : A :=
        match s with 
            str a s => a
        end.

    Fixpoint shift (n : nat) (s : stream A)  : stream A := 
        match n, s with 
            | 0, _ => s 
            | S n, str a s => shift n s
        end.

    Definition nth_stream (n : nat) (s : stream A) : A :=
        current (shift n s).

    Fixpoint prefixn (n : nat) (s : stream A) : list A :=
        match n, s with 
            | 0, _ => nil 
            | S n, str a s => cons a (prefixn n s)
        end.

    Fixpoint append (l : list A) (s : stream A) : stream A :=
        match l with 
            | nil => s 
            | cons a l => str a (append l s)
        end.
        
    Lemma prefixn_append : 
        forall (n : nat) (s : stream A), 
            append (prefixn n s) (shift n s) = s.
    Proof.
        induction n as [ | n IHn].
        -   reflexivity.
        -   intros [a s]; simpl.
            rewrite IHn; reflexivity.
    Qed.

End Op.

Notation hd := current.
Notation tl := (shift 1).


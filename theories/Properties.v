From Streams Require Import Streams.

Section Properties.

    Context {A : Type}.

    Definition safety (P : stream A -> Prop) : Prop :=
        forall s, 
            (forall n, exists s' : stream A,
                P (append (prefixn n s) s')) -> P s.

    Definition liveness (P : stream A -> Prop) : Prop :=
        forall l, exists s, P (append l s).

End Properties.

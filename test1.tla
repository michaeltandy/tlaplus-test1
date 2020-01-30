------------------------------- MODULE test1 -------------------------------

EXTENDS Naturals, TLC, Integers, Sequences, FiniteSets

(* --algorithm transfer

variable S = [a |-> [in |-> 0, out |-> 0], b |-> [in |-> 0, out |-> 0]];

define
  fwChan(p) == IF p = "ChanA" THEN "a" ELSE "b"
  txChan(p) == IF p = "SendPing" THEN "a" ELSE "b"
  rxChan(p) == IF p = "SendPing" THEN "b" ELSE "a"
end define;

process ChannelA \in {"ChanA", "ChanB"}
begin LoopChA:
  while TRUE do
   A: assert S[fwChan(self)].in = 0;
      await S[fwChan(self)].in /= 0;
        either
          \* Message successfully delivered 
          S[fwChan(self)].out := S[fwChan(self)].in || S[fwChan(self)].in := 0;
        or
          \* Message lost in transit
          S[fwChan(self)].in := 0;
        end either;
   B: await S[fwChan(self)].out = 0;
  end while;
end process;

process SendPing \in { "SendPing" }
begin
  Send: S[txChan(self)].in := 123;
  Wait: await (S[rxChan(self)].out /= 0);
        assert S[rxChan(self)].out = 321;
end process

process PingToPong \in { "PingToPong" }
begin
  AwaitPing: await (S[rxChan(self)].out /= 0);
             assert S[rxChan(self)].out = 123;
  SendPong: S[txChan(self)].in := 321;
end process

end algorithm *)

\* BEGIN TRANSLATION
VARIABLES S, pc

(* define statement *)
fwChan(p) == IF p = "ChanA" THEN "a" ELSE "b"
txChan(p) == IF p = "SendPing" THEN "a" ELSE "b"
rxChan(p) == IF p = "SendPing" THEN "b" ELSE "a"


vars == << S, pc >>

ProcSet == ({"ChanA", "ChanB"}) \cup ({ "SendPing" }) \cup ({ "PingToPong" })

Init == (* Global variables *)
        /\ S = [a |-> [in |-> 0, out |-> 0], b |-> [in |-> 0, out |-> 0]]
        /\ pc = [self \in ProcSet |-> CASE self \in {"ChanA", "ChanB"} -> "LoopChA"
                                        [] self \in { "SendPing" } -> "Send"
                                        [] self \in { "PingToPong" } -> "AwaitPing"]

LoopChA(self) == /\ pc[self] = "LoopChA"
                 /\ pc' = [pc EXCEPT ![self] = "A"]
                 /\ S' = S

A(self) == /\ pc[self] = "A"
           /\ Assert(S[fwChan(self)].in = 0, 
                     "Failure of assertion at line 18, column 7.")
           /\ S[fwChan(self)].in /= 0
           /\ \/ /\ S' = [S EXCEPT ![fwChan(self)].out = S[fwChan(self)].in,
                                   ![fwChan(self)].in = 0]
              \/ /\ S' = [S EXCEPT ![fwChan(self)].in = 0]
           /\ pc' = [pc EXCEPT ![self] = "B"]

B(self) == /\ pc[self] = "B"
           /\ S[fwChan(self)].out = 0
           /\ pc' = [pc EXCEPT ![self] = "LoopChA"]
           /\ S' = S

ChannelA(self) == LoopChA(self) \/ A(self) \/ B(self)

Send(self) == /\ pc[self] = "Send"
              /\ S' = [S EXCEPT ![txChan(self)].in = 123]
              /\ pc' = [pc EXCEPT ![self] = "Wait"]

Wait(self) == /\ pc[self] = "Wait"
              /\ (S[rxChan(self)].out /= 0)
              /\ Assert(S[rxChan(self)].out = 321, 
                        "Failure of assertion at line 35, column 9.")
              /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ S' = S

SendPing(self) == Send(self) \/ Wait(self)

AwaitPing(self) == /\ pc[self] = "AwaitPing"
                   /\ (S[rxChan(self)].out /= 0)
                   /\ Assert(S[rxChan(self)].out = 123, 
                             "Failure of assertion at line 41, column 14.")
                   /\ pc' = [pc EXCEPT ![self] = "SendPong"]
                   /\ S' = S

SendPong(self) == /\ pc[self] = "SendPong"
                  /\ S' = [S EXCEPT ![txChan(self)].in = 321]
                  /\ pc' = [pc EXCEPT ![self] = "Done"]

PingToPong(self) == AwaitPing(self) \/ SendPong(self)

Next == (\E self \in {"ChanA", "ChanB"}: ChannelA(self))
           \/ (\E self \in { "SendPing" }: SendPing(self))
           \/ (\E self \in { "PingToPong" }: PingToPong(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

ChannelInvariant == (S.a.in = 0 \/ S.a.out = 0) /\ (S.b.in = 0 \/ S.b.out = 0)

=============================================================================
\* Modification History
\* Last modified Thu Jan 30 22:15:44 GMT 2020 by mtandy
\* Created Tue Jan 28 23:30:18 GMT 2020 by mtandy

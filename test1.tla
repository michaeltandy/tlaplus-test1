------------------------------- MODULE test1 -------------------------------

EXTENDS Naturals, TLC, Integers, Sequences, FiniteSets

CONSTANT LossyChannel

(* --algorithm transfer

variable S = [a |-> [in |-> 0, out |-> 0], b |-> [in |-> 0, out |-> 0]];

define
  fwChan(p) == IF p = "ChanA" THEN "a" ELSE "b"
  txChan(p) == IF p = "SendPing" THEN "a" ELSE "b"
  rxChan(p) == IF p = "SendPing" THEN "b" ELSE "a"
  receive(p) == S[rxChan(p)].out
end define;

macro transmit(toTx) begin
    assert S[txChan(self)].in = 0;
    S[txChan(self)].in := toTx;
end macro;

fair process ChanSim \in {"ChanA", "ChanB"}
begin ChanSim:
  while TRUE do
   A: assert S[fwChan(self)].out = 0;
      await S[fwChan(self)].in /= 0;
        if LossyChannel then
          either
            \* Message successfully delivered 
            S[fwChan(self)].out := S[fwChan(self)].in || S[fwChan(self)].in := 0;
          or
          \* Message lost in transit
            S[fwChan(self)].in := 0;
          end either;
        else
          \* Message always delivered 
          S[fwChan(self)].out := S[fwChan(self)].in || S[fwChan(self)].in := 0;
        end if;          
   B: await S[fwChan(self)].out = 0;
  end while;
end process;

fair process SendPing \in { "SendPing" }
begin
  Send: transmit(123);
  Wait: await (receive(self) /= 0);
        assert receive(self) = 321;
  \*DonePing: S[rxChan(self)].out := 0
end process

fair process PingToPong \in { "PingToPong" }
begin
  AwaitPing: await (receive(self) /= 0);
             assert receive(self) = 123;
  SendPong: transmit(321);
  \*DonePong: S[rxChan(self)].out := 0
end process

end algorithm *)

\* BEGIN TRANSLATION
\* Label ChanSim of process ChanSim at line 25 col 3 changed to ChanSim_
VARIABLES S, pc

(* define statement *)
fwChan(p) == IF p = "ChanA" THEN "a" ELSE "b"
txChan(p) == IF p = "SendPing" THEN "a" ELSE "b"
rxChan(p) == IF p = "SendPing" THEN "b" ELSE "a"
receive(p) == S[rxChan(p)].out


vars == << S, pc >>

ProcSet == ({"ChanA", "ChanB"}) \cup ({ "SendPing" }) \cup ({ "PingToPong" })

Init == (* Global variables *)
        /\ S = [a |-> [in |-> 0, out |-> 0], b |-> [in |-> 0, out |-> 0]]
        /\ pc = [self \in ProcSet |-> CASE self \in {"ChanA", "ChanB"} -> "ChanSim_"
                                        [] self \in { "SendPing" } -> "Send"
                                        [] self \in { "PingToPong" } -> "AwaitPing"]

ChanSim_(self) == /\ pc[self] = "ChanSim_"
                  /\ pc' = [pc EXCEPT ![self] = "A"]
                  /\ S' = S

A(self) == /\ pc[self] = "A"
           /\ Assert(S[fwChan(self)].out = 0, 
                     "Failure of assertion at line 26, column 7.")
           /\ S[fwChan(self)].in /= 0
           /\ IF LossyChannel
                 THEN /\ \/ /\ S' = [S EXCEPT ![fwChan(self)].out = S[fwChan(self)].in,
                                              ![fwChan(self)].in = 0]
                         \/ /\ S' = [S EXCEPT ![fwChan(self)].in = 0]
                 ELSE /\ S' = [S EXCEPT ![fwChan(self)].out = S[fwChan(self)].in,
                                        ![fwChan(self)].in = 0]
           /\ pc' = [pc EXCEPT ![self] = "B"]

B(self) == /\ pc[self] = "B"
           /\ S[fwChan(self)].out = 0
           /\ pc' = [pc EXCEPT ![self] = "ChanSim_"]
           /\ S' = S

ChanSim(self) == ChanSim_(self) \/ A(self) \/ B(self)

Send(self) == /\ pc[self] = "Send"
              /\ Assert(S[txChan(self)].in = 0, 
                        "Failure of assertion at line 19, column 5 of macro called at line 46, column 9.")
              /\ S' = [S EXCEPT ![txChan(self)].in = 123]
              /\ pc' = [pc EXCEPT ![self] = "Wait"]

Wait(self) == /\ pc[self] = "Wait"
              /\ (receive(self) /= 0)
              /\ Assert(receive(self) = 321, 
                        "Failure of assertion at line 48, column 9.")
              /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ S' = S

SendPing(self) == Send(self) \/ Wait(self)

AwaitPing(self) == /\ pc[self] = "AwaitPing"
                   /\ (receive(self) /= 0)
                   /\ Assert(receive(self) = 123, 
                             "Failure of assertion at line 55, column 14.")
                   /\ pc' = [pc EXCEPT ![self] = "SendPong"]
                   /\ S' = S

SendPong(self) == /\ pc[self] = "SendPong"
                  /\ Assert(S[txChan(self)].in = 0, 
                            "Failure of assertion at line 19, column 5 of macro called at line 56, column 13.")
                  /\ S' = [S EXCEPT ![txChan(self)].in = 321]
                  /\ pc' = [pc EXCEPT ![self] = "Done"]

PingToPong(self) == AwaitPing(self) \/ SendPong(self)

Next == (\E self \in {"ChanA", "ChanB"}: ChanSim(self))
           \/ (\E self \in { "SendPing" }: SendPing(self))
           \/ (\E self \in { "PingToPong" }: PingToPong(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {"ChanA", "ChanB"} : WF_vars(ChanSim(self))
        /\ \A self \in { "SendPing" } : WF_vars(SendPing(self))
        /\ \A self \in { "PingToPong" } : WF_vars(PingToPong(self))

\* END TRANSLATION

ChannelInvariant == (S.a.in = 0 \/ S.a.out = 0) /\ (S.b.in = 0 \/ S.b.out = 0)

=============================================================================
\* Modification History
\* Last modified Thu Jan 30 23:09:00 GMT 2020 by mtandy
\* Created Tue Jan 28 23:30:18 GMT 2020 by mtandy

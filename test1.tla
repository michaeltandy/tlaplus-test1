------------------------------- MODULE test1 -------------------------------

EXTENDS Naturals, TLC, Integers, Sequences, FiniteSets

CONSTANT MaxDroppedMessageRun

(* --algorithm transfer

variables S = [a |-> [in |-> 0, out |-> 0], b |-> [in |-> 0, out |-> 0]],
Timer = [a |-> -1, b |-> -1, SendPing |-> -1, PingToPong |-> -1];

define
  fwChan(p) == IF p = "ChanA" THEN "a" ELSE "b"
  txChan(p) == IF p = "SendPing" THEN "a" ELSE "b"
  rxChan(p) == IF p = "SendPing" THEN "b" ELSE "a"
  receive(p) == S[rxChan(p)].out
end define;

macro transmit(toTx) begin
    assert S[txChan(self)].in = 0;
    S[txChan(self)].in := toTx;
    Timer[txChan(self)] := 2 || Timer[self] := 10;
end macro;

fair process TimerTick \in {"TimerTick"}
begin TimerTick:
  while TRUE do
   TT: await (~\E x \in DOMAIN Timer : Timer[x] = 0);
       await (\E x \in DOMAIN Timer : Timer[x] > 0);
       Timer["a"] := IF Timer["a"]>0 THEN Timer["a"]-1 ELSE Timer["a"] || Timer["b"] := IF Timer["b"]>0 THEN Timer["b"]-1 ELSE Timer["b"] || Timer["SendPing"] := IF Timer["SendPing"]>0 THEN Timer["SendPing"]-1 ELSE Timer["SendPing"] || Timer["PingToPong"] := IF Timer["PingToPong"]>0 THEN Timer["PingToPong"]-1 ELSE Timer["PingToPong"];
       \*with t \in DOMAIN Timer do
       \*  if Timer[t] > 0 then
       \*    Timer[t] := Timer[t]-1;
       \*  end if; 
       \*end with;
  end while;
end process;

fair process ChanSim \in {"ChanA", "ChanB"}
  variables droppedMessageRun = 0;
begin ChanSim:
  while TRUE do
   A: assert S[fwChan(self)].out = 0;
      await S[fwChan(self)].in /= 0;
        if droppedMessageRun < MaxDroppedMessageRun then
          either
            \* Message successfully delivered 
            S[fwChan(self)].out := S[fwChan(self)].in || S[fwChan(self)].in := 0;
            droppedMessageRun := 0;
          or
            \* Message lost in transit
            S[fwChan(self)].in := 0;
            droppedMessageRun := droppedMessageRun + 1;
          end either;
        else
          \* Message always delivered
          droppedMessageRun := 0; 
          S[fwChan(self)].out := S[fwChan(self)].in || S[fwChan(self)].in := 0;
        end if;
        Timer[fwChan(self)] := -1;
   B: await S[fwChan(self)].out = 0;
  end while;
end process;

fair process SendPing \in { "SendPing" }
begin
  Send: transmit(123);
  Wait: await (receive(self) /= 0) \/ (Timer[self] = 0);
        if receive(self) /= 0 then
            assert receive(self) = 321;
            S[rxChan(self)].out := 0;
        else
            Timer[self] := -1;
            goto Send;
        end if;
end process

fair process PingToPong \in { "PingToPong" }
begin Qwer:
  while TRUE do
    AwaitPing: await (receive(self) /= 0);
               assert receive(self) = 123;
               transmit(321);
    AfterPong: S[rxChan(self)].out := 0;
               Timer[self] := -1;
    AwaitSend: await (S[txChan(self)].in = 0);
  end while
end process

end algorithm *)

\* BEGIN TRANSLATION
\* Label TimerTick of process TimerTick at line 27 col 3 changed to TimerTick_
\* Label ChanSim of process ChanSim at line 42 col 3 changed to ChanSim_
VARIABLES S, Timer, pc

(* define statement *)
fwChan(p) == IF p = "ChanA" THEN "a" ELSE "b"
txChan(p) == IF p = "SendPing" THEN "a" ELSE "b"
rxChan(p) == IF p = "SendPing" THEN "b" ELSE "a"
receive(p) == S[rxChan(p)].out

VARIABLE droppedMessageRun

vars == << S, Timer, pc, droppedMessageRun >>

ProcSet == ({"TimerTick"}) \cup ({"ChanA", "ChanB"}) \cup ({ "SendPing" }) \cup ({ "PingToPong" })

Init == (* Global variables *)
        /\ S = [a |-> [in |-> 0, out |-> 0], b |-> [in |-> 0, out |-> 0]]
        /\ Timer = [a |-> -1, b |-> -1, SendPing |-> -1, PingToPong |-> -1]
        (* Process ChanSim *)
        /\ droppedMessageRun = [self \in {"ChanA", "ChanB"} |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in {"TimerTick"} -> "TimerTick_"
                                        [] self \in {"ChanA", "ChanB"} -> "ChanSim_"
                                        [] self \in { "SendPing" } -> "Send"
                                        [] self \in { "PingToPong" } -> "Qwer"]

TimerTick_(self) == /\ pc[self] = "TimerTick_"
                    /\ pc' = [pc EXCEPT ![self] = "TT"]
                    /\ UNCHANGED << S, Timer, droppedMessageRun >>

TT(self) == /\ pc[self] = "TT"
            /\ (~\E x \in DOMAIN Timer : Timer[x] = 0)
            /\ (\E x \in DOMAIN Timer : Timer[x] > 0)
            /\ Timer' = [Timer EXCEPT !["a"] = IF Timer["a"]>0 THEN Timer["a"]-1 ELSE Timer["a"],
                                      !["b"] = IF Timer["b"]>0 THEN Timer["b"]-1 ELSE Timer["b"],
                                      !["SendPing"] = IF Timer["SendPing"]>0 THEN Timer["SendPing"]-1 ELSE Timer["SendPing"],
                                      !["PingToPong"] = IF Timer["PingToPong"]>0 THEN Timer["PingToPong"]-1 ELSE Timer["PingToPong"]]
            /\ pc' = [pc EXCEPT ![self] = "TimerTick_"]
            /\ UNCHANGED << S, droppedMessageRun >>

TimerTick(self) == TimerTick_(self) \/ TT(self)

ChanSim_(self) == /\ pc[self] = "ChanSim_"
                  /\ pc' = [pc EXCEPT ![self] = "A"]
                  /\ UNCHANGED << S, Timer, droppedMessageRun >>

A(self) == /\ pc[self] = "A"
           /\ Assert(S[fwChan(self)].out = 0, 
                     "Failure of assertion at line 43, column 7.")
           /\ S[fwChan(self)].in /= 0
           /\ IF droppedMessageRun[self] < MaxDroppedMessageRun
                 THEN /\ \/ /\ S' = [S EXCEPT ![fwChan(self)].out = S[fwChan(self)].in,
                                              ![fwChan(self)].in = 0]
                            /\ droppedMessageRun' = [droppedMessageRun EXCEPT ![self] = 0]
                         \/ /\ S' = [S EXCEPT ![fwChan(self)].in = 0]
                            /\ droppedMessageRun' = [droppedMessageRun EXCEPT ![self] = droppedMessageRun[self] + 1]
                 ELSE /\ droppedMessageRun' = [droppedMessageRun EXCEPT ![self] = 0]
                      /\ S' = [S EXCEPT ![fwChan(self)].out = S[fwChan(self)].in,
                                        ![fwChan(self)].in = 0]
           /\ Timer' = [Timer EXCEPT ![fwChan(self)] = -1]
           /\ pc' = [pc EXCEPT ![self] = "B"]

B(self) == /\ pc[self] = "B"
           /\ S[fwChan(self)].out = 0
           /\ pc' = [pc EXCEPT ![self] = "ChanSim_"]
           /\ UNCHANGED << S, Timer, droppedMessageRun >>

ChanSim(self) == ChanSim_(self) \/ A(self) \/ B(self)

Send(self) == /\ pc[self] = "Send"
              /\ Assert(S[txChan(self)].in = 0, 
                        "Failure of assertion at line 20, column 5 of macro called at line 67, column 9.")
              /\ S' = [S EXCEPT ![txChan(self)].in = 123]
              /\ Timer' = [Timer EXCEPT ![txChan(self)] = 2,
                                        ![self] = 10]
              /\ pc' = [pc EXCEPT ![self] = "Wait"]
              /\ UNCHANGED droppedMessageRun

Wait(self) == /\ pc[self] = "Wait"
              /\ (receive(self) /= 0) \/ (Timer[self] = 0)
              /\ IF receive(self) /= 0
                    THEN /\ Assert(receive(self) = 321, 
                                   "Failure of assertion at line 70, column 13.")
                         /\ S' = [S EXCEPT ![rxChan(self)].out = 0]
                         /\ pc' = [pc EXCEPT ![self] = "Done"]
                         /\ Timer' = Timer
                    ELSE /\ Timer' = [Timer EXCEPT ![self] = -1]
                         /\ pc' = [pc EXCEPT ![self] = "Send"]
                         /\ S' = S
              /\ UNCHANGED droppedMessageRun

SendPing(self) == Send(self) \/ Wait(self)

Qwer(self) == /\ pc[self] = "Qwer"
              /\ pc' = [pc EXCEPT ![self] = "AwaitPing"]
              /\ UNCHANGED << S, Timer, droppedMessageRun >>

AwaitPing(self) == /\ pc[self] = "AwaitPing"
                   /\ (receive(self) /= 0)
                   /\ Assert(receive(self) = 123, 
                             "Failure of assertion at line 82, column 16.")
                   /\ Assert(S[txChan(self)].in = 0, 
                             "Failure of assertion at line 20, column 5 of macro called at line 83, column 16.")
                   /\ S' = [S EXCEPT ![txChan(self)].in = 321]
                   /\ Timer' = [Timer EXCEPT ![txChan(self)] = 2,
                                             ![self] = 10]
                   /\ pc' = [pc EXCEPT ![self] = "AfterPong"]
                   /\ UNCHANGED droppedMessageRun

AfterPong(self) == /\ pc[self] = "AfterPong"
                   /\ S' = [S EXCEPT ![rxChan(self)].out = 0]
                   /\ Timer' = [Timer EXCEPT ![self] = -1]
                   /\ pc' = [pc EXCEPT ![self] = "AwaitSend"]
                   /\ UNCHANGED droppedMessageRun

AwaitSend(self) == /\ pc[self] = "AwaitSend"
                   /\ (S[txChan(self)].in = 0)
                   /\ pc' = [pc EXCEPT ![self] = "Qwer"]
                   /\ UNCHANGED << S, Timer, droppedMessageRun >>

PingToPong(self) == Qwer(self) \/ AwaitPing(self) \/ AfterPong(self)
                       \/ AwaitSend(self)

Next == (\E self \in {"TimerTick"}: TimerTick(self))
           \/ (\E self \in {"ChanA", "ChanB"}: ChanSim(self))
           \/ (\E self \in { "SendPing" }: SendPing(self))
           \/ (\E self \in { "PingToPong" }: PingToPong(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {"TimerTick"} : WF_vars(TimerTick(self))
        /\ \A self \in {"ChanA", "ChanB"} : WF_vars(ChanSim(self))
        /\ \A self \in { "SendPing" } : WF_vars(SendPing(self))
        /\ \A self \in { "PingToPong" } : WF_vars(PingToPong(self))

\* END TRANSLATION

ChannelInvariant == (S.a.in = 0 \/ S.a.out = 0) /\ (S.b.in = 0 \/ S.b.out = 0)

\*ProgramFinished == pc["SendPing"]="Done" /\ pc["PingToPong"]="Done"
ProgramFinished == pc["SendPing"]="Done"

=============================================================================
\* Modification History
\* Last modified Wed Feb 05 22:45:25 GMT 2020 by mtandy
\* Created Tue Jan 28 23:30:18 GMT 2020 by mtandy

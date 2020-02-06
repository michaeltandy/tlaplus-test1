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
  
  ack == 1
  message == 2
end define;

macro transmit(toTx) begin
    assert S[txChan(self)].in = 0;
    S[txChan(self)].in := toTx;
    Timer[txChan(self)] := 2 || Timer[self] := 10;
end macro;

(*fair process TimerTick \in {"TimerTick"}
begin TimerTick:
  \*while TRUE do
       await (~\E x \in DOMAIN Timer : Timer[x] = 0);
       await (\E x \in DOMAIN Timer : Timer[x] > 0);
       Timer["a"] := IF Timer["a"]>0 THEN Timer["a"]-1 ELSE Timer["a"] || Timer["b"] := IF Timer["b"]>0 THEN Timer["b"]-1 ELSE Timer["b"] || Timer["SendPing"] := IF Timer["SendPing"]>0 THEN Timer["SendPing"]-1 ELSE Timer["SendPing"] || Timer["PingToPong"] := IF Timer["PingToPong"]>0 THEN Timer["PingToPong"]-1 ELSE Timer["PingToPong"];
       goto TimerTick;
       \*with t \in DOMAIN Timer do
       \*  if Timer[t] > 0 then
       \*    Timer[t] := Timer[t]-1;
       \*  end if; 
       \*end with;
  \*end while;
end process;*)

fair process ChanSim \in {"ChanA", "ChanB"}
  variables droppedMessageRun = 0;
begin ChanSim:
      await (S[fwChan(self)].in /= 0 /\ S[fwChan(self)].out = 0);
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
   goto ChanSim;
end process;

fair process AckedChannel \in { "SendPing", "PingToPong" }
  variables ackDue = FALSE;
begin InitChannel:
  either
      transmit(message);
      goto TransmittingData;
  or
      goto Idle;
  end either;
  
  Idle:
      await (receive(self) /= 0);
      if (receive(self) = message) then
          transmit(ack);
        t1: S[rxChan(self)].out := 0;
          goto TransmittingAckNotAwaiting
      else
          S[rxChan(self)].out := 0;
          goto Idle;
      end if;
      

  TransmittingAckNotAwaiting:
      await (S[txChan(self)].in = 0);
      Timer[self] := -1;
      goto Idle;
  
  TransmittingData:
      await (S[txChan(self)].in = 0 \/ receive(self) /= 0);
      if (receive(self) = message) /\ (S[txChan(self)].in = 0) then
          transmit(ack);
        t2: S[rxChan(self)].out := 0;
          goto TransmittingAckAwaitingAck;
      elsif (receive(self) = message) then
          S[rxChan(self)].out := 0;
          ackDue := TRUE;
          goto TransmittingData;
      elsif (S[txChan(self)].in = 0) then
          if ackDue then
              ackDue := FALSE;
              transmit(ack);
              goto TransmittingAckAwaitingAck;
          else
              goto AwaitingAck;
          end if;
      else
          S[rxChan(self)].out := 0;
          goto TransmittingAckAwaitingAck;
      end if;
      
  
  TransmittingAckAwaitingAck:
      await (S[txChan(self)].in = 0 \/ receive(self) = ack);
      if (receive(self) = ack) then
          S[rxChan(self)].out := 0;
          goto TransmittingAckNotAwaiting;
      elsif (S[txChan(self)].in = 0) then
          goto AwaitingAck;
      else
          goto TransmittingAckAwaitingAck;
      end if;
      
  AwaitingAck:
      await (receive(self) /= 0);
      if (receive(self) = ack) then
          S[rxChan(self)].out := 0;
          goto Idle;
      elsif (receive(self) = message) then
          transmit(ack);
        t4: S[rxChan(self)].out := 0;
          goto TransmittingAckAwaitingAck;
      else
          goto AwaitingAck;
      end if;
      
end process

end algorithm *)

\* BEGIN TRANSLATION
\* Label ChanSim of process ChanSim at line 46 col 7 changed to ChanSim_
VARIABLES S, Timer, pc

(* define statement *)
fwChan(p) == IF p = "ChanA" THEN "a" ELSE "b"
txChan(p) == IF p = "SendPing" THEN "a" ELSE "b"
rxChan(p) == IF p = "SendPing" THEN "b" ELSE "a"
receive(p) == S[rxChan(p)].out

ack == 1
message == 2

VARIABLES droppedMessageRun, ackDue

vars == << S, Timer, pc, droppedMessageRun, ackDue >>

ProcSet == ({"ChanA", "ChanB"}) \cup ({ "SendPing", "PingToPong" })

Init == (* Global variables *)
        /\ S = [a |-> [in |-> 0, out |-> 0], b |-> [in |-> 0, out |-> 0]]
        /\ Timer = [a |-> -1, b |-> -1, SendPing |-> -1, PingToPong |-> -1]
        (* Process ChanSim *)
        /\ droppedMessageRun = [self \in {"ChanA", "ChanB"} |-> 0]
        (* Process AckedChannel *)
        /\ ackDue = [self \in { "SendPing", "PingToPong" } |-> FALSE]
        /\ pc = [self \in ProcSet |-> CASE self \in {"ChanA", "ChanB"} -> "ChanSim_"
                                        [] self \in { "SendPing", "PingToPong" } -> "InitChannel"]

ChanSim_(self) == /\ pc[self] = "ChanSim_"
                  /\ (S[fwChan(self)].in /= 0 /\ S[fwChan(self)].out = 0)
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
                  /\ pc' = [pc EXCEPT ![self] = "ChanSim_"]
                  /\ UNCHANGED ackDue

ChanSim(self) == ChanSim_(self)

InitChannel(self) == /\ pc[self] = "InitChannel"
                     /\ \/ /\ Assert(S[txChan(self)].in = 0, 
                                     "Failure of assertion at line 23, column 5 of macro called at line 70, column 7.")
                           /\ S' = [S EXCEPT ![txChan(self)].in = message]
                           /\ Timer' = [Timer EXCEPT ![txChan(self)] = 2,
                                                     ![self] = 10]
                           /\ pc' = [pc EXCEPT ![self] = "TransmittingData"]
                        \/ /\ pc' = [pc EXCEPT ![self] = "Idle"]
                           /\ UNCHANGED <<S, Timer>>
                     /\ UNCHANGED << droppedMessageRun, ackDue >>

Idle(self) == /\ pc[self] = "Idle"
              /\ (receive(self) /= 0)
              /\ IF (receive(self) = message)
                    THEN /\ Assert(S[txChan(self)].in = 0, 
                                   "Failure of assertion at line 23, column 5 of macro called at line 79, column 11.")
                         /\ S' = [S EXCEPT ![txChan(self)].in = ack]
                         /\ Timer' = [Timer EXCEPT ![txChan(self)] = 2,
                                                   ![self] = 10]
                         /\ pc' = [pc EXCEPT ![self] = "t1"]
                    ELSE /\ S' = [S EXCEPT ![rxChan(self)].out = 0]
                         /\ pc' = [pc EXCEPT ![self] = "Idle"]
                         /\ Timer' = Timer
              /\ UNCHANGED << droppedMessageRun, ackDue >>

t1(self) == /\ pc[self] = "t1"
            /\ S' = [S EXCEPT ![rxChan(self)].out = 0]
            /\ pc' = [pc EXCEPT ![self] = "TransmittingAckNotAwaiting"]
            /\ UNCHANGED << Timer, droppedMessageRun, ackDue >>

TransmittingAckNotAwaiting(self) == /\ pc[self] = "TransmittingAckNotAwaiting"
                                    /\ (S[txChan(self)].in = 0)
                                    /\ Timer' = [Timer EXCEPT ![self] = -1]
                                    /\ pc' = [pc EXCEPT ![self] = "Idle"]
                                    /\ UNCHANGED << S, droppedMessageRun, 
                                                    ackDue >>

TransmittingData(self) == /\ pc[self] = "TransmittingData"
                          /\ (S[txChan(self)].in = 0 \/ receive(self) /= 0)
                          /\ IF (receive(self) = message) /\ (S[txChan(self)].in = 0)
                                THEN /\ Assert(S[txChan(self)].in = 0, 
                                               "Failure of assertion at line 23, column 5 of macro called at line 96, column 11.")
                                     /\ S' = [S EXCEPT ![txChan(self)].in = ack]
                                     /\ Timer' = [Timer EXCEPT ![txChan(self)] = 2,
                                                               ![self] = 10]
                                     /\ pc' = [pc EXCEPT ![self] = "t2"]
                                     /\ UNCHANGED ackDue
                                ELSE /\ IF (receive(self) = message)
                                           THEN /\ S' = [S EXCEPT ![rxChan(self)].out = 0]
                                                /\ ackDue' = [ackDue EXCEPT ![self] = TRUE]
                                                /\ pc' = [pc EXCEPT ![self] = "TransmittingData"]
                                                /\ Timer' = Timer
                                           ELSE /\ IF (S[txChan(self)].in = 0)
                                                      THEN /\ IF ackDue[self]
                                                                 THEN /\ ackDue' = [ackDue EXCEPT ![self] = FALSE]
                                                                      /\ Assert(S[txChan(self)].in = 0, 
                                                                                "Failure of assertion at line 23, column 5 of macro called at line 106, column 15.")
                                                                      /\ S' = [S EXCEPT ![txChan(self)].in = ack]
                                                                      /\ Timer' = [Timer EXCEPT ![txChan(self)] = 2,
                                                                                                ![self] = 10]
                                                                      /\ pc' = [pc EXCEPT ![self] = "TransmittingAckAwaitingAck"]
                                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "AwaitingAck"]
                                                                      /\ UNCHANGED << S, 
                                                                                      Timer, 
                                                                                      ackDue >>
                                                      ELSE /\ S' = [S EXCEPT ![rxChan(self)].out = 0]
                                                           /\ pc' = [pc EXCEPT ![self] = "TransmittingAckAwaitingAck"]
                                                           /\ UNCHANGED << Timer, 
                                                                           ackDue >>
                          /\ UNCHANGED droppedMessageRun

t2(self) == /\ pc[self] = "t2"
            /\ S' = [S EXCEPT ![rxChan(self)].out = 0]
            /\ pc' = [pc EXCEPT ![self] = "TransmittingAckAwaitingAck"]
            /\ UNCHANGED << Timer, droppedMessageRun, ackDue >>

TransmittingAckAwaitingAck(self) == /\ pc[self] = "TransmittingAckAwaitingAck"
                                    /\ (S[txChan(self)].in = 0 \/ receive(self) = ack)
                                    /\ IF (receive(self) = ack)
                                          THEN /\ S' = [S EXCEPT ![rxChan(self)].out = 0]
                                               /\ pc' = [pc EXCEPT ![self] = "TransmittingAckNotAwaiting"]
                                          ELSE /\ IF (S[txChan(self)].in = 0)
                                                     THEN /\ pc' = [pc EXCEPT ![self] = "AwaitingAck"]
                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "TransmittingAckAwaitingAck"]
                                               /\ S' = S
                                    /\ UNCHANGED << Timer, droppedMessageRun, 
                                                    ackDue >>

AwaitingAck(self) == /\ pc[self] = "AwaitingAck"
                     /\ (receive(self) /= 0)
                     /\ IF (receive(self) = ack)
                           THEN /\ S' = [S EXCEPT ![rxChan(self)].out = 0]
                                /\ pc' = [pc EXCEPT ![self] = "Idle"]
                                /\ Timer' = Timer
                           ELSE /\ IF (receive(self) = message)
                                      THEN /\ Assert(S[txChan(self)].in = 0, 
                                                     "Failure of assertion at line 23, column 5 of macro called at line 134, column 11.")
                                           /\ S' = [S EXCEPT ![txChan(self)].in = ack]
                                           /\ Timer' = [Timer EXCEPT ![txChan(self)] = 2,
                                                                     ![self] = 10]
                                           /\ pc' = [pc EXCEPT ![self] = "t4"]
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "AwaitingAck"]
                                           /\ UNCHANGED << S, Timer >>
                     /\ UNCHANGED << droppedMessageRun, ackDue >>

t4(self) == /\ pc[self] = "t4"
            /\ S' = [S EXCEPT ![rxChan(self)].out = 0]
            /\ pc' = [pc EXCEPT ![self] = "TransmittingAckAwaitingAck"]
            /\ UNCHANGED << Timer, droppedMessageRun, ackDue >>

AckedChannel(self) == InitChannel(self) \/ Idle(self) \/ t1(self)
                         \/ TransmittingAckNotAwaiting(self)
                         \/ TransmittingData(self) \/ t2(self)
                         \/ TransmittingAckAwaitingAck(self)
                         \/ AwaitingAck(self) \/ t4(self)

Next == (\E self \in {"ChanA", "ChanB"}: ChanSim(self))
           \/ (\E self \in { "SendPing", "PingToPong" }: AckedChannel(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {"ChanA", "ChanB"} : WF_vars(ChanSim(self))
        /\ \A self \in { "SendPing", "PingToPong" } : WF_vars(AckedChannel(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

ChannelInvariant == (S.a.in = 0 \/ S.a.out = 0) /\ (S.b.in = 0 \/ S.b.out = 0)

ProgramFinished == pc["SendPing"]="Idle" /\ pc["PingToPong"]="Idle"
\*ProgramFinished == pc["SendPing"]="Done"

=============================================================================
\* Modification History
\* Last modified Thu Feb 06 01:10:02 GMT 2020 by mtandy
\* Created Tue Jan 28 23:30:18 GMT 2020 by mtandy

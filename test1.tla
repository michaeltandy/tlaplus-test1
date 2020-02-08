------------------------------- MODULE test1 -------------------------------

EXTENDS Naturals, TLC, Integers, Sequences, FiniteSets

CONSTANT MaxDroppedMessageRun

(* --algorithm transfer

variables S = [a |-> [in |-> 0, out |-> 0], b |-> [in |-> 0, out |-> 0]],
Timer = [a |-> -1, b |-> -1, ProcX |-> -1, ProcY |-> -1],
Note = "";

define
  fwChan(p) == IF p = "ChanA" THEN "a" ELSE "b"
  txChan(p) == IF p = "ProcX" THEN "a" ELSE "b"
  rxChan(p) == IF p = "ProcX" THEN "b" ELSE "a"
  receive(p) == S[rxChan(p)].out
  
  ack == -1
end define;

macro transmit(toTx, selftimer) begin
    assert S[txChan(self)].in = 0;
    S[txChan(self)].in := toTx;
    if selftimer then
        Timer[txChan(self)] := 1 || Timer[self] := 3;
    else
        Timer[txChan(self)] := 1;
    end if;
end macro;

fair process TimerTick \in {"TimerTick"}
begin TimerTick:
       await (~\E x \in DOMAIN Timer : Timer[x] = 0);
       await (\E x \in DOMAIN Timer : Timer[x] > 0);
       await (~\E x \in {"a", "b"} : S[x].out /= 0); \* Timer stops when a message is delivered.
       Timer["a"] := IF Timer["a"]>0 THEN Timer["a"]-1 ELSE Timer["a"] || Timer["b"] := IF Timer["b"]>0 THEN Timer["b"]-1 ELSE Timer["b"] || Timer["ProcX"] := IF Timer["ProcX"]>0 THEN Timer["ProcX"]-1 ELSE Timer["ProcX"] || Timer["ProcY"] := IF Timer["ProcY"]>0 THEN Timer["ProcY"]-1 ELSE Timer["ProcY"];
       Note := "Time passes";
       goto TimerTick;
end process;

fair process ChanSim \in {"ChanA", "ChanB"}
  variables droppedMessageRun = 0;
begin ChanSim:
      await (S[fwChan(self)].in /= 0 /\ S[fwChan(self)].out = 0);
        if droppedMessageRun < MaxDroppedMessageRun then
          either
            \* Message successfully delivered 
            S[fwChan(self)].out := S[fwChan(self)].in || S[fwChan(self)].in := 0;
            droppedMessageRun := 0;
            Note := self\o" message delivered";
          or
            \* Message lost in transit
            S[fwChan(self)].in := 0;
            droppedMessageRun := droppedMessageRun + 1;
            Note := self\o" message dropped";
          end either;
        else
          \* Message always delivered
          droppedMessageRun := 0; 
          S[fwChan(self)].out := S[fwChan(self)].in || S[fwChan(self)].in := 0;
          Note := self\o" message delivered";
        end if;
        Timer[fwChan(self)] := -1;
   goto ChanSim;
end process;

fair process AckedChannel \in { "ProcX", "ProcY" }
  variables ackDue = FALSE,
  resendCounter = 0,
  currentMessage = 0,
  initialSendQueue \in { <<>>, <<1>>, <<1,2,3>> },
  remainingSendQueue = initialSendQueue;
begin InitChannel:
  Note := self\o" starts.";
  goto Idle;
  
  Idle:
      assert resendCounter = 0;
      if (Len(remainingSendQueue) > 0) then
          currentMessage := Head(remainingSendQueue);
          remainingSendQueue := Tail(remainingSendQueue);
          transmit(currentMessage, TRUE);
          Note := self\o" transmits new message";
          goto TransmittingData;
      else
          assert S[txChan(self)].in = 0;
          await (receive(self) /= 0);
          if (receive(self) \notin {0, ack} ) then
              Note := self\o" starts ack";
              transmit(ack, FALSE);
            t1: S[rxChan(self)].out := 0;
              goto TransmittingAckNotAwaiting
          else
              Note := self\o" ignores unexepected ack";
              S[rxChan(self)].out := 0;
              goto Idle;
          end if;
      end if;
      

  TransmittingAckNotAwaiting:
      await (S[txChan(self)].in = 0);
      Timer[self] := -1;
      Note := self\o" finishes sending ack";
      goto Idle;
  
  FinishingUnnecessaryResend:
      await (S[txChan(self)].in = 0);
      Timer[self] := -1;
      Note := self\o" finishes unnecessary resend";
      goto Idle;
  
  TransmittingData:
      await (S[txChan(self)].in = 0 \/ receive(self) /= 0);
      if (receive(self) \notin {0, ack}) /\ (S[txChan(self)].in = 0) then \* (1) is both-(2)-and-(3)
          transmit(ack, FALSE);
          Note := self\o" starts sending ack";
        t2: S[rxChan(self)].out := 0;
          goto TransmittingAckAwaitingAck;
      elsif (receive(self) \notin {0, ack}) then \* (2) Get something that needs an ack
          S[rxChan(self)].out := 0;
          ackDue := TRUE;
          Note := self\o" receives message, plans ack";
          goto TransmittingData;
      elsif (S[txChan(self)].in = 0) then \* (3) Finishes transmitting
          if ackDue then
              ackDue := FALSE;
              transmit(ack, FALSE);
              Note := self\o" finishes sending data, starts sending ack";
              goto TransmittingAckAwaitingAck;
          else
              Note := self\o" starts awaiting ack";
              goto AwaitingAck;
          end if;
      elsif (receive(self) = ack) then \* Receives ack before tx complete?!?!
          if (resendCounter > 0) then
              Note := self\o" accepts early ack";
              resendCounter := 0;
              goto FinishingUnnecessaryResend;
          else
              S[rxChan(self)].out := 0;
              Note := self\o" ignores unexpected (early) ack";
              goto TransmittingData;
          end if;
      else
          assert(FALSE);
      end if;
      
  
  TransmittingAckAwaitingAck:
      await (S[txChan(self)].in = 0 \/ receive(self) = ack);
      if (receive(self) = ack) then
          S[rxChan(self)].out := 0;
          resendCounter := 0;
          Note := self\o" receives expected ack";
          goto TransmittingAckNotAwaiting;
      elsif (S[txChan(self)].in = 0) then
          Note := self\o" completes transmission of ack";
          goto AwaitingAck;
      else
          assert(FALSE);
      end if;
      
  AwaitingAck:
      assert S[txChan(self)].in = 0;
      await (receive(self) /= 0 \/ Timer[self] = 0);
      if (receive(self) = ack) then
          S[rxChan(self)].out := 0;
          resendCounter := 0;
          Note := self\o" receives expected ack";
          goto Idle;
      elsif (Timer[self] = 0) then
          transmit(currentMessage, TRUE);
          resendCounter := resendCounter+1;
          Note := self\o" resends message after timeout";
          goto TransmittingData;
      elsif (receive(self) \notin {0, ack}) then
          transmit(ack, FALSE);
        t4: S[rxChan(self)].out := 0;
          Note := self\o" receives message, starts sending ack";
          goto TransmittingAckAwaitingAck;
      else
          assert(FALSE);
      end if;
      
end process

end algorithm *)

\* BEGIN TRANSLATION
\* Label TimerTick of process TimerTick at line 34 col 8 changed to TimerTick_
\* Label ChanSim of process ChanSim at line 45 col 7 changed to ChanSim_
VARIABLES S, Timer, Note, pc

(* define statement *)
fwChan(p) == IF p = "ChanA" THEN "a" ELSE "b"
txChan(p) == IF p = "ProcX" THEN "a" ELSE "b"
rxChan(p) == IF p = "ProcX" THEN "b" ELSE "a"
receive(p) == S[rxChan(p)].out

ack == -1

VARIABLES droppedMessageRun, ackDue, resendCounter, currentMessage, 
          initialSendQueue, remainingSendQueue

vars == << S, Timer, Note, pc, droppedMessageRun, ackDue, resendCounter, 
           currentMessage, initialSendQueue, remainingSendQueue >>

ProcSet == ({"TimerTick"}) \cup ({"ChanA", "ChanB"}) \cup ({ "ProcX", "ProcY" })

Init == (* Global variables *)
        /\ S = [a |-> [in |-> 0, out |-> 0], b |-> [in |-> 0, out |-> 0]]
        /\ Timer = [a |-> -1, b |-> -1, ProcX |-> -1, ProcY |-> -1]
        /\ Note = ""
        (* Process ChanSim *)
        /\ droppedMessageRun = [self \in {"ChanA", "ChanB"} |-> 0]
        (* Process AckedChannel *)
        /\ ackDue = [self \in { "ProcX", "ProcY" } |-> FALSE]
        /\ resendCounter = [self \in { "ProcX", "ProcY" } |-> 0]
        /\ currentMessage = [self \in { "ProcX", "ProcY" } |-> 0]
        /\ initialSendQueue \in [{ "ProcX", "ProcY" } -> { <<>>, <<1>>, <<1,2,3>> }]
        /\ remainingSendQueue = [self \in { "ProcX", "ProcY" } |-> initialSendQueue[self]]
        /\ pc = [self \in ProcSet |-> CASE self \in {"TimerTick"} -> "TimerTick_"
                                        [] self \in {"ChanA", "ChanB"} -> "ChanSim_"
                                        [] self \in { "ProcX", "ProcY" } -> "InitChannel"]

TimerTick_(self) == /\ pc[self] = "TimerTick_"
                    /\ (~\E x \in DOMAIN Timer : Timer[x] = 0)
                    /\ (\E x \in DOMAIN Timer : Timer[x] > 0)
                    /\ (~\E x \in {"a", "b"} : S[x].out /= 0)
                    /\ Timer' = [Timer EXCEPT !["a"] = IF Timer["a"]>0 THEN Timer["a"]-1 ELSE Timer["a"],
                                              !["b"] = IF Timer["b"]>0 THEN Timer["b"]-1 ELSE Timer["b"],
                                              !["ProcX"] = IF Timer["ProcX"]>0 THEN Timer["ProcX"]-1 ELSE Timer["ProcX"],
                                              !["ProcY"] = IF Timer["ProcY"]>0 THEN Timer["ProcY"]-1 ELSE Timer["ProcY"]]
                    /\ Note' = "Time passes"
                    /\ pc' = [pc EXCEPT ![self] = "TimerTick_"]
                    /\ UNCHANGED << S, droppedMessageRun, ackDue, 
                                    resendCounter, currentMessage, 
                                    initialSendQueue, remainingSendQueue >>

TimerTick(self) == TimerTick_(self)

ChanSim_(self) == /\ pc[self] = "ChanSim_"
                  /\ (S[fwChan(self)].in /= 0 /\ S[fwChan(self)].out = 0)
                  /\ IF droppedMessageRun[self] < MaxDroppedMessageRun
                        THEN /\ \/ /\ S' = [S EXCEPT ![fwChan(self)].out = S[fwChan(self)].in,
                                                     ![fwChan(self)].in = 0]
                                   /\ droppedMessageRun' = [droppedMessageRun EXCEPT ![self] = 0]
                                   /\ Note' = self\o" message delivered"
                                \/ /\ S' = [S EXCEPT ![fwChan(self)].in = 0]
                                   /\ droppedMessageRun' = [droppedMessageRun EXCEPT ![self] = droppedMessageRun[self] + 1]
                                   /\ Note' = self\o" message dropped"
                        ELSE /\ droppedMessageRun' = [droppedMessageRun EXCEPT ![self] = 0]
                             /\ S' = [S EXCEPT ![fwChan(self)].out = S[fwChan(self)].in,
                                               ![fwChan(self)].in = 0]
                             /\ Note' = self\o" message delivered"
                  /\ Timer' = [Timer EXCEPT ![fwChan(self)] = -1]
                  /\ pc' = [pc EXCEPT ![self] = "ChanSim_"]
                  /\ UNCHANGED << ackDue, resendCounter, currentMessage, 
                                  initialSendQueue, remainingSendQueue >>

ChanSim(self) == ChanSim_(self)

InitChannel(self) == /\ pc[self] = "InitChannel"
                     /\ Note' = self\o" starts."
                     /\ pc' = [pc EXCEPT ![self] = "Idle"]
                     /\ UNCHANGED << S, Timer, droppedMessageRun, ackDue, 
                                     resendCounter, currentMessage, 
                                     initialSendQueue, remainingSendQueue >>

Idle(self) == /\ pc[self] = "Idle"
              /\ Assert(resendCounter[self] = 0, 
                        "Failure of assertion at line 79, column 7.")
              /\ IF (Len(remainingSendQueue[self]) > 0)
                    THEN /\ currentMessage' = [currentMessage EXCEPT ![self] = Head(remainingSendQueue[self])]
                         /\ remainingSendQueue' = [remainingSendQueue EXCEPT ![self] = Tail(remainingSendQueue[self])]
                         /\ Assert(S[txChan(self)].in = 0, 
                                   "Failure of assertion at line 23, column 5 of macro called at line 83, column 11.")
                         /\ S' = [S EXCEPT ![txChan(self)].in = currentMessage'[self]]
                         /\ IF TRUE
                               THEN /\ Timer' = [Timer EXCEPT ![txChan(self)] = 1,
                                                              ![self] = 3]
                               ELSE /\ Timer' = [Timer EXCEPT ![txChan(self)] = 1]
                         /\ Note' = self\o" transmits new message"
                         /\ pc' = [pc EXCEPT ![self] = "TransmittingData"]
                    ELSE /\ Assert(S[txChan(self)].in = 0, 
                                   "Failure of assertion at line 87, column 11.")
                         /\ (receive(self) /= 0)
                         /\ IF (receive(self) \notin {0, ack} )
                               THEN /\ Note' = self\o" starts ack"
                                    /\ Assert(S[txChan(self)].in = 0, 
                                              "Failure of assertion at line 23, column 5 of macro called at line 91, column 15.")
                                    /\ S' = [S EXCEPT ![txChan(self)].in = ack]
                                    /\ IF FALSE
                                          THEN /\ Timer' = [Timer EXCEPT ![txChan(self)] = 1,
                                                                         ![self] = 3]
                                          ELSE /\ Timer' = [Timer EXCEPT ![txChan(self)] = 1]
                                    /\ pc' = [pc EXCEPT ![self] = "t1"]
                               ELSE /\ Note' = self\o" ignores unexepected ack"
                                    /\ S' = [S EXCEPT ![rxChan(self)].out = 0]
                                    /\ pc' = [pc EXCEPT ![self] = "Idle"]
                                    /\ Timer' = Timer
                         /\ UNCHANGED << currentMessage, remainingSendQueue >>
              /\ UNCHANGED << droppedMessageRun, ackDue, resendCounter, 
                              initialSendQueue >>

t1(self) == /\ pc[self] = "t1"
            /\ S' = [S EXCEPT ![rxChan(self)].out = 0]
            /\ pc' = [pc EXCEPT ![self] = "TransmittingAckNotAwaiting"]
            /\ UNCHANGED << Timer, Note, droppedMessageRun, ackDue, 
                            resendCounter, currentMessage, initialSendQueue, 
                            remainingSendQueue >>

TransmittingAckNotAwaiting(self) == /\ pc[self] = "TransmittingAckNotAwaiting"
                                    /\ (S[txChan(self)].in = 0)
                                    /\ Timer' = [Timer EXCEPT ![self] = -1]
                                    /\ Note' = self\o" finishes sending ack"
                                    /\ pc' = [pc EXCEPT ![self] = "Idle"]
                                    /\ UNCHANGED << S, droppedMessageRun, 
                                                    ackDue, resendCounter, 
                                                    currentMessage, 
                                                    initialSendQueue, 
                                                    remainingSendQueue >>

FinishingUnnecessaryResend(self) == /\ pc[self] = "FinishingUnnecessaryResend"
                                    /\ (S[txChan(self)].in = 0)
                                    /\ Timer' = [Timer EXCEPT ![self] = -1]
                                    /\ Note' = self\o" finishes unnecessary resend"
                                    /\ pc' = [pc EXCEPT ![self] = "Idle"]
                                    /\ UNCHANGED << S, droppedMessageRun, 
                                                    ackDue, resendCounter, 
                                                    currentMessage, 
                                                    initialSendQueue, 
                                                    remainingSendQueue >>

TransmittingData(self) == /\ pc[self] = "TransmittingData"
                          /\ (S[txChan(self)].in = 0 \/ receive(self) /= 0)
                          /\ IF (receive(self) \notin {0, ack}) /\ (S[txChan(self)].in = 0)
                                THEN /\ Assert(S[txChan(self)].in = 0, 
                                               "Failure of assertion at line 23, column 5 of macro called at line 117, column 11.")
                                     /\ S' = [S EXCEPT ![txChan(self)].in = ack]
                                     /\ IF FALSE
                                           THEN /\ Timer' = [Timer EXCEPT ![txChan(self)] = 1,
                                                                          ![self] = 3]
                                           ELSE /\ Timer' = [Timer EXCEPT ![txChan(self)] = 1]
                                     /\ Note' = self\o" starts sending ack"
                                     /\ pc' = [pc EXCEPT ![self] = "t2"]
                                     /\ UNCHANGED << ackDue, resendCounter >>
                                ELSE /\ IF (receive(self) \notin {0, ack})
                                           THEN /\ S' = [S EXCEPT ![rxChan(self)].out = 0]
                                                /\ ackDue' = [ackDue EXCEPT ![self] = TRUE]
                                                /\ Note' = self\o" receives message, plans ack"
                                                /\ pc' = [pc EXCEPT ![self] = "TransmittingData"]
                                                /\ UNCHANGED << Timer, 
                                                                resendCounter >>
                                           ELSE /\ IF (S[txChan(self)].in = 0)
                                                      THEN /\ IF ackDue[self]
                                                                 THEN /\ ackDue' = [ackDue EXCEPT ![self] = FALSE]
                                                                      /\ Assert(S[txChan(self)].in = 0, 
                                                                                "Failure of assertion at line 23, column 5 of macro called at line 129, column 15.")
                                                                      /\ S' = [S EXCEPT ![txChan(self)].in = ack]
                                                                      /\ IF FALSE
                                                                            THEN /\ Timer' = [Timer EXCEPT ![txChan(self)] = 1,
                                                                                                           ![self] = 3]
                                                                            ELSE /\ Timer' = [Timer EXCEPT ![txChan(self)] = 1]
                                                                      /\ Note' = self\o" finishes sending data, starts sending ack"
                                                                      /\ pc' = [pc EXCEPT ![self] = "TransmittingAckAwaitingAck"]
                                                                 ELSE /\ Note' = self\o" starts awaiting ack"
                                                                      /\ pc' = [pc EXCEPT ![self] = "AwaitingAck"]
                                                                      /\ UNCHANGED << S, 
                                                                                      Timer, 
                                                                                      ackDue >>
                                                           /\ UNCHANGED resendCounter
                                                      ELSE /\ IF (receive(self) = ack)
                                                                 THEN /\ IF (resendCounter[self] > 0)
                                                                            THEN /\ Note' = self\o" accepts early ack"
                                                                                 /\ resendCounter' = [resendCounter EXCEPT ![self] = 0]
                                                                                 /\ pc' = [pc EXCEPT ![self] = "FinishingUnnecessaryResend"]
                                                                                 /\ S' = S
                                                                            ELSE /\ S' = [S EXCEPT ![rxChan(self)].out = 0]
                                                                                 /\ Note' = self\o" ignores unexpected (early) ack"
                                                                                 /\ pc' = [pc EXCEPT ![self] = "TransmittingData"]
                                                                                 /\ UNCHANGED resendCounter
                                                                 ELSE /\ Assert((FALSE), 
                                                                                "Failure of assertion at line 147, column 11.")
                                                                      /\ pc' = [pc EXCEPT ![self] = "TransmittingAckAwaitingAck"]
                                                                      /\ UNCHANGED << S, 
                                                                                      Note, 
                                                                                      resendCounter >>
                                                           /\ UNCHANGED << Timer, 
                                                                           ackDue >>
                          /\ UNCHANGED << droppedMessageRun, currentMessage, 
                                          initialSendQueue, remainingSendQueue >>

t2(self) == /\ pc[self] = "t2"
            /\ S' = [S EXCEPT ![rxChan(self)].out = 0]
            /\ pc' = [pc EXCEPT ![self] = "TransmittingAckAwaitingAck"]
            /\ UNCHANGED << Timer, Note, droppedMessageRun, ackDue, 
                            resendCounter, currentMessage, initialSendQueue, 
                            remainingSendQueue >>

TransmittingAckAwaitingAck(self) == /\ pc[self] = "TransmittingAckAwaitingAck"
                                    /\ (S[txChan(self)].in = 0 \/ receive(self) = ack)
                                    /\ IF (receive(self) = ack)
                                          THEN /\ S' = [S EXCEPT ![rxChan(self)].out = 0]
                                               /\ resendCounter' = [resendCounter EXCEPT ![self] = 0]
                                               /\ Note' = self\o" receives expected ack"
                                               /\ pc' = [pc EXCEPT ![self] = "TransmittingAckNotAwaiting"]
                                          ELSE /\ IF (S[txChan(self)].in = 0)
                                                     THEN /\ Note' = self\o" completes transmission of ack"
                                                          /\ pc' = [pc EXCEPT ![self] = "AwaitingAck"]
                                                     ELSE /\ Assert((FALSE), 
                                                                    "Failure of assertion at line 162, column 11.")
                                                          /\ pc' = [pc EXCEPT ![self] = "AwaitingAck"]
                                                          /\ Note' = Note
                                               /\ UNCHANGED << S, 
                                                               resendCounter >>
                                    /\ UNCHANGED << Timer, droppedMessageRun, 
                                                    ackDue, currentMessage, 
                                                    initialSendQueue, 
                                                    remainingSendQueue >>

AwaitingAck(self) == /\ pc[self] = "AwaitingAck"
                     /\ Assert(S[txChan(self)].in = 0, 
                               "Failure of assertion at line 166, column 7.")
                     /\ (receive(self) /= 0 \/ Timer[self] = 0)
                     /\ IF (receive(self) = ack)
                           THEN /\ S' = [S EXCEPT ![rxChan(self)].out = 0]
                                /\ resendCounter' = [resendCounter EXCEPT ![self] = 0]
                                /\ Note' = self\o" receives expected ack"
                                /\ pc' = [pc EXCEPT ![self] = "Idle"]
                                /\ Timer' = Timer
                           ELSE /\ IF (Timer[self] = 0)
                                      THEN /\ Assert(S[txChan(self)].in = 0, 
                                                     "Failure of assertion at line 23, column 5 of macro called at line 174, column 11.")
                                           /\ S' = [S EXCEPT ![txChan(self)].in = currentMessage[self]]
                                           /\ IF TRUE
                                                 THEN /\ Timer' = [Timer EXCEPT ![txChan(self)] = 1,
                                                                                ![self] = 3]
                                                 ELSE /\ Timer' = [Timer EXCEPT ![txChan(self)] = 1]
                                           /\ resendCounter' = [resendCounter EXCEPT ![self] = resendCounter[self]+1]
                                           /\ Note' = self\o" resends message after timeout"
                                           /\ pc' = [pc EXCEPT ![self] = "TransmittingData"]
                                      ELSE /\ IF (receive(self) \notin {0, ack})
                                                 THEN /\ Assert(S[txChan(self)].in = 0, 
                                                                "Failure of assertion at line 23, column 5 of macro called at line 179, column 11.")
                                                      /\ S' = [S EXCEPT ![txChan(self)].in = ack]
                                                      /\ IF FALSE
                                                            THEN /\ Timer' = [Timer EXCEPT ![txChan(self)] = 1,
                                                                                           ![self] = 3]
                                                            ELSE /\ Timer' = [Timer EXCEPT ![txChan(self)] = 1]
                                                      /\ pc' = [pc EXCEPT ![self] = "t4"]
                                                 ELSE /\ Assert((FALSE), 
                                                                "Failure of assertion at line 184, column 11.")
                                                      /\ pc' = [pc EXCEPT ![self] = "Done"]
                                                      /\ UNCHANGED << S, Timer >>
                                           /\ UNCHANGED << Note, resendCounter >>
                     /\ UNCHANGED << droppedMessageRun, ackDue, currentMessage, 
                                     initialSendQueue, remainingSendQueue >>

t4(self) == /\ pc[self] = "t4"
            /\ S' = [S EXCEPT ![rxChan(self)].out = 0]
            /\ Note' = self\o" receives message, starts sending ack"
            /\ pc' = [pc EXCEPT ![self] = "TransmittingAckAwaitingAck"]
            /\ UNCHANGED << Timer, droppedMessageRun, ackDue, resendCounter, 
                            currentMessage, initialSendQueue, 
                            remainingSendQueue >>

AckedChannel(self) == InitChannel(self) \/ Idle(self) \/ t1(self)
                         \/ TransmittingAckNotAwaiting(self)
                         \/ FinishingUnnecessaryResend(self)
                         \/ TransmittingData(self) \/ t2(self)
                         \/ TransmittingAckAwaitingAck(self)
                         \/ AwaitingAck(self) \/ t4(self)

Next == (\E self \in {"TimerTick"}: TimerTick(self))
           \/ (\E self \in {"ChanA", "ChanB"}: ChanSim(self))
           \/ (\E self \in { "ProcX", "ProcY" }: AckedChannel(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {"TimerTick"} : WF_vars(TimerTick(self))
        /\ \A self \in {"ChanA", "ChanB"} : WF_vars(ChanSim(self))
        /\ \A self \in { "ProcX", "ProcY" } : WF_vars(AckedChannel(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

ChannelInvariant == (S.a.in = 0 \/ S.a.out = 0) /\ (S.b.in = 0 \/ S.b.out = 0)

ProgramFinished == pc["ProcX"]="Idle" /\ pc["ProcY"]="Idle"
                   /\ Len(remainingSendQueue["ProcX"]) = 0 /\ Len(remainingSendQueue["ProcY"]) = 0
\*ProgramFinished == pc["SendPing"]="Done"

=============================================================================
\* Modification History
\* Last modified Sat Feb 08 17:56:31 GMT 2020 by mtandy
\* Created Tue Jan 28 23:30:18 GMT 2020 by mtandy

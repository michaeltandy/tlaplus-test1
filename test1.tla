------------------------------- MODULE test1 -------------------------------

EXTENDS Naturals, TLC, Integers, Sequences, FiniteSets

CONSTANT droppedMessageLimit

(* --algorithm transfer

variables S = [a |-> [in |-> 0, out |-> 0], b |-> [in |-> 0, out |-> 0]],
Timer = [a |-> -1, b |-> -1, ProcX |-> -1, ProcY |-> -1],
Note = "",
droppedMessagesRemaining = droppedMessageLimit;

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
begin ChanSim:
      await (S[fwChan(self)].in /= 0 /\ S[fwChan(self)].out = 0);
        if droppedMessagesRemaining > 0 then
          either
            \* Message successfully delivered 
            S[fwChan(self)].out := S[fwChan(self)].in || S[fwChan(self)].in := 0;
            Note := self\o" message delivered";
          or
            \* Message lost in transit
            droppedMessagesRemaining := droppedMessagesRemaining-1;
            S[fwChan(self)].in := 0;
            Note := self\o" message dropped";
          end either;
        else
          \* Message always delivered
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
  lastRx = 0,
  initialSendQueue \in { <<>>, <<1>>, <<1,2>> },
  remainingSendQueue = initialSendQueue,
  rxHistory = <<>>;
begin InitChannel:
  Note := self\o" starts.";
  goto Idle;
  
  Idle:
      assert resendCounter = 0;
      assert Timer[self] = -1;
      if (Len(remainingSendQueue) > 0) then
          currentMessage := Head(remainingSendQueue);
          remainingSendQueue := Tail(remainingSendQueue);
          transmit(currentMessage, TRUE);
          Note := self\o" transmits new message";
          goto TransmittingData;
      else
          assert S[txChan(self)].in = 0;
          await (receive(self) /= 0);
          if (receive(self) > 0) then
              if (lastRx /= receive(self)) then
                  rxHistory := Append(rxHistory, receive(self));
                  lastRx := receive(self);
                  Note := self\o" acks new message";
              else
                  Note := self\o" acks duplicate message";
              end if;
              transmit(-lastRx, FALSE);
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
      if (receive(self) > 0) /\ (S[txChan(self)].in = 0) then \* (1) is both-(2)-and-(3)
          if (lastRx /= receive(self)) then
              rxHistory := Append(rxHistory, receive(self));
              lastRx := receive(self);
              Note := self\o" starts acking new message, then will await ack";
          else
              Note := self\o" starts acking duplicate message, then will await ack";
          end if;
          transmit(-lastRx, FALSE);
        t2: S[rxChan(self)].out := 0;
          goto TransmittingAckAwaitingAck;
      elsif (receive(self) > 0) then \* (2) Get something that needs an ack
          if (lastRx /= receive(self)) then
              rxHistory := Append(rxHistory, receive(self));
              lastRx := receive(self);
              Note := self\o" plans ack for new message";
          else
              Note := self\o" plans ack for duplicate message";
          end if;
          S[rxChan(self)].out := 0;
          ackDue := TRUE;
          goto TransmittingData;
      elsif (S[txChan(self)].in = 0) then \* (3) Finishes transmitting
          if ackDue then
              ackDue := FALSE;
              transmit(-lastRx, FALSE);
              Note := self\o" finishes sending data, starts sending ack";
              goto TransmittingAckAwaitingAck;
          else
              Note := self\o" starts awaiting ack";
              goto AwaitingAck;
          end if;
      elsif (receive(self) < 0) then \* Receives ack before tx complete?!?!
          if (resendCounter > 0 /\ receive(self) = -currentMessage) then
              Note := self\o" accepts early ack, as this is a resend.";
              resendCounter := 0;
              Timer[self] := -1;
              goto FinishingUnnecessaryResend;
          elsif (receive(self) = -currentMessage) then
              assert(FALSE);
          else
              S[rxChan(self)].out := 0;
              Note := self\o" ignores ack from previous message";
              goto TransmittingData;
          end if;
      else
          assert(FALSE);
      end if;
      
  
  TransmittingAckAwaitingAck:
      await (S[txChan(self)].in = 0 \/ receive(self) < 0);
      if (receive(self) < 0) then
          if (receive(self) = -currentMessage) then
              S[rxChan(self)].out := 0;
              resendCounter := 0;
              Timer[self] := -1;
              Note := self\o" receives expected ack";
              goto TransmittingAckNotAwaiting;
          else
              S[rxChan(self)].out := 0;
              Note := self\o" ignores other-message ack";
              goto TransmittingAckAwaitingAck;
          end if;
      elsif (S[txChan(self)].in = 0) then
          Note := self\o" completes transmission of ack";
          goto AwaitingAck;
      else
          assert(FALSE);
      end if;
      
  AwaitingAck:
      assert S[txChan(self)].in = 0;
      await (receive(self) /= 0 \/ Timer[self] = 0);
      if (receive(self) < 0) then
          if (receive(self) = -currentMessage) then
            S[rxChan(self)].out := 0;
            resendCounter := 0;
            Timer[self] := -1;
            Note := self\o" receives expected ack";
            goto Idle;
          else
            S[rxChan(self)].out := 0;
            Note := self\o" ignores other-message ack";
            goto AwaitingAck;
          end if
      elsif (Timer[self] = 0) then
          transmit(currentMessage, TRUE);
          resendCounter := resendCounter+1;
          Note := self\o" resends message after timeout";
          goto TransmittingData;
      elsif (receive(self) > 0) then
          if (lastRx /= receive(self)) then
              rxHistory := Append(rxHistory, receive(self));
              lastRx := receive(self);
              Note := self\o" receives message, starts sending ack";
          else
              Note := self\o" receives duplicate message, starts sending ack";
          end if;
        t4: S[rxChan(self)].out := 0;
          goto TransmittingAckAwaitingAck;
      else
          assert(FALSE);
      end if;
      
end process

end algorithm *)

\* BEGIN TRANSLATION
\* Label TimerTick of process TimerTick at line 35 col 8 changed to TimerTick_
\* Label ChanSim of process ChanSim at line 45 col 7 changed to ChanSim_
VARIABLES S, Timer, Note, droppedMessagesRemaining, pc

(* define statement *)
fwChan(p) == IF p = "ChanA" THEN "a" ELSE "b"
txChan(p) == IF p = "ProcX" THEN "a" ELSE "b"
rxChan(p) == IF p = "ProcX" THEN "b" ELSE "a"
receive(p) == S[rxChan(p)].out

ack == -1

VARIABLES ackDue, resendCounter, currentMessage, lastRx, initialSendQueue, 
          remainingSendQueue, rxHistory

vars == << S, Timer, Note, droppedMessagesRemaining, pc, ackDue, 
           resendCounter, currentMessage, lastRx, initialSendQueue, 
           remainingSendQueue, rxHistory >>

ProcSet == ({"TimerTick"}) \cup ({"ChanA", "ChanB"}) \cup ({ "ProcX", "ProcY" })

Init == (* Global variables *)
        /\ S = [a |-> [in |-> 0, out |-> 0], b |-> [in |-> 0, out |-> 0]]
        /\ Timer = [a |-> -1, b |-> -1, ProcX |-> -1, ProcY |-> -1]
        /\ Note = ""
        /\ droppedMessagesRemaining = droppedMessageLimit
        (* Process AckedChannel *)
        /\ ackDue = [self \in { "ProcX", "ProcY" } |-> FALSE]
        /\ resendCounter = [self \in { "ProcX", "ProcY" } |-> 0]
        /\ currentMessage = [self \in { "ProcX", "ProcY" } |-> 0]
        /\ lastRx = [self \in { "ProcX", "ProcY" } |-> 0]
        /\ initialSendQueue \in [{ "ProcX", "ProcY" } -> { <<>>, <<1>>, <<1,2>> }]
        /\ remainingSendQueue = [self \in { "ProcX", "ProcY" } |-> initialSendQueue[self]]
        /\ rxHistory = [self \in { "ProcX", "ProcY" } |-> <<>>]
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
                    /\ UNCHANGED << S, droppedMessagesRemaining, ackDue, 
                                    resendCounter, currentMessage, lastRx, 
                                    initialSendQueue, remainingSendQueue, 
                                    rxHistory >>

TimerTick(self) == TimerTick_(self)

ChanSim_(self) == /\ pc[self] = "ChanSim_"
                  /\ (S[fwChan(self)].in /= 0 /\ S[fwChan(self)].out = 0)
                  /\ IF droppedMessagesRemaining > 0
                        THEN /\ \/ /\ S' = [S EXCEPT ![fwChan(self)].out = S[fwChan(self)].in,
                                                     ![fwChan(self)].in = 0]
                                   /\ Note' = self\o" message delivered"
                                   /\ UNCHANGED droppedMessagesRemaining
                                \/ /\ droppedMessagesRemaining' = droppedMessagesRemaining-1
                                   /\ S' = [S EXCEPT ![fwChan(self)].in = 0]
                                   /\ Note' = self\o" message dropped"
                        ELSE /\ S' = [S EXCEPT ![fwChan(self)].out = S[fwChan(self)].in,
                                               ![fwChan(self)].in = 0]
                             /\ Note' = self\o" message delivered"
                             /\ UNCHANGED droppedMessagesRemaining
                  /\ Timer' = [Timer EXCEPT ![fwChan(self)] = -1]
                  /\ pc' = [pc EXCEPT ![self] = "ChanSim_"]
                  /\ UNCHANGED << ackDue, resendCounter, currentMessage, 
                                  lastRx, initialSendQueue, remainingSendQueue, 
                                  rxHistory >>

ChanSim(self) == ChanSim_(self)

InitChannel(self) == /\ pc[self] = "InitChannel"
                     /\ Note' = self\o" starts."
                     /\ pc' = [pc EXCEPT ![self] = "Idle"]
                     /\ UNCHANGED << S, Timer, droppedMessagesRemaining, 
                                     ackDue, resendCounter, currentMessage, 
                                     lastRx, initialSendQueue, 
                                     remainingSendQueue, rxHistory >>

Idle(self) == /\ pc[self] = "Idle"
              /\ Assert(resendCounter[self] = 0, 
                        "Failure of assertion at line 79, column 7.")
              /\ Assert(Timer[self] = -1, 
                        "Failure of assertion at line 80, column 7.")
              /\ IF (Len(remainingSendQueue[self]) > 0)
                    THEN /\ currentMessage' = [currentMessage EXCEPT ![self] = Head(remainingSendQueue[self])]
                         /\ remainingSendQueue' = [remainingSendQueue EXCEPT ![self] = Tail(remainingSendQueue[self])]
                         /\ Assert(S[txChan(self)].in = 0, 
                                   "Failure of assertion at line 24, column 5 of macro called at line 84, column 11.")
                         /\ S' = [S EXCEPT ![txChan(self)].in = currentMessage'[self]]
                         /\ IF TRUE
                               THEN /\ Timer' = [Timer EXCEPT ![txChan(self)] = 1,
                                                              ![self] = 3]
                               ELSE /\ Timer' = [Timer EXCEPT ![txChan(self)] = 1]
                         /\ Note' = self\o" transmits new message"
                         /\ pc' = [pc EXCEPT ![self] = "TransmittingData"]
                         /\ UNCHANGED << lastRx, rxHistory >>
                    ELSE /\ Assert(S[txChan(self)].in = 0, 
                                   "Failure of assertion at line 88, column 11.")
                         /\ (receive(self) /= 0)
                         /\ IF (receive(self) > 0)
                               THEN /\ IF (lastRx[self] /= receive(self))
                                          THEN /\ rxHistory' = [rxHistory EXCEPT ![self] = Append(rxHistory[self], receive(self))]
                                               /\ lastRx' = [lastRx EXCEPT ![self] = receive(self)]
                                               /\ Note' = self\o" acks new message"
                                          ELSE /\ Note' = self\o" acks duplicate message"
                                               /\ UNCHANGED << lastRx, 
                                                               rxHistory >>
                                    /\ Assert(S[txChan(self)].in = 0, 
                                              "Failure of assertion at line 24, column 5 of macro called at line 98, column 15.")
                                    /\ S' = [S EXCEPT ![txChan(self)].in = -lastRx'[self]]
                                    /\ IF FALSE
                                          THEN /\ Timer' = [Timer EXCEPT ![txChan(self)] = 1,
                                                                         ![self] = 3]
                                          ELSE /\ Timer' = [Timer EXCEPT ![txChan(self)] = 1]
                                    /\ pc' = [pc EXCEPT ![self] = "t1"]
                               ELSE /\ Note' = self\o" ignores unexepected ack"
                                    /\ S' = [S EXCEPT ![rxChan(self)].out = 0]
                                    /\ pc' = [pc EXCEPT ![self] = "Idle"]
                                    /\ UNCHANGED << Timer, lastRx, rxHistory >>
                         /\ UNCHANGED << currentMessage, remainingSendQueue >>
              /\ UNCHANGED << droppedMessagesRemaining, ackDue, resendCounter, 
                              initialSendQueue >>

t1(self) == /\ pc[self] = "t1"
            /\ S' = [S EXCEPT ![rxChan(self)].out = 0]
            /\ pc' = [pc EXCEPT ![self] = "TransmittingAckNotAwaiting"]
            /\ UNCHANGED << Timer, Note, droppedMessagesRemaining, ackDue, 
                            resendCounter, currentMessage, lastRx, 
                            initialSendQueue, remainingSendQueue, rxHistory >>

TransmittingAckNotAwaiting(self) == /\ pc[self] = "TransmittingAckNotAwaiting"
                                    /\ (S[txChan(self)].in = 0)
                                    /\ Timer' = [Timer EXCEPT ![self] = -1]
                                    /\ Note' = self\o" finishes sending ack"
                                    /\ pc' = [pc EXCEPT ![self] = "Idle"]
                                    /\ UNCHANGED << S, 
                                                    droppedMessagesRemaining, 
                                                    ackDue, resendCounter, 
                                                    currentMessage, lastRx, 
                                                    initialSendQueue, 
                                                    remainingSendQueue, 
                                                    rxHistory >>

FinishingUnnecessaryResend(self) == /\ pc[self] = "FinishingUnnecessaryResend"
                                    /\ (S[txChan(self)].in = 0)
                                    /\ Timer' = [Timer EXCEPT ![self] = -1]
                                    /\ Note' = self\o" finishes unnecessary resend"
                                    /\ pc' = [pc EXCEPT ![self] = "Idle"]
                                    /\ UNCHANGED << S, 
                                                    droppedMessagesRemaining, 
                                                    ackDue, resendCounter, 
                                                    currentMessage, lastRx, 
                                                    initialSendQueue, 
                                                    remainingSendQueue, 
                                                    rxHistory >>

TransmittingData(self) == /\ pc[self] = "TransmittingData"
                          /\ (S[txChan(self)].in = 0 \/ receive(self) /= 0)
                          /\ IF (receive(self) > 0) /\ (S[txChan(self)].in = 0)
                                THEN /\ IF (lastRx[self] /= receive(self))
                                           THEN /\ rxHistory' = [rxHistory EXCEPT ![self] = Append(rxHistory[self], receive(self))]
                                                /\ lastRx' = [lastRx EXCEPT ![self] = receive(self)]
                                                /\ Note' = self\o" starts acking new message, then will await ack"
                                           ELSE /\ Note' = self\o" starts acking duplicate message, then will await ack"
                                                /\ UNCHANGED << lastRx, 
                                                                rxHistory >>
                                     /\ Assert(S[txChan(self)].in = 0, 
                                               "Failure of assertion at line 24, column 5 of macro called at line 131, column 11.")
                                     /\ S' = [S EXCEPT ![txChan(self)].in = -lastRx'[self]]
                                     /\ IF FALSE
                                           THEN /\ Timer' = [Timer EXCEPT ![txChan(self)] = 1,
                                                                          ![self] = 3]
                                           ELSE /\ Timer' = [Timer EXCEPT ![txChan(self)] = 1]
                                     /\ pc' = [pc EXCEPT ![self] = "t2"]
                                     /\ UNCHANGED << ackDue, resendCounter >>
                                ELSE /\ IF (receive(self) > 0)
                                           THEN /\ IF (lastRx[self] /= receive(self))
                                                      THEN /\ rxHistory' = [rxHistory EXCEPT ![self] = Append(rxHistory[self], receive(self))]
                                                           /\ lastRx' = [lastRx EXCEPT ![self] = receive(self)]
                                                           /\ Note' = self\o" plans ack for new message"
                                                      ELSE /\ Note' = self\o" plans ack for duplicate message"
                                                           /\ UNCHANGED << lastRx, 
                                                                           rxHistory >>
                                                /\ S' = [S EXCEPT ![rxChan(self)].out = 0]
                                                /\ ackDue' = [ackDue EXCEPT ![self] = TRUE]
                                                /\ pc' = [pc EXCEPT ![self] = "TransmittingData"]
                                                /\ UNCHANGED << Timer, 
                                                                resendCounter >>
                                           ELSE /\ IF (S[txChan(self)].in = 0)
                                                      THEN /\ IF ackDue[self]
                                                                 THEN /\ ackDue' = [ackDue EXCEPT ![self] = FALSE]
                                                                      /\ Assert(S[txChan(self)].in = 0, 
                                                                                "Failure of assertion at line 24, column 5 of macro called at line 148, column 15.")
                                                                      /\ S' = [S EXCEPT ![txChan(self)].in = -lastRx[self]]
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
                                                      ELSE /\ IF (receive(self) < 0)
                                                                 THEN /\ IF (resendCounter[self] > 0 /\ receive(self) = -currentMessage[self])
                                                                            THEN /\ Note' = self\o" accepts early ack, as this is a resend."
                                                                                 /\ resendCounter' = [resendCounter EXCEPT ![self] = 0]
                                                                                 /\ Timer' = [Timer EXCEPT ![self] = -1]
                                                                                 /\ pc' = [pc EXCEPT ![self] = "FinishingUnnecessaryResend"]
                                                                                 /\ S' = S
                                                                            ELSE /\ IF (receive(self) = -currentMessage[self])
                                                                                       THEN /\ Assert((FALSE), 
                                                                                                      "Failure of assertion at line 162, column 15.")
                                                                                            /\ pc' = [pc EXCEPT ![self] = "TransmittingAckAwaitingAck"]
                                                                                            /\ UNCHANGED << S, 
                                                                                                            Note >>
                                                                                       ELSE /\ S' = [S EXCEPT ![rxChan(self)].out = 0]
                                                                                            /\ Note' = self\o" ignores ack from previous message"
                                                                                            /\ pc' = [pc EXCEPT ![self] = "TransmittingData"]
                                                                                 /\ UNCHANGED << Timer, 
                                                                                                 resendCounter >>
                                                                 ELSE /\ Assert((FALSE), 
                                                                                "Failure of assertion at line 169, column 11.")
                                                                      /\ pc' = [pc EXCEPT ![self] = "TransmittingAckAwaitingAck"]
                                                                      /\ UNCHANGED << S, 
                                                                                      Timer, 
                                                                                      Note, 
                                                                                      resendCounter >>
                                                           /\ UNCHANGED ackDue
                                                /\ UNCHANGED << lastRx, 
                                                                rxHistory >>
                          /\ UNCHANGED << droppedMessagesRemaining, 
                                          currentMessage, initialSendQueue, 
                                          remainingSendQueue >>

t2(self) == /\ pc[self] = "t2"
            /\ S' = [S EXCEPT ![rxChan(self)].out = 0]
            /\ pc' = [pc EXCEPT ![self] = "TransmittingAckAwaitingAck"]
            /\ UNCHANGED << Timer, Note, droppedMessagesRemaining, ackDue, 
                            resendCounter, currentMessage, lastRx, 
                            initialSendQueue, remainingSendQueue, rxHistory >>

TransmittingAckAwaitingAck(self) == /\ pc[self] = "TransmittingAckAwaitingAck"
                                    /\ (S[txChan(self)].in = 0 \/ receive(self) < 0)
                                    /\ IF (receive(self) < 0)
                                          THEN /\ IF (receive(self) = -currentMessage[self])
                                                     THEN /\ S' = [S EXCEPT ![rxChan(self)].out = 0]
                                                          /\ resendCounter' = [resendCounter EXCEPT ![self] = 0]
                                                          /\ Timer' = [Timer EXCEPT ![self] = -1]
                                                          /\ Note' = self\o" receives expected ack"
                                                          /\ pc' = [pc EXCEPT ![self] = "TransmittingAckNotAwaiting"]
                                                     ELSE /\ S' = [S EXCEPT ![rxChan(self)].out = 0]
                                                          /\ Note' = self\o" ignores other-message ack"
                                                          /\ pc' = [pc EXCEPT ![self] = "TransmittingAckAwaitingAck"]
                                                          /\ UNCHANGED << Timer, 
                                                                          resendCounter >>
                                          ELSE /\ IF (S[txChan(self)].in = 0)
                                                     THEN /\ Note' = self\o" completes transmission of ack"
                                                          /\ pc' = [pc EXCEPT ![self] = "AwaitingAck"]
                                                     ELSE /\ Assert((FALSE), 
                                                                    "Failure of assertion at line 191, column 11.")
                                                          /\ pc' = [pc EXCEPT ![self] = "AwaitingAck"]
                                                          /\ Note' = Note
                                               /\ UNCHANGED << S, Timer, 
                                                               resendCounter >>
                                    /\ UNCHANGED << droppedMessagesRemaining, 
                                                    ackDue, currentMessage, 
                                                    lastRx, initialSendQueue, 
                                                    remainingSendQueue, 
                                                    rxHistory >>

AwaitingAck(self) == /\ pc[self] = "AwaitingAck"
                     /\ Assert(S[txChan(self)].in = 0, 
                               "Failure of assertion at line 195, column 7.")
                     /\ (receive(self) /= 0 \/ Timer[self] = 0)
                     /\ IF (receive(self) < 0)
                           THEN /\ IF (receive(self) = -currentMessage[self])
                                      THEN /\ S' = [S EXCEPT ![rxChan(self)].out = 0]
                                           /\ resendCounter' = [resendCounter EXCEPT ![self] = 0]
                                           /\ Timer' = [Timer EXCEPT ![self] = -1]
                                           /\ Note' = self\o" receives expected ack"
                                           /\ pc' = [pc EXCEPT ![self] = "Idle"]
                                      ELSE /\ S' = [S EXCEPT ![rxChan(self)].out = 0]
                                           /\ Note' = self\o" ignores other-message ack"
                                           /\ pc' = [pc EXCEPT ![self] = "AwaitingAck"]
                                           /\ UNCHANGED << Timer, 
                                                           resendCounter >>
                                /\ UNCHANGED << lastRx, rxHistory >>
                           ELSE /\ IF (Timer[self] = 0)
                                      THEN /\ Assert(S[txChan(self)].in = 0, 
                                                     "Failure of assertion at line 24, column 5 of macro called at line 210, column 11.")
                                           /\ S' = [S EXCEPT ![txChan(self)].in = currentMessage[self]]
                                           /\ IF TRUE
                                                 THEN /\ Timer' = [Timer EXCEPT ![txChan(self)] = 1,
                                                                                ![self] = 3]
                                                 ELSE /\ Timer' = [Timer EXCEPT ![txChan(self)] = 1]
                                           /\ resendCounter' = [resendCounter EXCEPT ![self] = resendCounter[self]+1]
                                           /\ Note' = self\o" resends message after timeout"
                                           /\ pc' = [pc EXCEPT ![self] = "TransmittingData"]
                                           /\ UNCHANGED << lastRx, rxHistory >>
                                      ELSE /\ IF (receive(self) > 0)
                                                 THEN /\ IF (lastRx[self] /= receive(self))
                                                            THEN /\ rxHistory' = [rxHistory EXCEPT ![self] = Append(rxHistory[self], receive(self))]
                                                                 /\ lastRx' = [lastRx EXCEPT ![self] = receive(self)]
                                                                 /\ Note' = self\o" receives message, starts sending ack"
                                                            ELSE /\ Note' = self\o" receives duplicate message, starts sending ack"
                                                                 /\ UNCHANGED << lastRx, 
                                                                                 rxHistory >>
                                                      /\ pc' = [pc EXCEPT ![self] = "t4"]
                                                 ELSE /\ Assert((FALSE), 
                                                                "Failure of assertion at line 225, column 11.")
                                                      /\ pc' = [pc EXCEPT ![self] = "Done"]
                                                      /\ UNCHANGED << Note, 
                                                                      lastRx, 
                                                                      rxHistory >>
                                           /\ UNCHANGED << S, Timer, 
                                                           resendCounter >>
                     /\ UNCHANGED << droppedMessagesRemaining, ackDue, 
                                     currentMessage, initialSendQueue, 
                                     remainingSendQueue >>

t4(self) == /\ pc[self] = "t4"
            /\ S' = [S EXCEPT ![rxChan(self)].out = 0]
            /\ pc' = [pc EXCEPT ![self] = "TransmittingAckAwaitingAck"]
            /\ UNCHANGED << Timer, Note, droppedMessagesRemaining, ackDue, 
                            resendCounter, currentMessage, lastRx, 
                            initialSendQueue, remainingSendQueue, rxHistory >>

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

\*ChannelInvariant == (S.a.in = 0 \/ S.a.out = 0) /\ (S.b.in = 0 \/ S.b.out = 0)

NeverRxMoreThanTxInvariant == Len(rxHistory["ProcX"]) <= Len(initialSendQueue["ProcY"])
                     /\ Len(rxHistory["ProcY"]) <= Len(initialSendQueue["ProcX"])

ProgramFinished == pc["ProcX"]="Idle" /\ pc["ProcY"]="Idle"
                   /\ Len(remainingSendQueue["ProcX"]) = 0 /\ Len(remainingSendQueue["ProcY"]) = 0
                   /\ Len(rxHistory["ProcX"]) = Len(initialSendQueue["ProcY"])
                   /\ Len(rxHistory["ProcY"]) = Len(initialSendQueue["ProcX"])
\*ProgramFinished == pc["SendPing"]="Done"

=============================================================================
\* Modification History
\* Last modified Sun Feb 09 13:09:57 GMT 2020 by mtandy
\* Created Tue Jan 28 23:30:18 GMT 2020 by mtandy

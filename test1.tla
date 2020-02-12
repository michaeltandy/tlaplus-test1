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

macro transmit(toTx, selftimer, clearRx) begin
    assert S[txChan(self)].in = 0;
    if clearRx then
        S[txChan(self)].in := toTx || S[rxChan(self)].out := 0
    else
        S[txChan(self)].in := toTx;
    end if;
    if selftimer then
        Timer[txChan(self)] := 0 || Timer[self] := 1;
    else
        Timer[txChan(self)] := 0;
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
  unackedMessageCount = 0,
  initialSendQueue \in { <<>>, <<1>>, <<1,2>> },
  \*initialSendQueue = (IF self = "ProcX" THEN <<1>> ELSE <<1,2>>), 
  \*initialSendQueue = <<1,2>>,
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
          transmit(currentMessage, TRUE, FALSE);
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
              transmit(-lastRx, FALSE, TRUE);
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
          transmit(-lastRx, FALSE, TRUE);
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
              transmit(-lastRx, FALSE, FALSE);
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
      \*assert S[txChan(self)].in < 0;
      await (S[txChan(self)].in = 0 \/ receive(self) < 0);
      if (receive(self) < 0) then
          if (receive(self) = -currentMessage) then
              S[rxChan(self)].out := 0;
              resendCounter := 0;
              Timer[self] := -1;
              if (S[txChan(self)].in /= 0) then
                  Note := self\o" receives expected ack";
                  goto TransmittingAckNotAwaiting;
              else
                  Note := self\o" receives expected ack and completes transmission.";
                  goto Idle;
              end if;
          else
              S[rxChan(self)].out := 0;
              if (S[txChan(self)].in /= 0) then
                  Note := self\o" ignores other-message ack";
                  goto TransmittingAckAwaitingAck;
              else
                  Note := self\o" ignores other-message ack, and completes transmission.";
                  goto AwaitingAck;
              end if;
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
          if (resendCounter < 3) then
              transmit(currentMessage, TRUE, FALSE);
              resendCounter := resendCounter+1;
              Note := self\o" resends message after timeout";
              goto TransmittingData;
          else
              unackedMessageCount := unackedMessageCount+1;
              Note := self\o" dropped message after several retries.";
              resendCounter := 0;
              Timer[self] := -1;
              goto Idle;
          end if;
      elsif (receive(self) > 0) then
          if (lastRx /= receive(self)) then
              rxHistory := Append(rxHistory, receive(self));
              lastRx := receive(self);
              Note := self\o" receives message, starts sending ack";
          else
              Note := self\o" receives duplicate message, starts sending ack";
          end if;
          transmit(-lastRx, FALSE, TRUE);
          goto TransmittingAckAwaitingAck;
      else
          assert(FALSE);
      end if;
      
end process

end algorithm *)

\* BEGIN TRANSLATION
\* Label TimerTick of process TimerTick at line 39 col 8 changed to TimerTick_
\* Label ChanSim of process ChanSim at line 49 col 7 changed to ChanSim_
VARIABLES S, Timer, Note, droppedMessagesRemaining, pc

(* define statement *)
fwChan(p) == IF p = "ChanA" THEN "a" ELSE "b"
txChan(p) == IF p = "ProcX" THEN "a" ELSE "b"
rxChan(p) == IF p = "ProcX" THEN "b" ELSE "a"
receive(p) == S[rxChan(p)].out

ack == -1

VARIABLES ackDue, resendCounter, currentMessage, lastRx, unackedMessageCount, 
          initialSendQueue, remainingSendQueue, rxHistory

vars == << S, Timer, Note, droppedMessagesRemaining, pc, ackDue, 
           resendCounter, currentMessage, lastRx, unackedMessageCount, 
           initialSendQueue, remainingSendQueue, rxHistory >>

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
        /\ unackedMessageCount = [self \in { "ProcX", "ProcY" } |-> 0]
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
                                    unackedMessageCount, initialSendQueue, 
                                    remainingSendQueue, rxHistory >>

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
                                  lastRx, unackedMessageCount, 
                                  initialSendQueue, remainingSendQueue, 
                                  rxHistory >>

ChanSim(self) == ChanSim_(self)

InitChannel(self) == /\ pc[self] = "InitChannel"
                     /\ Note' = self\o" starts."
                     /\ pc' = [pc EXCEPT ![self] = "Idle"]
                     /\ UNCHANGED << S, Timer, droppedMessagesRemaining, 
                                     ackDue, resendCounter, currentMessage, 
                                     lastRx, unackedMessageCount, 
                                     initialSendQueue, remainingSendQueue, 
                                     rxHistory >>

Idle(self) == /\ pc[self] = "Idle"
              /\ Assert(resendCounter[self] = 0, 
                        "Failure of assertion at line 86, column 7.")
              /\ Assert(Timer[self] = -1, 
                        "Failure of assertion at line 87, column 7.")
              /\ IF (Len(remainingSendQueue[self]) > 0)
                    THEN /\ currentMessage' = [currentMessage EXCEPT ![self] = Head(remainingSendQueue[self])]
                         /\ remainingSendQueue' = [remainingSendQueue EXCEPT ![self] = Tail(remainingSendQueue[self])]
                         /\ Assert(S[txChan(self)].in = 0, 
                                   "Failure of assertion at line 24, column 5 of macro called at line 91, column 11.")
                         /\ IF FALSE
                               THEN /\ S' = [S EXCEPT ![txChan(self)].in = currentMessage'[self],
                                                      ![rxChan(self)].out = 0]
                               ELSE /\ S' = [S EXCEPT ![txChan(self)].in = currentMessage'[self]]
                         /\ IF TRUE
                               THEN /\ Timer' = [Timer EXCEPT ![txChan(self)] = 0,
                                                              ![self] = 1]
                               ELSE /\ Timer' = [Timer EXCEPT ![txChan(self)] = 0]
                         /\ Note' = self\o" transmits new message"
                         /\ pc' = [pc EXCEPT ![self] = "TransmittingData"]
                         /\ UNCHANGED << lastRx, rxHistory >>
                    ELSE /\ Assert(S[txChan(self)].in = 0, 
                                   "Failure of assertion at line 95, column 11.")
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
                                              "Failure of assertion at line 24, column 5 of macro called at line 105, column 15.")
                                    /\ IF TRUE
                                          THEN /\ S' = [S EXCEPT ![txChan(self)].in = -lastRx'[self],
                                                                 ![rxChan(self)].out = 0]
                                          ELSE /\ S' = [S EXCEPT ![txChan(self)].in = -lastRx'[self]]
                                    /\ IF FALSE
                                          THEN /\ Timer' = [Timer EXCEPT ![txChan(self)] = 0,
                                                                         ![self] = 1]
                                          ELSE /\ Timer' = [Timer EXCEPT ![txChan(self)] = 0]
                                    /\ pc' = [pc EXCEPT ![self] = "TransmittingAckNotAwaiting"]
                               ELSE /\ Note' = self\o" ignores unexepected ack"
                                    /\ S' = [S EXCEPT ![rxChan(self)].out = 0]
                                    /\ pc' = [pc EXCEPT ![self] = "Idle"]
                                    /\ UNCHANGED << Timer, lastRx, rxHistory >>
                         /\ UNCHANGED << currentMessage, remainingSendQueue >>
              /\ UNCHANGED << droppedMessagesRemaining, ackDue, resendCounter, 
                              unackedMessageCount, initialSendQueue >>

TransmittingAckNotAwaiting(self) == /\ pc[self] = "TransmittingAckNotAwaiting"
                                    /\ (S[txChan(self)].in = 0)
                                    /\ Timer' = [Timer EXCEPT ![self] = -1]
                                    /\ Note' = self\o" finishes sending ack"
                                    /\ pc' = [pc EXCEPT ![self] = "Idle"]
                                    /\ UNCHANGED << S, 
                                                    droppedMessagesRemaining, 
                                                    ackDue, resendCounter, 
                                                    currentMessage, lastRx, 
                                                    unackedMessageCount, 
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
                                                    unackedMessageCount, 
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
                                               "Failure of assertion at line 24, column 5 of macro called at line 137, column 11.")
                                     /\ IF TRUE
                                           THEN /\ S' = [S EXCEPT ![txChan(self)].in = -lastRx'[self],
                                                                  ![rxChan(self)].out = 0]
                                           ELSE /\ S' = [S EXCEPT ![txChan(self)].in = -lastRx'[self]]
                                     /\ IF FALSE
                                           THEN /\ Timer' = [Timer EXCEPT ![txChan(self)] = 0,
                                                                          ![self] = 1]
                                           ELSE /\ Timer' = [Timer EXCEPT ![txChan(self)] = 0]
                                     /\ pc' = [pc EXCEPT ![self] = "TransmittingAckAwaitingAck"]
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
                                                                                "Failure of assertion at line 24, column 5 of macro called at line 153, column 15.")
                                                                      /\ IF FALSE
                                                                            THEN /\ S' = [S EXCEPT ![txChan(self)].in = -lastRx[self],
                                                                                                   ![rxChan(self)].out = 0]
                                                                            ELSE /\ S' = [S EXCEPT ![txChan(self)].in = -lastRx[self]]
                                                                      /\ IF FALSE
                                                                            THEN /\ Timer' = [Timer EXCEPT ![txChan(self)] = 0,
                                                                                                           ![self] = 1]
                                                                            ELSE /\ Timer' = [Timer EXCEPT ![txChan(self)] = 0]
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
                                                                                                      "Failure of assertion at line 167, column 15.")
                                                                                            /\ pc' = [pc EXCEPT ![self] = "TransmittingAckAwaitingAck"]
                                                                                            /\ UNCHANGED << S, 
                                                                                                            Note >>
                                                                                       ELSE /\ S' = [S EXCEPT ![rxChan(self)].out = 0]
                                                                                            /\ Note' = self\o" ignores ack from previous message"
                                                                                            /\ pc' = [pc EXCEPT ![self] = "TransmittingData"]
                                                                                 /\ UNCHANGED << Timer, 
                                                                                                 resendCounter >>
                                                                 ELSE /\ Assert((FALSE), 
                                                                                "Failure of assertion at line 174, column 11.")
                                                                      /\ pc' = [pc EXCEPT ![self] = "TransmittingAckAwaitingAck"]
                                                                      /\ UNCHANGED << S, 
                                                                                      Timer, 
                                                                                      Note, 
                                                                                      resendCounter >>
                                                           /\ UNCHANGED ackDue
                                                /\ UNCHANGED << lastRx, 
                                                                rxHistory >>
                          /\ UNCHANGED << droppedMessagesRemaining, 
                                          currentMessage, unackedMessageCount, 
                                          initialSendQueue, remainingSendQueue >>

TransmittingAckAwaitingAck(self) == /\ pc[self] = "TransmittingAckAwaitingAck"
                                    /\ (S[txChan(self)].in = 0 \/ receive(self) < 0)
                                    /\ IF (receive(self) < 0)
                                          THEN /\ IF (receive(self) = -currentMessage[self])
                                                     THEN /\ S' = [S EXCEPT ![rxChan(self)].out = 0]
                                                          /\ resendCounter' = [resendCounter EXCEPT ![self] = 0]
                                                          /\ Timer' = [Timer EXCEPT ![self] = -1]
                                                          /\ IF (S'[txChan(self)].in /= 0)
                                                                THEN /\ Note' = self\o" receives expected ack"
                                                                     /\ pc' = [pc EXCEPT ![self] = "TransmittingAckNotAwaiting"]
                                                                ELSE /\ Note' = self\o" receives expected ack and completes transmission."
                                                                     /\ pc' = [pc EXCEPT ![self] = "Idle"]
                                                     ELSE /\ S' = [S EXCEPT ![rxChan(self)].out = 0]
                                                          /\ IF (S'[txChan(self)].in /= 0)
                                                                THEN /\ Note' = self\o" ignores other-message ack"
                                                                     /\ pc' = [pc EXCEPT ![self] = "TransmittingAckAwaitingAck"]
                                                                ELSE /\ Note' = self\o" ignores other-message ack, and completes transmission."
                                                                     /\ pc' = [pc EXCEPT ![self] = "AwaitingAck"]
                                                          /\ UNCHANGED << Timer, 
                                                                          resendCounter >>
                                          ELSE /\ IF (S[txChan(self)].in = 0)
                                                     THEN /\ Note' = self\o" completes transmission of ack"
                                                          /\ pc' = [pc EXCEPT ![self] = "AwaitingAck"]
                                                     ELSE /\ Assert((FALSE), 
                                                                    "Failure of assertion at line 207, column 11.")
                                                          /\ pc' = [pc EXCEPT ![self] = "AwaitingAck"]
                                                          /\ Note' = Note
                                               /\ UNCHANGED << S, Timer, 
                                                               resendCounter >>
                                    /\ UNCHANGED << droppedMessagesRemaining, 
                                                    ackDue, currentMessage, 
                                                    lastRx, 
                                                    unackedMessageCount, 
                                                    initialSendQueue, 
                                                    remainingSendQueue, 
                                                    rxHistory >>

AwaitingAck(self) == /\ pc[self] = "AwaitingAck"
                     /\ Assert(S[txChan(self)].in = 0, 
                               "Failure of assertion at line 211, column 7.")
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
                                /\ UNCHANGED << lastRx, unackedMessageCount, 
                                                rxHistory >>
                           ELSE /\ IF (Timer[self] = 0)
                                      THEN /\ IF (resendCounter[self] < 3)
                                                 THEN /\ Assert(S[txChan(self)].in = 0, 
                                                                "Failure of assertion at line 24, column 5 of macro called at line 227, column 15.")
                                                      /\ IF FALSE
                                                            THEN /\ S' = [S EXCEPT ![txChan(self)].in = currentMessage[self],
                                                                                   ![rxChan(self)].out = 0]
                                                            ELSE /\ S' = [S EXCEPT ![txChan(self)].in = currentMessage[self]]
                                                      /\ IF TRUE
                                                            THEN /\ Timer' = [Timer EXCEPT ![txChan(self)] = 0,
                                                                                           ![self] = 1]
                                                            ELSE /\ Timer' = [Timer EXCEPT ![txChan(self)] = 0]
                                                      /\ resendCounter' = [resendCounter EXCEPT ![self] = resendCounter[self]+1]
                                                      /\ Note' = self\o" resends message after timeout"
                                                      /\ pc' = [pc EXCEPT ![self] = "TransmittingData"]
                                                      /\ UNCHANGED unackedMessageCount
                                                 ELSE /\ unackedMessageCount' = [unackedMessageCount EXCEPT ![self] = unackedMessageCount[self]+1]
                                                      /\ Note' = self\o" dropped message after several retries."
                                                      /\ resendCounter' = [resendCounter EXCEPT ![self] = 0]
                                                      /\ Timer' = [Timer EXCEPT ![self] = -1]
                                                      /\ pc' = [pc EXCEPT ![self] = "Idle"]
                                                      /\ S' = S
                                           /\ UNCHANGED << lastRx, rxHistory >>
                                      ELSE /\ IF (receive(self) > 0)
                                                 THEN /\ IF (lastRx[self] /= receive(self))
                                                            THEN /\ rxHistory' = [rxHistory EXCEPT ![self] = Append(rxHistory[self], receive(self))]
                                                                 /\ lastRx' = [lastRx EXCEPT ![self] = receive(self)]
                                                                 /\ Note' = self\o" receives message, starts sending ack"
                                                            ELSE /\ Note' = self\o" receives duplicate message, starts sending ack"
                                                                 /\ UNCHANGED << lastRx, 
                                                                                 rxHistory >>
                                                      /\ Assert(S[txChan(self)].in = 0, 
                                                                "Failure of assertion at line 24, column 5 of macro called at line 246, column 11.")
                                                      /\ IF TRUE
                                                            THEN /\ S' = [S EXCEPT ![txChan(self)].in = -lastRx'[self],
                                                                                   ![rxChan(self)].out = 0]
                                                            ELSE /\ S' = [S EXCEPT ![txChan(self)].in = -lastRx'[self]]
                                                      /\ IF FALSE
                                                            THEN /\ Timer' = [Timer EXCEPT ![txChan(self)] = 0,
                                                                                           ![self] = 1]
                                                            ELSE /\ Timer' = [Timer EXCEPT ![txChan(self)] = 0]
                                                      /\ pc' = [pc EXCEPT ![self] = "TransmittingAckAwaitingAck"]
                                                 ELSE /\ Assert((FALSE), 
                                                                "Failure of assertion at line 249, column 11.")
                                                      /\ pc' = [pc EXCEPT ![self] = "Done"]
                                                      /\ UNCHANGED << S, Timer, 
                                                                      Note, 
                                                                      lastRx, 
                                                                      rxHistory >>
                                           /\ UNCHANGED << resendCounter, 
                                                           unackedMessageCount >>
                     /\ UNCHANGED << droppedMessagesRemaining, ackDue, 
                                     currentMessage, initialSendQueue, 
                                     remainingSendQueue >>

AckedChannel(self) == InitChannel(self) \/ Idle(self)
                         \/ TransmittingAckNotAwaiting(self)
                         \/ FinishingUnnecessaryResend(self)
                         \/ TransmittingData(self)
                         \/ TransmittingAckAwaitingAck(self)
                         \/ AwaitingAck(self)

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

NeverDropMoreThanSentInvariant == unackedMessageCount["ProcY"] <= Len(initialSendQueue["ProcY"])
                     /\ unackedMessageCount["ProcX"] <= Len(initialSendQueue["ProcX"])

MessageDropsPerTransportDropInvariant == ((3*unackedMessageCount["ProcX"] + 3*unackedMessageCount["ProcY"]) <= droppedMessageLimit)

ProgramFinished == pc["ProcX"]="Idle" /\ pc["ProcY"]="Idle"
                   /\ Len(remainingSendQueue["ProcX"]) = 0 /\ Len(remainingSendQueue["ProcY"]) = 0
                   /\ Len(rxHistory["ProcX"]) >= Len(initialSendQueue["ProcY"])-unackedMessageCount["ProcY"]
                   /\ Len(rxHistory["ProcY"]) >= Len(initialSendQueue["ProcX"])-unackedMessageCount["ProcX"]
\*ProgramFinished == pc["SendPing"]="Done"

=============================================================================
\* Modification History
\* Last modified Wed Feb 12 21:42:39 GMT 2020 by mtandy
\* Created Tue Jan 28 23:30:18 GMT 2020 by mtandy

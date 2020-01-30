------------------------------- MODULE test1 -------------------------------

EXTENDS Naturals, TLC, Integers, Sequences, FiniteSets

(* --algorithm transfer

variables channelA_in = 0, channelA_out = 0,
channelB_in = 0, channelB_out = 0;

process ChannelA = "ChanA"
begin LoopChA:
  while TRUE do
   A: assert channelA_out = 0;
      await channelA_in /= 0;
        either
          \* Message successfully delivered 
          channelA_out := channelA_in;
          channelA_in := 0;
        or
          \* Message lost in transit
          channelA_in := 0;
        end either;
   B: await channelA_out = 0;
  end while;
end process;

process ChannelB = "ChanB"
begin LoopChB:
  while TRUE do
   A: assert channelB_out = 0;
      await channelB_in /= 0;
          channelB_out := channelB_in;
          channelB_in := 0;
   B: await channelB_out = 0;
  end while;
end process;

process SendPing = "SendPing"
begin
  Send: channelA_in := 123;
  Wait: await (channelB_out /= 0);
        assert channelB_out = 321;
end process

process PingToPong = "PingToPong"
begin
  AwaitPing: await (channelA_out /= 0);
             assert channelA_out = 123;
  SendPong: channelB_in := 321;
end process

end algorithm *)

\* BEGIN TRANSLATION
\* Label A of process ChannelA at line 13 col 7 changed to A_
\* Label B of process ChannelA at line 23 col 7 changed to B_
VARIABLES channelA_in, channelA_out, channelB_in, channelB_out, pc

vars == << channelA_in, channelA_out, channelB_in, channelB_out, pc >>

ProcSet == {"ChanA"} \cup {"ChanB"} \cup {"SendPing"} \cup {"PingToPong"}

Init == (* Global variables *)
        /\ channelA_in = 0
        /\ channelA_out = 0
        /\ channelB_in = 0
        /\ channelB_out = 0
        /\ pc = [self \in ProcSet |-> CASE self = "ChanA" -> "LoopChA"
                                        [] self = "ChanB" -> "LoopChB"
                                        [] self = "SendPing" -> "Send"
                                        [] self = "PingToPong" -> "AwaitPing"]

LoopChA == /\ pc["ChanA"] = "LoopChA"
           /\ pc' = [pc EXCEPT !["ChanA"] = "A_"]
           /\ UNCHANGED << channelA_in, channelA_out, channelB_in, 
                           channelB_out >>

A_ == /\ pc["ChanA"] = "A_"
      /\ Assert(channelA_out = 0, 
                "Failure of assertion at line 13, column 7.")
      /\ channelA_in /= 0
      /\ \/ /\ channelA_out' = channelA_in
            /\ channelA_in' = 0
         \/ /\ channelA_in' = 0
            /\ UNCHANGED channelA_out
      /\ pc' = [pc EXCEPT !["ChanA"] = "B_"]
      /\ UNCHANGED << channelB_in, channelB_out >>

B_ == /\ pc["ChanA"] = "B_"
      /\ channelA_out = 0
      /\ pc' = [pc EXCEPT !["ChanA"] = "LoopChA"]
      /\ UNCHANGED << channelA_in, channelA_out, channelB_in, channelB_out >>

ChannelA == LoopChA \/ A_ \/ B_

LoopChB == /\ pc["ChanB"] = "LoopChB"
           /\ pc' = [pc EXCEPT !["ChanB"] = "A"]
           /\ UNCHANGED << channelA_in, channelA_out, channelB_in, 
                           channelB_out >>

A == /\ pc["ChanB"] = "A"
     /\ Assert(channelB_out = 0, 
               "Failure of assertion at line 30, column 7.")
     /\ channelB_in /= 0
     /\ channelB_out' = channelB_in
     /\ channelB_in' = 0
     /\ pc' = [pc EXCEPT !["ChanB"] = "B"]
     /\ UNCHANGED << channelA_in, channelA_out >>

B == /\ pc["ChanB"] = "B"
     /\ channelB_out = 0
     /\ pc' = [pc EXCEPT !["ChanB"] = "LoopChB"]
     /\ UNCHANGED << channelA_in, channelA_out, channelB_in, channelB_out >>

ChannelB == LoopChB \/ A \/ B

Send == /\ pc["SendPing"] = "Send"
        /\ channelA_in' = 123
        /\ pc' = [pc EXCEPT !["SendPing"] = "Wait"]
        /\ UNCHANGED << channelA_out, channelB_in, channelB_out >>

Wait == /\ pc["SendPing"] = "Wait"
        /\ (channelB_out /= 0)
        /\ Assert(channelB_out = 321, 
                  "Failure of assertion at line 42, column 9.")
        /\ pc' = [pc EXCEPT !["SendPing"] = "Done"]
        /\ UNCHANGED << channelA_in, channelA_out, channelB_in, channelB_out >>

SendPing == Send \/ Wait

AwaitPing == /\ pc["PingToPong"] = "AwaitPing"
             /\ (channelA_out /= 0)
             /\ Assert(channelA_out = 123, 
                       "Failure of assertion at line 48, column 14.")
             /\ pc' = [pc EXCEPT !["PingToPong"] = "SendPong"]
             /\ UNCHANGED << channelA_in, channelA_out, channelB_in, 
                             channelB_out >>

SendPong == /\ pc["PingToPong"] = "SendPong"
            /\ channelB_in' = 321
            /\ pc' = [pc EXCEPT !["PingToPong"] = "Done"]
            /\ UNCHANGED << channelA_in, channelA_out, channelB_out >>

PingToPong == AwaitPing \/ SendPong

Next == ChannelA \/ ChannelB \/ SendPing \/ PingToPong

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

ChannelInvariant == (channelA_in = 0 \/ channelA_out = 0) /\ (channelB_in = 0 \/ channelB_out = 0)

=============================================================================
\* Modification History
\* Last modified Thu Jan 30 21:07:13 GMT 2020 by mtandy
\* Created Tue Jan 28 23:30:18 GMT 2020 by mtandy

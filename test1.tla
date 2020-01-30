------------------------------- MODULE test1 -------------------------------

EXTENDS Naturals, TLC, Integers, Sequences, FiniteSets

(* --algorithm transfer

variables channelA_in = 0, channelA_out = 0,
channelB_in = 0, channelB_out = 0;

process ChannelA = 0
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

process ChannelB = 0
begin LoopChB:
  while TRUE do
   A: assert channelB_out = 0;
      await channelB_in /= 0;
          channelB_out := channelB_in;
          channelB_in := 0;
   B: await channelB_out = 0;
  end while;
end process;

process SendPing = 1
begin
  Send: channelA_in := 123;
  Wait: await (channelB_out /= 0);
        assert channelB_out = 321;
end process

process PingToPong = 2
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

ProcSet == {0} \cup {0} \cup {1} \cup {2}

Init == (* Global variables *)
        /\ channelA_in = 0
        /\ channelA_out = 0
        /\ channelB_in = 0
        /\ channelB_out = 0
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "LoopChA"
                                        [] self = 0 -> "LoopChB"
                                        [] self = 1 -> "Send"
                                        [] self = 2 -> "AwaitPing"]

LoopChA == /\ pc[0] = "LoopChA"
           /\ pc' = [pc EXCEPT ![0] = "A_"]
           /\ UNCHANGED << channelA_in, channelA_out, channelB_in, 
                           channelB_out >>

A_ == /\ pc[0] = "A_"
      /\ Assert(channelA_out = 0, 
                "Failure of assertion at line 13, column 7.")
      /\ channelA_in /= 0
      /\ \/ /\ channelA_out' = channelA_in
            /\ channelA_in' = 0
         \/ /\ channelA_in' = 0
            /\ UNCHANGED channelA_out
      /\ pc' = [pc EXCEPT ![0] = "B_"]
      /\ UNCHANGED << channelB_in, channelB_out >>

B_ == /\ pc[0] = "B_"
      /\ channelA_out = 0
      /\ pc' = [pc EXCEPT ![0] = "LoopChA"]
      /\ UNCHANGED << channelA_in, channelA_out, channelB_in, channelB_out >>

ChannelA == LoopChA \/ A_ \/ B_

LoopChB == /\ pc[0] = "LoopChB"
           /\ pc' = [pc EXCEPT ![0] = "A"]
           /\ UNCHANGED << channelA_in, channelA_out, channelB_in, 
                           channelB_out >>

A == /\ pc[0] = "A"
     /\ Assert(channelB_out = 0, 
               "Failure of assertion at line 30, column 7.")
     /\ channelB_in /= 0
     /\ channelB_out' = channelB_in
     /\ channelB_in' = 0
     /\ pc' = [pc EXCEPT ![0] = "B"]
     /\ UNCHANGED << channelA_in, channelA_out >>

B == /\ pc[0] = "B"
     /\ channelB_out = 0
     /\ pc' = [pc EXCEPT ![0] = "LoopChB"]
     /\ UNCHANGED << channelA_in, channelA_out, channelB_in, channelB_out >>

ChannelB == LoopChB \/ A \/ B

Send == /\ pc[1] = "Send"
        /\ channelA_in' = 123
        /\ pc' = [pc EXCEPT ![1] = "Wait"]
        /\ UNCHANGED << channelA_out, channelB_in, channelB_out >>

Wait == /\ pc[1] = "Wait"
        /\ (channelB_out /= 0)
        /\ Assert(channelB_out = 321, 
                  "Failure of assertion at line 42, column 9.")
        /\ pc' = [pc EXCEPT ![1] = "Done"]
        /\ UNCHANGED << channelA_in, channelA_out, channelB_in, channelB_out >>

SendPing == Send \/ Wait

AwaitPing == /\ pc[2] = "AwaitPing"
             /\ (channelA_out /= 0)
             /\ Assert(channelA_out = 123, 
                       "Failure of assertion at line 48, column 14.")
             /\ pc' = [pc EXCEPT ![2] = "SendPong"]
             /\ UNCHANGED << channelA_in, channelA_out, channelB_in, 
                             channelB_out >>

SendPong == /\ pc[2] = "SendPong"
            /\ channelB_in' = 321
            /\ pc' = [pc EXCEPT ![2] = "Done"]
            /\ UNCHANGED << channelA_in, channelA_out, channelB_out >>

PingToPong == AwaitPing \/ SendPong

Next == ChannelA \/ ChannelB \/ SendPing \/ PingToPong

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

ChannelInvariant == (channelA_in = 0 \/ channelA_out = 0) /\ (channelB_in = 0 \/ channelB_out = 0)

=============================================================================
\* Modification History
\* Last modified Thu Jan 30 20:34:47 GMT 2020 by mtandy
\* Created Tue Jan 28 23:30:18 GMT 2020 by mtandy

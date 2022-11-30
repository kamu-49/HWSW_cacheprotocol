-------------------------------- MODULE MSI --------------------------------
EXTENDS TLC, Integers

CONSTANT CoreNum, MaxWrite

Cores == 1..CoreNum
memory == "Memory"
Storage == Cores \union {memory}
State == {"M", "S", "I"}
Data == 0..MaxWrite

VARIABLES state, data, currentValue, i, pc

vars == << state, data, currentValue, i, pc >>

ProcSet == {"bus"}

  PrRd(core) == /\ CASE state[core] = "I" ->
                           /\ data' = [data EXCEPT ![core] = data[memory]]
                           /\ state' = [state EXCEPT ![core] = "S"]
                     [] OTHER ->
                           /\ TRUE
                           /\ UNCHANGED << state, data >>
                /\ Assert(data'[core] = currentValue, 
                                "Failure of assertion at line 30, column 3 of macro called at line 96, column 7.")
                                
  PrWr(core) == /\ currentValue' = currentValue + 1
                /\ data' = [data EXCEPT ![core] = currentValue']
                /\ state' = [state EXCEPT ![core] = "M"]
                
  BusRd(core) == /\ CASE state[core] = "M" ->
                            /\ data' = [data EXCEPT ![memory] = data[core]]
                            /\ state' = [state EXCEPT ![core] = "S"]
                      [] OTHER ->
                            /\ TRUE
                            /\ UNCHANGED << state, data >>
                            
  BusRdX(core) == /\ CASE state[core] = "S" ->
                             /\ state' = [state EXCEPT ![core] = "I"]
                             /\ data' = data
                       [] state[core] = "M" ->
                             /\ data' = [data EXCEPT ![memory] = data[core]]
                             /\ state' = [state EXCEPT ![core] = "I"]
                       [] OTHER ->
                             /\ TRUE
                             /\ UNCHANGED << state, data >>
   
  BusUpgr(core) == /\ CASE state[core] = "S" ->
                              /\ state' = [state EXCEPT ![core] = "I"]
                        [] state'[core] = "M" ->
                              /\ Assert(FALSE, 
                                             "Failure of assertion at line 89, column 5 of macro called at line 127, column 7.")
                        [] OTHER ->
                              /\ TRUE
                              /\ UNCHANGED << state, data >>
                              
  BusRdFrom(core) == /\ PrRd(core)
                     /\ \A otherCore \in Cores \ {core}: BusRd(otherCore)
                     
  BusRdXFrom(core) == /\ PrWr(core)
                      /\ \A otherCore \in Cores \ {core}: BusRdX(otherCore)
                     
  BusUpgrFrom(core) == /\ PrWr(core)
                       /\ \A otherCore \in Cores \ {core}: BusUpgr(otherCore)
                       

Init == (* Global variables *)
        /\ state = [c \in Cores |-> "I"]
        /\ data = [c \in Storage |-> 0]
        /\ currentValue = 0
        /\ i = 0
        /\ pc = [self \in ProcSet |-> "BusRequest"]
                       
bus == /\ pc["bus"] = "BusRequest"
       /\ \E core \in Cores:
            \/ /\ state[core] = "I"
               /\ BusRdFrom(core)
            \/ /\ state[core] = "I"
               /\ BusRdXFrom(core)
            \/ /\ state[core] = "S"
               /\ BusUpgrFrom(core)
       /\ IF currentValue < MaxWrite
             THEN /\ pc' = [pc EXCEPT !["bus"] = "BusRequest"]
             ELSE /\ pc' = [pc EXCEPT !["bus"] = "Done"]
       /\ UNCHANGED << data, currentValue >>
       

TYPE_OK == /\ \A c \in Cores : state[c] \in State
           /\ \A c \in Storage : data[c] \in Data

                     
(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars
                     
Next == bus
           \/ Terminating

Spec == Init /\ [][Next]_vars
             /\ TYPE_OK

Termination == <>(\A self \in ProcSet: pc[self] = "Done")
                       
                       

=============================================================================
\* Modification History
\* Last modified Tue Nov 29 21:37:34 EST 2022 by hq990
\* Created Wed Nov 23 20:34:22 EST 2022 by hq990

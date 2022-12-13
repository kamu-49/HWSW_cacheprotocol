------------------------------ MODULE MSI_ARAT ------------------------------
EXTENDS MSI

CState == {"I", "IS^D", "IM^D", "S", "SM^D", "M"}
MState == {"IorS", "IorS^D", "M"}

Message == [type: {"GetS", "GetM", "PutM"},
            sender: Cores,
            receivers: SUBSET Storage]
           \union
           [type: {"Data"},
            data: Data,
            sender: Storage,
            receivers: SUBSET Storage]


coreBusEvent(core) ==
    /\ updateBusReceivers(core)
    /\ \/ /\
               \/ trans(core, "I", "GetS", FALSE, "I")
               \/ trans(core, "I", "GetM", FALSE, "I")
               \/ trans(core, "I", "PutM", FALSE, "I")
               \/ trans(core, "IS^D", "GetS", TRUE, "IS^D")
               \/ trans(core, "S", "GetS", FALSE, "S")
               \/ trans(core, "S", "GetM", FALSE, "I")
               \/ trans(core, "SM^D", "GetM", TRUE, "SM^D")
               \/ trans(core, "IM^D", "GetM", TRUE, "IM^D")
          /\ UNCHANGED << data, queue >>
       \/ /\ 
               \/ /\ trans(core, "IS^D", "Data", TRUE, "S")
                  /\ updateData(core, bus.data)
               \/ /\ trans(core, "IM^D", "Data", TRUE, "M")
                  /\ updateData(core, bus.data)
               \/ /\ trans(core, "SM^D", "Data", TRUE, "M")
                  /\ updateData(core, bus.data)
          /\ UNCHANGED << queue >>
       \/ /\
               \/ /\ trans(core, "M", "GetS", FALSE, "S")
                  /\ sendData(core, {memory, bus.sender})
               \/ /\ trans(core, "M", "GetM", FALSE, "I")
                  /\ sendData(core, {bus.sender})
          /\ UNCHANGED << data >>

memoryBusEvent ==
    /\ updateBusReceivers(memory)
    /\ \/ /\ 
             \/ /\ memoryTrans("IorS", "GetS", "IorS")
                /\ sendData(memory, {bus.sender})
             \/ /\ memoryTrans("IorS", "GetM", "M")
                /\ sendData(memory, {bus.sender})
          /\ UNCHANGED << data >>
       \/ /\ 
             \/ memoryTrans("M", "GetS", "IorS^D")
             \/ memoryTrans("M", "GetM", "M")
             \/ memoryTrans("M", "PutM", "IorS^D")
          /\ UNCHANGED << data, queue >>
       \/ /\ 
             \/ /\ memoryTrans("IorS^D", "Data", "IorS")
                /\ updateData(memory, bus.data)
          /\ UNCHANGED << queue >>
    
getS(core) ==
    /\ sendMsg("GetS", core)
    /\ state[core] = "I"
    /\ updateState(core, "IS^D")
    /\ UNCHANGED << data, bus >>
getM(core) ==
    /\ sendMsg("GetM", core)
    /\ \/ /\ state[core] = "I"
          /\ updateState(core, "IM^D")
       \/ /\ state[core] = "S"
          /\ updateState(core, "SM^D")
    /\ UNCHANGED << data, bus >>
putM(core) ==
    /\ state[core] = "M"
    /\ sendMsg("PutM", core)
    /\ sendData(core, {memory})
    /\ updateState(core, "I")
    /\ UNCHANGED << data, bus >>
coreAction(core) ==
    \/ coreBusEvent(core)
    \/ getS(core)
    \/ getM(core)
    \/ putM(core)
    \/ /\ write(core)
       /\ UNCHANGED << state, bus, queue >>

---------------------------------------------------------

memoryAction == memoryBusEvent

Next == 
    IF nextMessage
    THEN 
        /\ updateBus
        /\ UNCHANGED << state, data >>
    ELSE
        \/ \E core \in Cores: coreAction(core)
        \/ memoryAction

typeInvariant == 
    /\ \A c \in Cores : state[c] \in CState
    /\ state[memory] \in MState
    /\ \A c \in Storage : data[c] \in Data
    /\ bus \in Message
    /\ \A msg \in queue : msg \in Message


Spec == Init /\ [][Next /\ atomicRequest]_vars

Invariants == /\ typeInvariant
              /\ cacheCoherence

=============================================================================
\* Modification History
\* Last modified Mon Dec 12 16:20:00 EST 2022 by hq990
\* Created Sun Dec 11 17:15:41 EST 2022 by hq990

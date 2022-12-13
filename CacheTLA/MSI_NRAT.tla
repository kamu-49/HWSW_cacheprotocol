------------------------------ MODULE MSI_NRAT ------------------------------
EXTENDS MSI

CState == {"I", "IS^AD", "IS^D", "IM^AD", "IM^D", "S", "SM^AD", "SM^D", "M", "MI^A", "II^A"}
MState == {"IorS", "IorS^D", "M", "M^D"}

Message == [type: {"GetS", "GetM", "PutM"},
            sender: Cores,
            receivers: SUBSET Storage]
           \union
           [type: {"Data"},
            data: Data,
            sender: Storage,
            receivers: SUBSET Storage]
           \union
           [type: {"NoData"},
            receivers: {memory}]


coreBusEvent(core) ==
    /\ updateBusReceivers(core)
    /\ \/ /\
               \/ trans(core, "I", "GetS", FALSE, "I")
               \/ trans(core, "I", "GetM", FALSE, "I")
               \/ trans(core, "I", "PutM", FALSE, "I")
               
               \/ trans(core, "IS^AD", "GetS", TRUE, "IS^D")
               \/ trans(core, "IS^AD", "GetS", FALSE, "IS^AD")
               \/ trans(core, "IS^AD", "GetM", FALSE, "IS^AD")
               \/ trans(core, "IS^AD", "PutM", FALSE, "IS^AD")
               
               \/ trans(core, "IM^AD", "GetM", TRUE, "IM^D")
               \/ trans(core, "IM^AD", "GetS", FALSE, "IM^AD")
               \/ trans(core, "IM^AD", "GetM", FALSE, "IM^AD")
               \/ trans(core, "IM^AD", "PutM", FALSE, "IM^AD")
               
               \/ trans(core, "S", "GetS", FALSE, "S")
               \/ trans(core, "S", "GetM", FALSE, "I")
               \/ trans(core, "S", "PutM", FALSE, "S")
               
               \/ trans(core, "SM^AD", "GetM", TRUE, "SM^D")
               \/ trans(core, "SM^AD", "GetS", FALSE, "SM^AD")
               \/ trans(core, "SM^AD", "GetM", FALSE, "IM^AD")
               \/ trans(core, "SM^AD", "PutM", FALSE, "SM^AD")
               
               \/ trans(core, "M", "PutM", FALSE, "M")
               
               \/ trans(core, "II^A", "GetS", FALSE, "II^A")
               \/ trans(core, "II^A", "GetM", FALSE, "II^A")
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
               \/ /\ trans(core, "MI^A", "PutM", TRUE, "I")
                  /\ sendData(core, {memory})
               \/ /\ trans(core, "MI^A", "GetS", FALSE, "II^A")
                  /\ sendData(core, {memory, bus.sender})
               \/ /\ trans(core, "MI^A", "GetM", FALSE, "II^A")
                  /\ sendData(core, {bus.sender})
               \/ /\ trans(core, "II^A", "PutM", TRUE, "I")
                  /\ sendNoData
          /\ UNCHANGED << data >>

memoryBusEvent ==
    /\ updateBusReceivers(memory)
    /\ 
       \/ /\ 
             \/ memoryTrans("IorS", "PutM", "IorS^D")
             \/ memoryTrans("IorS^D", "NoData", "IorS")
             \/ memoryTrans("M", "GetS", "IorS^D")
             \/ memoryTrans("M", "GetM", "M")
             \/ memoryTrans("M", "PutM", "M^D")
             \/ memoryTrans("M^D", "NoData", "M")
          /\ UNCHANGED << data, queue >>
       \/ /\ 
             \/ /\ memoryTrans("IorS^D", "Data", "IorS")
                /\ updateData(memory, bus.data)
             \/ /\ memoryTrans("M^D", "Data", "IorS")
                /\ updateData(memory, bus.data)
          /\ UNCHANGED << queue >>
       \/ /\ 
             \/ /\ memoryTrans("IorS", "GetS", "IorS")
                /\ sendData(memory, {bus.sender})
             \/ /\ memoryTrans("IorS", "GetM", "M")
                /\ sendData(memory, {bus.sender})
          /\ UNCHANGED << data >>
    
getS(core) ==
    /\ sendMsg("GetS", core)
    /\ state[core] = "I"
    /\ updateState(core, "IS^AD")
    /\ UNCHANGED << data, bus >>
getM(core) ==
    /\ sendMsg("GetM", core)
    /\ \/ /\ state[core] = "I"
          /\ updateState(core, "IM^AD")
       \/ /\ state[core] = "S"
          /\ updateState(core, "SM^AD")
    /\ UNCHANGED << data, bus >>
putM(core) ==
    /\ state[core] = "M"
    /\ sendMsg("PutM", core)
    /\ sendData(core, {memory})
    /\ updateState(core, "MI^A")
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


Spec == Init /\ [][Next /\ atomicTransaction]_vars

Invariants == /\ typeInvariant
              /\ cacheCoherence


=============================================================================
\* Modification History
\* Last modified Mon Dec 12 16:19:26 EST 2022 by hq990
\* Created Sun Dec 11 17:37:04 EST 2022 by hq990

-------------------------------- MODULE MSI --------------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT CoreNum, MaxWrite

Cores == 1..CoreNum
memory == 0
Storage == Cores \union {memory}

CState == {"I", "IS^D", "IM^D", "S", "SM^D", "M"}
MState == {"IorS", "IorS^D", "M"}
Data == 0..MaxWrite
Message == [type: {"GetS", "GetM", "PutM"},
            sender: Cores,
            receivers: SUBSET Storage]
           \union
           [type: {"Data"},
            data: Data,
            sender: Storage,
            receivers: SUBSET Storage]

VARIABLES state, data, bus, queue

vars == << state, data, bus, queue >>

Init == (* Global variables *)
        /\ state = [c \in Storage |-> IF c \in Cores THEN "I" ELSE "IorS"]
        /\ data = [c \in Storage |-> 0]
        /\ bus = [type |-> "Data", data |-> 0, sender |-> memory, receivers |-> {}]
        /\ queue = {}

-----------------

nextMessage ==
    /\ bus.receivers = {}
    /\ queue # {}
    
updateBus ==
    /\ \E message \in queue:
        /\ bus' = message
        /\ queue' = queue \ {message}
    /\ UNCHANGED << state, data >>
    
updateData(entity, newData) ==
    data' = [data EXCEPT![entity] = newData]

updateState(entity, newState) ==
    state' = [state EXCEPT![entity] = newState]
    
send(msg) == queue' = queue \union {msg}

sendData(from, to) ==
    send([type |-> "Data",
          data |-> data[from],
          sender |-> from,
          receivers |-> to])

sendMsg(msg, from) ==
    send([type |-> msg,
          sender |-> from,
          receivers |-> Storage])

trans(entity, prevState, message, isOwn, nextState) ==
    /\ state[entity] = prevState
    /\ bus.type = message
    /\ \/ (bus.sender = entity) = isOwn
       \/ message = "Data"
    /\ updateState(entity, nextState)
    
memoryTrans(prevState, message, nextState) ==
    trans(memory, prevState, message, FALSE, nextState)
    
updateBusReceivers(entity) ==
    /\ entity \in bus.receivers
    /\ bus' = [bus EXCEPT!.receivers = bus.receivers \ {entity}]

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
write(core) ==
    /\ state[core] = "M"
    /\ data[core] < MaxWrite
    /\ updateData(core, data[core] + 1)
    /\ UNCHANGED << state, bus, queue >>

coreAction(core) ==
    IF bus.receivers # {}
    THEN coreBusEvent(core)
    ELSE \/ getS(core)
         \/ getM(core)
         \/ putM(core)
         \/ write(core)
         
memoryAction == memoryBusEvent

Next == 
    IF nextMessage
    THEN updateBus
    ELSE
        \/ \E core \in Cores: coreAction(core)
        \/ memoryAction

------------------

typeInvariant == 
    /\ \A c \in Cores : state[c] \in CState
    /\ state[memory] \in MState
    /\ \A c \in Storage : data[c] \in Data
    /\ bus \in Message
    /\ \A msg \in queue : msg \in Message
    
cacheCoherence ==
    /\ \A c \in Cores :
        state[c] \in {"S", "M"} => data[c] >= data[memory]
    /\ \A c1, c2 \in Cores :
        state[c1] \in {"S", "M"} => data[c1] >= data[c2]

Spec == Init /\ [][Next]_vars
             
Invariants == /\ typeInvariant
              /\ cacheCoherence

THEOREM Spec => Invariants

=============================================================================
\* Modification History
\* Last modified Thu Dec 01 20:36:13 EST 2022 by hq990
\* Created Wed Nov 23 20:34:22 EST 2022 by hq990
